#!/usr/bin/env python3
"""Build project modules serially, optionally limited to selected roots.

With --target, build only those modules and their transitive project
dependencies, then check the selected Lake targets. Without --target,
build every project module and check Lake's default targets as before.

Requires Python 3.11+. Fetch the pinned dependency cache before running this
script: project modules are serialized, but Lake manages external dependencies.
No Lean source, build trace, or cache metadata is rewritten by this script.
"""

import argparse
import graphlib
from pathlib import Path
import re
import subprocess
import sys

if sys.version_info < (3, 11):
    raise SystemExit("build_serial requires Python 3.11 or newer")

import tomllib


NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def header_imports(source: str) -> set[str]:
    """Read Lean's import header, skipping line and nested block comments."""
    pos = 0

    def token() -> str:
        nonlocal pos
        while pos < len(source):
            if source[pos].isspace() or source[pos] == "\ufeff":
                pos += 1
            elif source.startswith("--", pos):
                end = source.find("\n", pos)
                pos = len(source) if end < 0 else end + 1
            elif source.startswith("/-", pos):
                pos += 2
                depth = 1
                while depth and pos < len(source):
                    if source.startswith("/-", pos):
                        depth += 1
                        pos += 2
                    elif source.startswith("-/", pos):
                        depth -= 1
                        pos += 2
                    else:
                        pos += 1
                if depth:
                    raise ValueError("unterminated block comment in import header")
            else:
                match = NAME.match(source, pos)
                if match:
                    pos = match.end()
                    if pos < len(source) and not (
                        source[pos].isspace() or source.startswith(("--", "/-"), pos)
                    ):
                        raise ValueError("unsupported token in import header")
                    return match.group()
                value = source[pos]
                pos += 1
                return value
        return ""

    imports = set()
    word = token()
    while word in {"module", "prelude"}:
        word = token()
    while word:
        if word == "public":
            word = token()
        if word == "meta":
            word = token()
        if word != "import":
            break
        name = token()
        if name == "all":
            name = token()
        if not NAME.fullmatch(name):
            raise ValueError(f"unsupported or missing imported module name: {name!r}")
        imports.add(name)
        word = token()
    return imports


def discover_modules(root: Path) -> dict[str, Path]:
    config = tomllib.loads((root / "lakefile.toml").read_text(encoding="utf-8"))
    libraries = config.get("lean_lib", [])
    names = [lib["name"] for lib in libraries]
    if not names or len(names) != len(set(names)):
        raise ValueError("lean_lib names must be nonempty and unique")
    modules = {}
    for lib in libraries:
        name = lib["name"]
        if not NAME.fullmatch(name) or "roots" in lib or "globs" in lib:
            raise ValueError(f"unsupported library roots/globs or name: {name!r}")
        src = (root / lib.get("srcDir", ".")).resolve()
        if not src.is_relative_to(root):
            raise ValueError(f"library source directory is outside the repository: {name}")
        base = src.joinpath(*name.split("."))
        files = list(base.rglob("*.lean")) if base.is_dir() else []
        if base.with_suffix(".lean").is_file():
            files.append(base.with_suffix(".lean"))
        if not files:
            raise ValueError(f"no Lean sources found for library {name}")
        for path in sorted(files):
            module = ".".join(path.relative_to(src).with_suffix("").parts)
            if not NAME.fullmatch(module) or not path.resolve().is_relative_to(root):
                raise ValueError(f"unsupported module name or external source: {module}")
            if module in modules:
                raise ValueError(f"duplicate module name: {module}")
            modules[module] = path
    for module, path in modules.items():
        for dependency in header_imports(path.read_text(encoding="utf-8")):
            if dependency not in modules and any(
                dependency == name or dependency.startswith(name + ".") for name in names
            ):
                raise ValueError(f"{module} imports missing project module {dependency}")
    return modules


def dependency_order(dependencies: dict[str, set[str]]) -> list[str]:
    sorter = graphlib.TopologicalSorter(dependencies)
    sorter.prepare()  # Reject cycles before starting any build.
    order = []
    while sorter.is_active():
        ready = sorted(sorter.get_ready())
        order.extend(ready)
        sorter.done(*ready)
    return order


def dependency_closure(dependencies: dict[str, set[str]], targets: list[str]) -> dict[str, set[str]]:
    """Keep exactly the selected roots and their transitive dependencies."""
    for target in targets:
        if target not in dependencies:
            raise ValueError(f"unknown project module target: {target!r}")
    selected = set()
    pending = list(targets)
    while pending:
        name = pending.pop()
        if name in selected:
            continue
        selected.add(name)
        pending.extend(dependencies[name] - selected)
    return {name: dependencies[name] for name in sorted(selected)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dry-run", action="store_true", help="print module order; do not run Lake")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1],
                        help="repository root (defaults to this script's parent repository)")
    parser.add_argument("--target", action="append", default=[], metavar="MODULE",
                        help="build this module root and its dependencies (repeatable)")
    args = parser.parse_args()
    root = args.root.resolve()
    targets = list(dict.fromkeys(args.target))
    try:
        modules = discover_modules(root)
        dependencies = {
            name: header_imports(path.read_text(encoding="utf-8")) & modules.keys()
            for name, path in sorted(modules.items())
        }
        if targets:
            dependencies = dependency_closure(dependencies, targets)
        order = dependency_order(dependencies)
        if args.dry_run:
            print("\n".join(order))
            return 0
        for index, name in enumerate(order, 1):
            print(f"[{index}/{len(order)}] lake build {name}", flush=True)
            subprocess.run(["lake", "build", name], cwd=root, check=True)
        final_command = ["lake", "build", *targets]
        if targets:
            print(f"Checking selected targets: {' '.join(final_command)}", flush=True)
        else:
            print("Checking all default targets: lake build", flush=True)
        subprocess.run(final_command, cwd=root, check=True)
    except subprocess.CalledProcessError as error:
        return error.returncode if error.returncode > 0 else 1
    except (OSError, ValueError, KeyError, TypeError, graphlib.CycleError) as error:
        print(f"build_serial: {error}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        return 130
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
