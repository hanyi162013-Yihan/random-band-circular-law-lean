#!/usr/bin/env python3
"""Supplement the kernel/axiom audits with a source-token scan.

Ignore Lean comments (including nested block comments) and string literals.
This is a lexical safeguard, not a substitute for checking compiled axioms.
Use --path to restrict the scan to one directory inside the repository.
"""

import argparse
import re
import os
import subprocess
import sys
from pathlib import Path


def code_only(source: str) -> str:
    result = list(source)
    i = depth = 0
    quoted = False
    while i < len(source):
        end = i + 1
        if depth:
            if source.startswith("/-", i):
                depth += 1
                end += 1
            elif source.startswith("-/", i):
                depth -= 1
                end += 1
        elif quoted:
            if source[i] == "\\":
                end = min(i + 2, len(source))
            elif source[i] == '"':
                quoted = False
        elif source.startswith("/-", i):
            depth = 1
            end += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            if end == -1:
                end = len(source)
        elif source[i] == '"':
            quoted = True
        else:
            i += 1
            continue
        for j in range(i, end):
            if result[j] != "\n":
                result[j] = " "
        i = end
    return "".join(result)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--path", type=Path,
        help="scan only this directory (relative to the repository root)",
    )
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    selected = None
    if args.path is not None:
        directory = (root / args.path).resolve()
        try:
            selected = directory.relative_to(root)
        except ValueError:
            parser.error(f"scan directory is outside the repository: {args.path}")
        if not directory.is_dir():
            parser.error(f"scan directory does not exist or is not a directory: {args.path}")
    # Include newly written source before it is staged; a tracked-only scan
    # can otherwise silently omit the very proofs being checked locally.
    if (root / ".git").exists():
        paths = subprocess.check_output(
            ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z", "--", "*.lean"],
            cwd=root,
        ).decode().split("\0")
        mode = "tracked and new"
    else:
        # Source-only archives have no Git metadata. Exclude generated
        # dependency/build trees even after the user has fetched the cache.
        paths = []
        for directory, dirs, files in os.walk(root):
            dirs[:] = [name for name in dirs if name not in {".git", ".lake"}]
            paths.extend(str((Path(directory) / name).relative_to(root))
                         for name in files if name.endswith(".lean"))
        mode = "source archive"
    failed = False
    count = 0
    for relative in sorted(set(filter(None, paths))):
        if selected is not None and not Path(relative).is_relative_to(selected):
            continue
        count += 1
        code = code_only((root / relative).read_text())
        for match in re.finditer(r"\b(sorry|admit|axiom)\b", code):
            line = code.count("\n", 0, match.start()) + 1
            print(f"{relative}:{line}: forbidden token {match.group()}")
            failed = True
    if not count:
        scope = "workspace" if selected is None else str(selected)
        print(f"No {scope} Lean files found", file=sys.stderr)
        return 1
    if not failed:
        scope = "workspace" if selected is None else str(selected)
        print(f"Source-token scan passed: {count} {scope} Lean files ({mode})")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
