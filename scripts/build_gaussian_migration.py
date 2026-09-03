#!/usr/bin/env python3
"""Serially check the real root/Section 5/Section 6 import closures.

No artifacts or dependency traces are fabricated. Every module is passed
through Lake, followed by an ordinary build of the public targets. Include
the pinned Ginibre dependency in the serial order to bound peak memory.
"""

import argparse
import subprocess
from pathlib import Path

from build_serial import discover_modules, header_imports, dependency_closure, dependency_order
from check_axioms import run_audits

ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    "root": ["ShortRingAnchor", "CircularLawSection4", "BernoulliLinearAlgebra",
             "BernoulliSection9", "SubgaussianSection8", "BernoulliSection8", "BernoulliSection10",
             "BernoulliSection10Complex", "BernoulliSection10Source"],
    "section5": ["CircularLawSections56"],
    "section6": ["CircularLawSection6", "CircularLawSection6.GinibreFiniteFormulaSources"],
}
AUDITS = {
    "root": ["Section4/AxiomAudit.lean", "Section4/CompanionAxiomAudit.lean",
             "Section4/FourGapsAxiomAudit.lean", "Section4/FlatAxiomAudit.lean",
             "Section4/Section4CompleteAxiomAudit.lean", "Section4/AssumptionFreeAxiomAudit.lean",
             "SubgaussianSection8/AxiomAudit.lean", "Section8/AxiomAudit.lean",
             "Section8/Section3IntegrationAudit.lean",
             "Section10/BernoulliSection10/AxiomAudit.lean",
             "Section10/BernoulliSection10/AsymptoticAxiomAudit.lean",
             "Section10/BernoulliSection10/CompletionAxiomAudit.lean",
             "Section10/BernoulliSection10Complex/AnalyticAxiomAudit.lean",
             "Section10/BernoulliSection10Complex/FrontAxiomAudit.lean",
             "Section10/BernoulliSection10Complex/GaussianReferenceAxiomAudit.lean",
             "Section10/BernoulliSection10Complex/ClosureAxiomAudit.lean",
             "Section10/BernoulliSection10Source/ModelAxiomAudit.lean",
             "Section10/BernoulliSection10Source/AxiomAudit.lean",
             "Section9/AxiomAudit.lean", "Section9/SmallBallAxiomAudit.lean"],
    "section5": ["AxiomAudit.lean", "GaussianMigrationAudit.lean"],
    "section6": ["GaussianMigrationAudit.lean"],
}


def sources(ginibre_root: Path) -> dict[str, Path]:
    modules = {}
    for project in [ROOT, ROOT / "section5", ROOT / "section6", ginibre_root]:
        discovered = discover_modules(project)
        overlap = modules.keys() & discovered.keys()
        if overlap:
            raise ValueError(f"Duplicate modules: {sorted(overlap)}")
        modules.update(discovered)
    return modules


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", choices=TARGETS, required=True)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--audit", action="store_true")
    parser.add_argument("--ginibre-root", type=Path,
                        default=ROOT / ".lake/packages/GinibreCorrelationIdentities")
    args = parser.parse_args()
    project = ROOT if args.project == "root" else ROOT / args.project
    if args.audit:
        if args.dry_run:
            raise ValueError("Use --dry-run for builds, not audits")
        run_audits(project, [Path(p) for p in AUDITS[args.project]])
        return 0
    modules = sources(args.ginibre_root.resolve())
    dependencies = {name: header_imports(path.read_text()) & modules.keys()
                    for name, path in modules.items()}
    # Reject cycles in the entire source graph, including legacy adapters.
    dependency_order(dependencies)
    selected = dependency_closure(dependencies, TARGETS[args.project])
    order = dependency_order(selected)
    if args.dry_run:
        print("\n".join(order))
        print(f"{args.project}: {len(order)} modules; no Lean command executed")
        return 0
    failed, blocked = set(), set()
    positions = {name: index for index, name in enumerate(order, 1)}

    def check_batch(batch: list[str]) -> None:
        # The no-build probe only accepts Lake-validated traces. A cache miss
        # recursively narrows the batch, down to ordinary serial compilation.
        # No timestamps, traces or artifacts are manufactured here.
        active = []
        for name in batch:
            if selected[name] & (failed | blocked):
                blocked.add(name)
                print(f"[{positions[name]}/{len(order)}] BLOCKED {name}", flush=True)
            else:
                active.append(name)
        if not active:
            return
        if len(active) > 1:
            probe = subprocess.run(
                ["lake", "--no-build", "--log-level", "error", "build",
                 *("+" + name for name in active)],
                cwd=project, capture_output=True, text=True)
            if probe.returncode == 0:
                print(f"[{positions[active[-1]]}/{len(order)}] Lake validated "
                      f"{len(active)} cached modules (through {active[-1]})", flush=True)
                return
            middle = len(active) // 2
            check_batch(active[:middle])
            check_batch(active[middle:])
            return
        name = active[0]
        print(f"[{positions[name]}/{len(order)}] lake build +{name}", flush=True)
        result = subprocess.run(["lake", "--log-level", "error", "build", "+" + name],
                                cwd=project)
        if result.returncode:
            failed.add(name)

    for start in range(0, len(order), 32):
        check_batch(order[start:start + 32])
    if failed:
        print(f"Failed: {sorted(failed)}; blocked: {len(blocked)}", flush=True)
        return 1
    print(f"Final public targets: {TARGETS[args.project]}", flush=True)
    return subprocess.run(["lake", "--no-cache", "build", *TARGETS[args.project]],
                          cwd=project).returncode


if __name__ == "__main__":
    raise SystemExit(main())
