#!/usr/bin/env python3
"""Replay the changed proof modules with the pinned Lean kernel.

This is Lean's own `leanchecker`, not an external proof checker. Imported
dependencies are reused; the selected modules' declarations, including
private declarations, are replayed into their original import environments.
No checking limits, artifacts, dependency traces, or timestamps are changed.
"""

import argparse
from collections import Counter
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    "root": [
        "ShortRingAnchor.BC12.GaussianPairNormalization",
        "BernoulliSection8.Section3GaussianLaw",
        "BernoulliSection8.Section3Integration",
        "BernoulliSection10Source.VerifiedGinibreSources",
        "BernoulliSection10Source.FullBlockLogLimit",
        "BernoulliSection10Source.ConnectedHighBand",
        "BernoulliSection10Source.DensityCircularLaw",
    ],
    "section5": [
        "CircularLawSections56.Section5.PublishedSection3Source",
        "CircularLawSections56.Section5.VerifiedGinibreSources",
        "CircularLawSections56.Section5.TaperVerifiedGinibre",
        "CircularLawSections56.Section5.PublishedSection3ConcreteRings",
        "CircularLawSections56.Section5.PublishedSection3ConcreteAnchors",
        "CircularLawSections56.Section5.PublishedSection3ConcreteEndpoint",
        "CircularLawSections56.Section5.VerifiedComplexPressureInputs",
        "CircularLawSections56.Section5.VerifiedComplexSection5Endpoint",
    ],
    "section6": [
        "CircularLawSection6.GinibreReferenceSources",
        "CircularLawSection6.GinibreSourceConsequences",
        "CircularLawSection6.SparseSpectralEndpoint",
        "CircularLawSection6.SubsequenceSourceEndpoint",
        "CircularLawSection6.Section34GaussianProfileTheorem",
        "CircularLawSection6.PublishedSection3GaussianProfile",
        "CircularLawSection6.PublishedSourceGaussianProfile",
        "CircularLawSection6.GinibreReducedSources",
        "CircularLawSection6.GinibreFiniteFormulaSources",
        "CircularLawSection6.PublishedConcreteGaussianProfile",
        "CircularLawSection6.PublishedConcreteCoreEndpoint",
        "CircularLawSection6.DenseProfileConclusion",
        "CircularLawSection6.DenseProfileEndpoint",
        "CircularLawSection6.BBVCoreSources",
        "CircularLawSection6.BBVProfileEndpoint",
        "CircularLawSection6.BBVOnlyProfileEndpoint",
        "CircularLawSection6.VerifiedCorePressure",
    ],
}


def validate_replay(targets: list[str], output: str, returncode: int) -> int:
    if returncode:
        raise RuntimeError(f"Lean kernel replay exited with status {returncode}")
    expected = Counter(targets)
    actual = Counter(line.removeprefix("replaying ").strip()
                     for line in output.splitlines() if line.startswith("replaying "))
    if not expected or actual != expected:
        raise RuntimeError(f"Kernel replay coverage mismatch: expected {expected}, got {actual}")
    return sum(actual.values())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", choices=TARGETS, required=True)
    args = parser.parse_args()
    project = ROOT if args.project == "root" else ROOT / args.project
    targets = TARGETS[args.project]
    command = ["lake", "--no-cache", "env", "leanchecker", "--verbose", *targets]
    print(f"Kernel replay ({args.project}): {len(targets)} changed proof modules; one worker",
          flush=True)
    lines = []
    with subprocess.Popen(command, cwd=project,
                          env={**os.environ, "LEAN_NUM_THREADS": "1"},
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True, bufsize=1) as process:
        for line in process.stdout:
            print(line, end="", flush=True)
            lines.append(line)
        returncode = process.wait()
    count = validate_replay(targets, "".join(lines), returncode)
    print(f"PASS kernel replay: {count} modules, exact coverage, exit status zero", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
