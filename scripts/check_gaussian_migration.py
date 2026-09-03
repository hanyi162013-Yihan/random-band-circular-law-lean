#!/usr/bin/env python3
"""Lexical guard for the migrated public interfaces, not a Lean proof check."""
from pathlib import Path
import re
from check_placeholders import code_only

root = Path(__file__).resolve().parents[1]

for folder in ["section5/CircularLawSections56/Section5",
               "Section10/BernoulliSection10Source"]:
    source = code_only((root / folder / "VerifiedGinibreSources.lean").read_text())
    if re.search(r"\b(sorry|admit|unsafe|axiom|native_decide|set_option)\b", source):
        raise SystemExit(f"Forbidden checking escape/option in {folder}")
    for required in ["theorem ginibreOnSequence_hasLaw", "theorem provedGinibreInput",
                     "BC12.ginibre_logdet_convergesInProbability_of_ginibreLaw",
                     "BC12.negativeMomentTightness_of_ginibreLaw_and_v3"]:
        if required not in source:
            raise SystemExit(f"Missing constructed Gaussian source: {folder}: {required}")

for path in [
    "section5/CircularLawSections56/Section5/PublishedSection3ConcreteEndpoint.lean",
    "section5/CircularLawSections56/Section5/PublishedSection3ConcreteAnchors.lean",
    "section5/CircularLawSections56/Section5/PublishedSection3ConcreteRings.lean",
    "Section10/BernoulliSection10Source/DensityCircularLaw.lean",
    "Section10/BernoulliSection10Source/ConnectedHighBand.lean",
    "Section10/BernoulliSection10Source/FullBlockLogLimit.lean",
    "section6/CircularLawSection6/DenseProfileConclusion.lean",
    "section6/CircularLawSection6/DenseProfileEndpoint.lean",
]:
    source = code_only((root / path).read_text())
    if re.search(r"\(\w+\s*:\s*BC12GinibreInput\)", source):
        raise SystemExit(f"External Gaussian source reintroduced in {path}")

for filename, structure in [("BBVCoreSources", "GaussianProfileBBVCoreSources"),
                            ("BBVOnlyProfileEndpoint", "GaussianProfileBBVSources")]:
    source = code_only((root / f"section6/CircularLawSection6/{filename}.lean").read_text())
    match = re.search(rf"^structure {structure} .*? where\n(.*?)(?=^\S)", source, re.M | re.S)
    if not match or re.findall(r"^  (\w+)\s*:", match[1], re.M) != ["bbv", "coreSection4"]:
        raise SystemExit(f"Unexpected fields in {structure}")

print("Gaussian source migration: constructed reference sources and reduced public boundaries pass.")
