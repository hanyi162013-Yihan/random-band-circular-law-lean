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

for filename, structure, fields in [
    ("BBVCoreSources", "GaussianProfileBBVCoreSources", ["bbv", "coreSection4"]),
    ("BBVOnlyProfileEndpoint", "GaussianProfileBBVSources", ["bbv", "coreSection4"]),
    ("PublishedConcreteGaussianProfile", "GaussianProfileConcreteSources",
     ["bbv", "ginibreSquared", "coreSection4"]),
    ("GinibreReducedSources", "GaussianProfileReducedSources",
     ["bbv", "ginibreSquared", "coreSection4"]),
    ("SparseSpectralEndpoint", "SparseGaussianSourceInputs",
     ["coreSection5", "coreSection3", "bbv"]),
    ("SubsequenceSourceEndpoint", "GaussianProfileSourceInputs",
     ["coreSection5", "coreSection3", "bbv"]),
    ("Section34GaussianProfileTheorem", "GaussianProfileSection34Inputs",
     ["coreSection34", "coreSection3", "bbv"]),
    ("PublishedSection3GaussianProfile", "GaussianProfilePublishedSection3Inputs",
     ["coreSection34", "coreSection3", "bbv"]),
    ("PublishedSourceGaussianProfile", "GaussianProfilePublishedSources",
     ["coreSection34", "coreLocal", "bbv"]),
]:
    source = code_only((root / f"section6/CircularLawSection6/{filename}.lean").read_text())
    match = re.search(rf"^structure {structure} .*? where\n(.*?)(?=^\S)", source, re.M | re.S)
    if not match or re.findall(r"^  (\w+)\s*:", match[1], re.M) != fields:
        raise SystemExit(f"Unexpected fields in {structure}")

consequences = code_only((root / "section6/CircularLawSection6/GinibreSourceConsequences.lean").read_text())
if re.search(r"\b(sorry|admit|unsafe|axiom|native_decide|set_option)\b", consequences):
    raise SystemExit("Forbidden checking escape/option in Gaussian reference consequences")

taper = code_only((root / "section5/CircularLawSections56/Section5/TaperVerifiedGinibre.lean").read_text())
if re.search(r"\b(sorry|admit|unsafe|axiom|native_decide|set_option)\b", taper):
    raise SystemExit("Forbidden checking escape/option in the taper Gaussian adapter")
match = re.search(r"^structure Section3TaperNonGaussianInputs.*? where\n(.*?)(?=^\S)",
                  taper, re.M | re.S)
if not match or re.findall(r"^  (\w+)\s*:", match[1], re.M) != [
        "minimum_singular", "counting", "local_comparison"]:
    raise SystemExit("Unexpected Gaussian analytic premise in the new taper interface")

normalization = code_only((root / "section3/ShortRingAnchor/BC12/GaussianPairNormalization.lean").read_text())
if re.search(r"\b(sorry|admit|unsafe|axiom|native_decide|set_option)\b", normalization):
    raise SystemExit("Forbidden checking escape/option in shared Gaussian normalization")
for path in ["Section8/BernoulliSection8/Section3GaussianLaw.lean",
             "Section10/BernoulliSection10Source/VerifiedGinibreSources.lean"]:
    if "BC12.normalizedGaussianPair_map hN" not in code_only((root / path).read_text()):
        raise SystemExit(f"Shared Gaussian normalization missing from {path}")

reference = code_only((root / "section6/CircularLawSection6/GinibreReferenceSources.lean").read_text())
for declaration in ["ginibre_raw_verified", "ginibre_spectral_verified"]:
    match = re.search(rf"^theorem {declaration}\b(.*?)(?=^theorem |^end )",
                      reference, re.M | re.S)
    if not match or re.search(r"\b(BBVComparisonInput|BC12GinibreInput|hBBV|hBC12)\b", match[1]):
        raise SystemExit(f"Unnecessary external source in {declaration}")
for filename in ["BBVCoreSources", "BBVProfileEndpoint", "DenseProfileEndpoint"]:
    source = code_only((root / f"section6/CircularLawSection6/{filename}.lean").read_text())
    if re.search(r"\b(ginibre_raw_of_bc12|ginibre_spectral_of_bc12)\b", source):
        raise SystemExit(f"Preferred {filename} route reverted to a conditional Gaussian limit")

print("Gaussian source migration: constructed reference sources and reduced public boundaries pass.")
