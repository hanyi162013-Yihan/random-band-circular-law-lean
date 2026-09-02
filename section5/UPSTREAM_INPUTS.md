# Accepted Section 3 inputs and the existing LSV project

The user's
[high-band-lsv-2609-01295](https://github.com/hanyi162013-Yihan/high-band-lsv-2609-01295)
project covers the high-band Hilbert–Schmidt-truncated least-singular-value
estimate corresponding to **Theorem 3.1** and Appendix B of the manuscript
(the theorem is sometimes informally called Proposition 3.1).

The inspected public revision is `d20607307ee57f31d77397b34bdb2910bef30936`.
The paper-facing entry points are:

- `HighBandLSV.PaperModelTheorem.planar_main_statement`
- `HighBandLSV.PaperModelTheorem.real_main_statement`

They give the actual-model truncated probability bound with exponential
threshold and an eventual natural cutoff. The real theorem retains the explicit
`RealFiniteGeometricBrascampLieb` hypothesis; the planar theorem does not.
Neither statement asserts the complete remaining Section 3 argument.

This Section 5 release retains its agreed ordinary Section 3 inputs. It does
**not** claim a Lean import/transport adapter from that separate LSV project's
model, least-singular-value and HS definitions into
`Section3TaperAnalyticInputs`; the repository link documents provenance, not a
completed dependency connection. No new LSV dependency or toolchain is downloaded.

The counting estimate (Proposition 3.4), local comparison (Lemma 3.5), and other
short-ring/dense-reference ingredients remain separately identified in
[SECTION5_COVERAGE.md](SECTION5_COVERAGE.md). The five small support modules
included here are definitions and conditional assembly tools, not a proof of
all those upstream analytic inputs.
