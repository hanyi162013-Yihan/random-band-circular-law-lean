# Section 10 — real and planar-complex bounded-density circular laws

Lean 4 formalization of the IID bounded-density branches of Section 10 in
Yi Han's [arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1):
Proposition 10.1, local results 10.2–10.10, equations 10.30–10.57, and their
assembly into the circular-law conclusion of Theorem 2.10.

**Verified:** [cloud run 33719162307](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33719162307)
passed at `362c47f`: all three Section 10 targets and their actual dependencies,
207 chapter files without placeholders, 492 exact axiom reports, and the
final printed signatures. Verification took 4 minutes 13 seconds using
checked caches. No local integration build was performed, and no completed
whole-repository check is claimed. See [SOURCE_CONNECTION_AUDIT.md](SOURCE_CONNECTION_AUDIT.md).

## Public entry points

Use `import BernoulliSection10Source`. The final results are in
[DensityCircularLaw.lean](BernoulliSection10Source/DensityCircularLaw.lean),
all under the namespace `BernoulliSection10Source`:

| Entry point | Conclusion |
|---|---|
| `planar_density_circular_law` | Circular empirical spectral limit for complex planar-density atoms |
| `real_density_circular_law` | Circular empirical spectral limit for real density atoms |
| `planar_density_ring_log_limit` | Complex-atom normalized log-determinant limit for arbitrary growing bandwidth |
| `real_density_ring_log_limit` | Real-atom normalized log-determinant limit for arbitrary growing bandwidth |

The circular laws apply to every bounded continuous real test function on
`ℂ`. The matrices are the literal normalized three-neighbor full-block
cyclic matrices, with `N n = (s n + 3) * W n`. Their entries are sampled
from one infinite IID sequence; the finite physical-row marginals are proved
to be the required product laws. No auxiliary random model is an input.

## Exact retained assumptions

- A real or complex probability law with mean zero, unit second moment,
  bounded Lebesgue density, and finite third absolute moment.
- Positive integer bandwidths `W n` tending to infinity. The number of
  block sites may vary without a further growth condition.
- The explicitly accepted BBV and BC12 literature inputs; in the real
  branch only, the geometric Brascamp–Lieb inequality as well.

Complex density is a condition on the joint planar law. Neither independent
real/imaginary parts, circular symmetry, nor `E ξ² = 0` is assumed. The
numerical density normalization `L ≥ 1` is constructed internally and is
not a public complex-model condition.

The actual Section 3 model, LSV application, counting/bulk estimates,
Gaussian reference and high-band limit are connected internally. The final
statements retain no `Section3Inputs`, high-band, reset, seam, remainder,
pressure or reference-limit certificate. Tao–Vu replacement is imported as
proved source. BBV/BC12 and the real Brascamp–Lieb input are not claimed as
proved internally; see [ASSUMPTIONS.md](ASSUMPTIONS.md).

## Mathematical organization and maps

| Library | Role |
|---|---|
| `BernoulliSection10` | Stable real-density proofs and reusable deterministic, asymptotic and replacement results |
| `BernoulliSection10Complex` | Planar density/affine logarithms, actual complex row and packet laws, concentration, reset, seam, pressure and spectral assembly |
| `BernoulliSection10Source` | Concrete Section 3 connections for both atom spaces, literal Ginibre construction, final certificate-free entry points and audits |

The [real proof map](FORMALIZATION_MAP.md) records each original statement
and its proof dependencies. The [complex extension map](COMPLEX_FORMALIZATION_MAP.md)
records every item from 10.1 through 10.10 and the final closure. The
[source-connection audit](SOURCE_CONNECTION_AUDIT.md) records the common
final interface, exact dependency scope and successful verification gates.

Deterministic exterior algebra comes from the stable Section 9 library.
Planar small-ball facts come from Section 4; generic tail integration,
finite-product transports and Tao–Vu adapters are reused, as documented in
[COMPLEX_REUSE_AUDIT.md](COMPLEX_REUSE_AUDIT.md) and
[PROVENANCE.md](PROVENANCE.md). Root Lake selects the published `section3/`
source, not the historical `vendor/short-ring-analysis/` snapshot.

## Density-definition correction

The source integration exposed a Lean-only error in the old Section 3
density record: undeclared `top` was accidentally generalized, making its
finite-bound field impossible to satisfy. The single shared correction
`5c7be7b` uses `(⊤ : ENNReal)` and guards the record against implicit
generalization. Both development tasks reuse that same commit. See
[DENSITY_SCHEMA_CORRECTION.md](DENSITY_SCHEMA_CORRECTION.md) for the
printed evidence, canonical file hash and construction regression.

The [old real audit](AUDIT.md) and
[historical real README](REAL_BASELINE_README.md) remain available as earlier
conditional verification records. They do not certify the old upstream
density record's inhabitability or eliminate the literature assumptions.

## Reproduction and scope

Use Lean `v4.33.0`, the committed mathlib manifest, and Python 3.11 or newer.
The scoped cloud-only integration procedure, placeholder scan, exact axiom
audits and printed-signature checks are listed in
[SOURCE_CONNECTION_AUDIT.md](SOURCE_CONNECTION_AUDIT.md). For a scoped build:

```sh
lake exe cache get
lake build BernoulliSection10Source
python3 scripts/check_axioms.py \
  --audit-file Section10/BernoulliSection10Source/AxiomAudit.lean
```

This scope does not include heterogeneous atom laws in the broad versions
of 10.2–10.3, directional conditional-density alternatives, or arbitrary
finite-`(2+α)`-moment extensions. Allowing three block sites as well as the
paper's at-least-four-site case is an extension, not a proof gap.
