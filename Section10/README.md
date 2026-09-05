# Section 10: real and complex bounded-density block rings

This package formalizes the real and planar-complex IID bounded-density,
finite-third-moment branches of results 10.1–10.10 and the circular-law
conclusion of Theorem 2.10. The matrices are the actual normalized
three-neighbor full-block rings.

## Public entry points

Use `import BernoulliSection10Source`. The results in
[DensityCircularLaw.lean](BernoulliSection10Source/DensityCircularLaw.lean)
are in the namespace `BernoulliSection10Source`:

| Theorem | Conclusion |
| --- | --- |
| `planar_density_circular_law` | Circular empirical spectral limit for complex planar-density atoms |
| `real_density_circular_law` | Circular empirical spectral limit for real density atoms |
| `planar_density_ring_log_limit` | Complex-atom normalized log-determinant limit for every fixed complex shift |
| `real_density_ring_log_limit` | Real-atom normalized log-determinant limit for every fixed complex shift |

The circular laws apply to every bounded continuous real test function on
`ℂ`. The dimension is `N n = (s n + 3) * W n`. Entries are sampled from one
infinite IID sequence; the finite physical-row marginals are proved to have
the required product laws.

## Assumptions

- A real or complex probability law with mean zero, unit second moment,
  bounded Lebesgue density and finite third absolute moment.
- Positive integer bandwidths `W n` tending to infinity. The number of
  block sites may vary without a further growth condition.
- The explicit BBV comparison input; the real branch also takes the
  geometric Brascamp–Lieb inequality.

Complex density is a condition on the joint planar law. Independent real and
imaginary parts, circular symmetry and `E ξ² = 0` are not required. The density
bound normalization `L ≥ 1` is constructed internally.

The proof constructs the Section 3 model, least-value and counting estimates,
Gaussian reference, high-band limit, pressure and spectral closure.
Tao–Vu replacement is a proved source dependency.
`VerifiedGinibreSources` constructs the actual normalized Gaussian law,
full-log limit and negative-moment bound from the proved Gaussian formulas
and BBV. The mathematical inputs above remain explicit theorem hypotheses.

## Organization and coverage

| Library | Role |
| --- | --- |
| `BernoulliSection10` | Real-density proofs and reusable deterministic, asymptotic and replacement results |
| `BernoulliSection10Complex` | Planar density estimates, actual complex row and packet laws, concentration, reset, seam, pressure and spectral assembly |
| `BernoulliSection10Source` | Concrete Section 3 applications, Gaussian reference construction, final endpoints and audits |

The [real proof map](FORMALIZATION_MAP.md) and
[complex proof map](COMPLEX_FORMALIZATION_MAP.md) record the source statements
and their dependencies. The [source-connection audit](SOURCE_CONNECTION_AUDIT.md)
specifies the checked public signatures and dependency scope.
The [reusable real-density layer](REAL_BASELINE_README.md) documents the
generic assembly.

Deterministic exterior algebra comes from Section 9 and planar small-ball
facts from Section 4. Root Lake loads the Section 3 proofs from `section3/`.
[PROVENANCE.md](PROVENANCE.md) records the source dependencies.

The endpoints cover fixed IID atom laws with a finite third moment.
Heterogeneous laws, directional conditional-density alternatives and general
finite-`(2+α)`-moment extensions are outside this scope. The implementation
permits three block sites, including the paper's at-least-four-site case.

## Build and verification

Use Lean 4.33.0, the committed dependency manifests and Python 3.11 or newer.
With dependencies available, run from the repository root:

```sh
lake build BernoulliSection10Source
python3 scripts/check_axioms.py \
  --audit-file Section10/BernoulliSection10Source/AxiomAudit.lean
```

[GitHub Actions](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/workflows/section10-density.yml)
provides scoped builds, placeholder scans, axiom audits and printed-signature
checks. The [cross-project certificate](../POINTWISE_Z_VERIFICATION.md)
records verification of the public endpoints and selected kernel replays.
Transitive axiom reports permit only `propext`, `Classical.choice` and
`Quot.sound`.
