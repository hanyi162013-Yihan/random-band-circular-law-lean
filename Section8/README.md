# Section 8: discrete Bernoulli branch

This directory formalizes the Rademacher specialization of Section 8, with
independent entries taking values ±1 with equal probabilities. The actual matrix
is `BernoulliSection8.rademacherMatrix W s`, with block count `s + 3`, scalar
dimension `N = (s + 3)W` and normalization `1 / sqrt(3W)`.

## Public results and inputs

The results in
[Section8Results.lean](BernoulliSection8/Section8Results.lean) are
`BernoulliSection8.section8_bernoulli_log_potential` and
`BernoulliSection8.section8_bernoulli_circular_law`.
The log-potential statement holds in probability for every fixed complex shift.
The circular law applies to every bounded continuous real test function.

The model conditions are positive widths and core-site counts, `W → ∞` and
`W / log N → ∞`. The permitted mathematical inputs are:

- `NguyenBottomSingularInput`, at a subgaussian bound at least one.
- `CookDeformedSquareInput`, specialized to the actual Rademacher family.
- `RademacherSection3UpstreamInputs`: Proposition 3.2, Cook Theorem 1.12 and
  the two canonical BBV comparisons, with a common comparison constant.

The high-band anchor follows from the concrete Section 3 Proposition 3.8.
Its Gaussian reference law and estimates are constructed internally. The final
proof also constructs pressure, reset, seam, energy and log-potential estimates.
Section 4 is not an additional analytic input.

The reset argument integrates each capped loss before summing. Cook's error is
averaged, while Nguyen's exponentially small interface failures are
union-bounded using `log N / W → 0`. The independent anchor contains
`ceil(W^(1/200))` complete cells and a terminal packet. Zero determinants
are included in the terminal bad events.

See the [source map](SOURCE_MAP.md),
[Section 3 connection](SECTION3_INTEGRATION.md),
[Section 9 dependency map](SECTION9_DEPENDENCY_AUDIT.md) and
[Section 10 reuse map](SECTION10_REUSE_AUDIT.md).
The [general subgaussian result](../SubgaussianSection8/README.md) covers fixed
real IID atom laws with a finite subgaussian MGF parameter.

## Build and verification

Run from the repository root with the pinned dependencies available:

```sh
lake build BernoulliSection8
python3 scripts/check_axioms.py --audit-file Section8/AxiomAudit.lean
lake env lean Section8/PublicSignatureAudit.lean
python3 scripts/check_placeholders.py --path Section8
```

[GitHub Actions](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/workflows/lean.yml)
builds the two Section 8 targets and their actual imports, checks the public
signatures and audits the endpoints together with the Section 3 connection.
The [verification certificate](../POINTWISE_Z_VERIFICATION.md) specifies the
cross-project coverage. Axiom reports permit only `propext`,
`Classical.choice` and `Quot.sound`.
