# Section 3: finite-moment and subgaussian high-band anchors

This package formalizes Propositions 3.6 and 3.8 of the circular-law manuscript
for the actual normalized cyclic random matrices. The logarithmic-potential
conclusions hold in probability for every fixed `z : ℂ`, with constants allowed
to depend on the shift.

## Results and inputs

| Result | Model and conclusion | Mathematical inputs |
| --- | --- | --- |
| Proposition 3.6 | Bounded-density finite-moment atoms; normalized shifted log-determinant convergence in the high-band regime | Canonical BBV comparisons; the density-alternative wrapper also takes geometric Brascamp–Lieb |
| Proposition 3.8 | Centered variance-one real subgaussian atoms, including discrete laws, on a three-neighbor full-block ring; the same high-band log-potential conclusion | Proposition 3.2, Cook Theorem 1.12 and canonical BBV comparisons |

For Proposition 3.6, dimensions and bandwidths tend to infinity and satisfy

```text
W ≥ M^(8/9 + ω),    0 < ω < 1/9.
```

For Proposition 3.8, `N = (s + 3)W`, with `s > 0`, `W > 0`,
`N,W → ∞`, and eventually `W ≥ N^(8/9 + ω)`.
The conclusion in each case is

```text
(1/N) log |det(H_N - z I_N)| → U_circ(z) in probability.
```

The model hypotheses specify the atom laws, moments, density where applicable,
independent copies, normalization and deterministic scales. The dense reference
has the specified normalized complex Gaussian law. Independence between matrix
sizes or between the ring and reference ensembles is not required.

The public proof modules are:

```lean
import ShortRingAnchor.Proposition36VerifiedGinibre
import ShortRingAnchor.Proposition38.VerifiedGinibre
```

See their declarations for the full signatures:
[Proposition 3.6](ShortRingAnchor/Proposition36VerifiedGinibre.lean) and
[Proposition 3.8](ShortRingAnchor/Proposition38/VerifiedGinibre.lean).
The [density proof map](HIGH_BAND_INTEGRATION.md) and
[subgaussian proof map](PROPOSITION38.md) give the source correspondence.

The literature inputs are explicit theorem parameters. Theorem 3.1 is a proved
source dependency. Hermitization counting, Lemma 3.5, Gaussian reference
estimates and the final logarithmic approximation are constructed internally.
The density-alternative wrapper exposes its Brascamp–Lieb argument for either
atom alternative. The specialized planar least-value route is documented in
[Proposition36Planar.lean](ShortRingAnchor/Proposition36Planar.lean).

## Internal proof

1. Construct the actual cyclic and dense matrix models, independent entry laws,
   row and column variance normalization, and a common moment budget.
2. Obtain the least-singular-value event. The density route applies Theorem 3.1
   and removes its Hilbert–Schmidt cutoff using the second moment and Markov.
   The subgaussian route combines Proposition 3.2 with Cook's estimate, proving
   spread, broad connectivity and the operator-norm event internally.
3. Apply the v3 probability estimates to Hermitization. Singular vectors give
   independent Hermitization eigenvectors, yielding simultaneous small-value
   counts above the mesoscopic cutoff.
4. Compare the Stieltjes transforms on each fixed compact horizontal interval,
   then derive the local squared-singular-value CDF estimate by Poisson smoothing.
5. Control the low, middle and high logarithmic ranges using least values,
   counts, negative moments, CDF comparison and upper second moments.
6. Identify the singular-value logarithmic sum with the matrix log determinant
   and complete the approximation in probability, including singular bad events.

The dense Gaussian reference estimates use the pinned
[Ginibre proof dependency](https://github.com/hanyi162013-Yihan/ginibre-correlation-identities-lean),
which derives the finite spectral law and correlation identities from Gaussian
entries. The law transports, logarithmic limit and negative-moment tightness
are proved in the dependency chain; the negative-moment route uses BBV and
provides the exponent `p = 1/128`.

## Compact Stieltjes-to-CDF comparison

For symmetric finite spectra `(+s,-s)` and `(+t,-t)`, the theorem
`squaredCdfDistanceOn_le_of_stieltjes` proves

```text
sup_{0 ≤ x ≤ R²} |F_{s²}(x) - F_{t²}(x)|
  ≤ ((2R + 10) E + (8C + 8) sqrt(v)) / pi.
```

Its premises are `R ≥ 0`, `v > 0`, `3 sqrt(v) ≤ 1`, `E ≥ 0`,
Stieltjes-transform distance at most `E` on `[-R-1,R+1] + iv`, and
imaginary part of the reference transform at most `C`. The proof covers
zero values and atoms at interval endpoints.

`matrix_stieltjesTrace_eq_symmetric_singularValues` identifies the actual
Hermitization resolvent trace with the symmetric singular-value transform.
The probability connection constructs a horizontal grid, its union bound
and Lipschitz interpolation, and obtains one common CDF exponent for all
fixed cutoffs. The comparison applies to every fixed compact interval.
See [MatrixLocalBulk.lean](ShortRingAnchor/MatrixLocalBulk.lean),
[V3MatrixLocalBulk.lean](ShortRingAnchor/V3MatrixLocalBulk.lean) and
[RADIUS_SHORTCUT.md](RADIUS_SHORTCUT.md).

## Nonsingularity and measure theory

Every nonzero multivariate complex polynomial has a null zero set under a
finite product of sigma-finite nonatomic coordinate measures. The proof uses
finite one-variable root sets and Fubini induction. Bounded marginal densities
give absolute continuity, and independent coordinates give the joint product
law. Real-density atoms are handled on their real sample spaces.

Explicit polynomial witnesses prove determinant nonvanishing for the relevant
density models at each fixed shift. This is a separate almost-sure statement
for each chosen `z`, not a common event over all complex shifts. For discrete
ring atoms, the least-value argument controls singular samples by events whose
probability tends to zero.

## Build and verification

From the repository root, with the pinned Lean 4.33.0 and mathlib dependencies:

```sh
lake build ShortRingAnchor
```

[GitHub Actions](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/workflows/section3.yml)
builds the Section 3 import closure, scans for placeholders and checks exact
axiom reports. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
The [cross-project certificate](../POINTWISE_Z_VERIFICATION.md) records
downstream verification.

[UPSTREAM.md](UPSTREAM.md) documents source provenance and licenses.
Proposition 3.2, Cook, BBV and the real geometric Brascamp–Lieb input have the
explicit boundaries above; an axiom audit does not prove these hypotheses.
