# Section 6: Gaussian noncompact profiles (work in progress)

This is a separate continuation of Section 5 on the
`codex/section6-formalization` branch. It imports the checked `section5/`
package and shares the parent's pinned Lean 4.33.0/mathlib dependencies.
No second mathlib checkout or large local download is needed.

## New proof layer

The thirty-three-module checkpoint at commit `62b56b1` passed the dedicated
[GitHub verification](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33678501518):
the publication-layout build, transitive axiom audit (433 declarations,
367 theorem declarations), and all 40 regression examples. This includes
the expected tail Jensen inequality for planar almost every parameter,
with its integrability and nonvanishing inputs discharged by reuse.

The newer checked layer also instantiates Gaussian density and atom-log
control, identifies the compact core with the actual Section 5 finite-band
model, and proves determinant concentration on the original cyclic sample
space. Its constant is uniform in dimension and bandwidth. The Gaussian
finite variance bound currently covers dimensions at least two, which
suffices for the checked limits; an all-positive-dimensions extension is
under validation separately.

The next five-module batch extends the estimate to all positive dimensions,
transports Section 5's literal probability limit to the compact-core mean,
and constructs an actual Hermitian eigenvector coupling with its exact
Hilbert--Schmidt cost. These additions are not part of the 33-module checkpoint;
the 38-module integration and all 43 regressions are pending.

- `IteratedSqueeze`: the genuine two-limit argument (matrix size first,
  truncation radius second), with eventual radius hypotheses and the
  fourth-root tail cutoff. No uniform-in-radius convergence is assumed.
- `PotentialContinuity`: continuity of the explicit circular potential and
  its variance-scaled version, including convergence as core mass tends to one.
- `PolynomialJensen`: actual circle-integral Jensen lower bounds and radial
  monotonicity from mathlib's analytic Jensen theorem. Roots on the circle
  and zero constant terms in the monotonicity theorem are supported.
- `DeterminantJensen`: the actual polynomial `det(w B + A)`, its evaluation
  identity, circle integrability, and normalized Jensen lower bound.
- `VaryingNormalization`: varying-radius convergence from fixed radii in
  a dense set, and the countable a.e. version with one common full-measure set.
- `SampledProfile`, `CenteredMesh`: the actual centered cyclic sampling,
  normalized variance weights, exact core cardinality and integer-sum identities.
- `CyclicMatrix`, `ProfileMatrices`: concrete core/tail matrices, exact energy
  identities, variance normalization and product-law expected energies.
- `ComplexGaussian`, `CyclicIndependence`, `GaussianProfile`: the actual normalized
  circular complex Gaussian, atomlessness, independent core/tail matrices,
  and law-preserving tail rotations.
- `BVQuadrature`, `ProfileQuadrature`: uniform mesh error bounded by total
  variation times mesh size, specialized to the literal full and core sums.
- `ProfileMassLimits`, `SparseProfileGeometry`, `LimitingProfileMass`: actual
  normalized core/tail limits, sparse unwrapping, positive finite-radius
  tails, monotonicity and radius exhaustion.
- `ProfileComparability`: uniform dense and fixed-core variance bounds.
- `InvariantPhaseAverage`, `GaussianTailJensen`, `ReusedLogDetIntegrability`,
  `GaussianTailJensenAE`: invariant Fubini averaging, replacement local L²
  estimates transported to random samples, and the actual expected Jensen
  inequality on a common full-measure set for all sizes and integer radii.
- `GaussianDensityBounds`, `CoreBandIdentification`: actual bounded-density
  atom input, exact finite-band weights, IID marginal law, and matrix identity.
- `AffineLogFromDiagonal`, `RowResamplingClosure`, `DeterminantRowFibers`,
  `RowLogUniformBound`: diagonal-only row bounds, the zero-cofactor branch,
  automatic global L² and variance, and the reused Section 5 logarithmic constant.
- `CyclicRowTransport`, `NormalizedConcentration`, `GaussianCyclicConcentration`,
  `ProfileDiagonalBound`, `ProfileConcentration`: original cyclic-law
  concentration, the proved logarithmic rate limit, a bandwidth-uniform
  diagonal lower bound, and full/core/normalized-core model instantiations.

These are proved lemmas, not new axioms. This directory does **not** yet assert
the full noncompact Gaussian-profile circular-law theorem.

## Remaining mathematical boundaries

BV Riemann-sum limits, dense/core weight comparability, and the a.e.-parameter
expected tail Jensen inequality are checked. No stronger every-parameter
claim is needed for that Jensen connection.
Gaussian affine-log/cofactor concentration is now proved. The compact-core
raw-mean connection to the Section 5 endpoint is under validation.
Compact-core cutoff periodicization, finite-matrix singular-value comparison,
hard-edge control, and final sparse/dense replacement assembly still need
their full source-to-model connections. The existing conditional
helpers under `CircularLawSections56.Section6` are reused but are not counted
as proofs of these remaining boundaries. In particular, Section 5 supplies
the indicator-model results, not the noncompact-profile conclusion itself.

## Verification

[VERIFICATION.md](VERIFICATION.md) records the exact verified commit and scope:
33 modules, 433 audited declarations (367 theorem declarations, including
generated declarations), and 40 regression examples. This is not a proof of
the entire manuscript section.

For an integrated build in this repository layout:

```sh
cd section6
LEAN_NUM_THREADS=1 lake --no-cache build CircularLawSection6
lake --no-cache env lean -DwarningAsError=true AxiomAudit.lean
lake --no-cache env lean -DwarningAsError=true Regression.lean
```

Local development checks only the new modules against installed caches;
publication-layout integration is kept distinct from those targeted checks.
`AxiomAudit.lean` rejects every transitive axiom except `propext`,
`Classical.choice`, and `Quot.sound`. It does not discharge ordinary hypotheses.
