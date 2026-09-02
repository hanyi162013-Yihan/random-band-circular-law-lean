# Section 6: Gaussian noncompact profiles (work in progress)

This is a separate continuation of Section 5 on the
`codex/section6-formalization` branch. It imports the checked `section5/`
package and shares the parent's pinned Lean 4.33.0/mathlib dependencies.
No second mathlib checkout or large local download is needed.

## New proof layer

The fifty-module checkpoint at commit `e177c08` passed the dedicated
[GitHub verification](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33689098945):
the publication-layout build, transitive axiom audit (584 declarations,
507 theorem declarations), and all 53 regression examples.

This includes the actual Gaussian density and atom-log control, core model
identification, all-positive-dimension determinant concentration, and the
Section 5 probability-to-core-mean bridge. It also proves the singular-value
Lipschitz comparison using canonical singular bases and their overlap
energies, the exact logarithmic cutoff constant, the literal matrix energy
identification, and cutoff measurability on the nonsingular event. No Mirsky
inequality or measurable singular-frame choice is supplied as a premise.

Seven further verified modules derive expected
cutoff stability and integrability, the literal Gaussian tail error, the
determinant/singular-log and scaling identities, and the actual expected
core/full sandwich, varying-scale cutoff stability, and actual radial mean
monotonicity and normalization. They are included in the 50-module checkpoint.

The next four modules (54 total, 59 regression examples) connect the
canonical floor-radius band geometry, positive fixed-scale Section 5 mean
transport, the actual raw core mass limit, and varying cutoff normalization.
They also construct a common-atom routing coupling and prove its expected
boundary-row energy bound. These four modules are under validation, not
included in the checkpoint; the contiguous-block geometry remains pending.

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
- `GaussianAllDimensions`, `TriangularLawTransport`, `CompactCoreRawBridge`:
  the dimension-one case, measure-preserving probability transport, and the
  literal Section 5 probability-to-core-mean implication with concentration proved.
- `WeightedSpectralCoupling`, `HermitianSpectralCoupling`, `PositiveSingularBasis`,
  `SingularSpectralCoupling`: actual orthonormal frames and overlap-energy
  comparisons, including the singular-value Lipschitz sum bound.
- `LogCutoffComparison`, `MatrixCutoffComparison`, `CutoffMeasurability`:
  the exact cutoff constant and normalization, shifted/scaled matrix bounds,
  and a measurable representative agreeing off the singular event.

These are proved lemmas, not new axioms. This directory does **not** yet assert
the full noncompact Gaussian-profile circular-law theorem.

## Remaining mathematical boundaries

BV Riemann-sum limits, dense/core weight comparability, and the a.e.-parameter
expected tail Jensen inequality are checked. No stronger every-parameter
claim is needed for that Jensen connection.
Gaussian affine-log/cofactor concentration, the literal Section 5 probability
to core-mean implication, and finite-matrix singular-value comparison are
checked. Canonical radius/scale and eventual-geometry assembly of the core
endpoint, compact-core cutoff periodicization, the cited direct comparison,
hard-edge control, and final sparse/dense replacement assembly still need
their full source-to-model connections. The existing conditional
helpers under `CircularLawSections56.Section6` are reused but are not counted
as proofs of these remaining boundaries. In particular, Section 5 supplies
the indicator-model results, not the noncompact-profile conclusion itself.

## Verification

[VERIFICATION.md](VERIFICATION.md) records the exact verified commit and scope:
50 modules, 584 audited declarations (507 theorem declarations, including
generated declarations), and 53 regression examples. This is not a proof of
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
