# Section 6: Gaussian noncompact profiles (work in progress)

This is a separate continuation of Section 5 on the
`codex/section6-formalization` branch. It imports the checked `section5/`
package and shares the parent's pinned Lean 4.33.0/mathlib dependencies.
No second mathlib checkout or large local download is needed.

## New proof layer

The fourteen-module checkpoint at commit `0dce34d` passed the dedicated
[GitHub verification](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33667008094):
the publication-layout build, transitive axiom audit, and all 20 regression
examples. Three subsequent modules (`ProfileMassLimits`, `SparseProfileGeometry`,
`ProfileComparability`) are a new development batch, not covered by that run.

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

These are proved lemmas, not new axioms. This directory does **not** yet assert
the full noncompact Gaussian-profile circular-law theorem.

## Remaining mathematical boundaries

BV Riemann-sum limits and dense/core weight comparability are being checked in
the next batch. Compact-core cutoff periodicization and singular-value
comparison, Gaussian affine-log/cofactor
concentration, rotation-invariant expectation/Fubini transport, finite-matrix
Mirsky estimate, hard-edge input, and final sparse/dense replacement assembly
still need their full source-to-model connections. The existing conditional
helpers under `CircularLawSections56.Section6` are reused but are not counted
as proofs of these remaining boundaries. In particular, Section 5 supplies
the indicator-model results, not the noncompact-profile conclusion itself.

## Verification

[VERIFICATION.md](VERIFICATION.md) records the exact verified commit and scope:
14 modules, 215 audited declarations (173 theorem declarations, including
generated declarations), and 20 regression examples. This is not a proof of
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
