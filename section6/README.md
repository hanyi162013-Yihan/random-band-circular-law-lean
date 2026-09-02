# Section 6: Gaussian noncompact profiles (work in progress)

This is a separate continuation of Section 5 on the
`codex/section6-formalization` branch. It imports the checked `section5/`
package and shares the parent's pinned Lean 4.33.0/mathlib dependencies.
No second mathlib checkout or large local download is needed.

## New proof layer

The current development batch adds literal sampled profiles, cyclic matrices,
product-law independence, normalized complex Gaussians, core/tail energies,
tail rotations and a uniform BV quadrature estimate. `SampledProfile` and
`CyclicMatrix` have passed targeted local strict checks. The rest of this
batch is undergoing compilation; it is not yet a verified checkpoint.
The earlier five-module checkpoint below remains separately recorded.

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

These are proved lemmas, not new axioms. This directory does **not** yet assert
the full noncompact Gaussian-profile circular-law theorem.

## Remaining mathematical boundaries

The new literal Gaussian model connections and BV quadrature require completion
of their current verification. BV Riemann-sum limits, compact-core cutoff
periodicization and singular-value comparison, Gaussian affine-log/cofactor
concentration, rotation-invariant expectation/Fubini transport, finite-matrix
Mirsky estimate, hard-edge input, and final sparse/dense replacement assembly
still need their full source-to-model connections. The existing conditional
helpers under `CircularLawSections56.Section6` are reused but are not counted
as proofs of these remaining boundaries. In particular, Section 5 supplies
the indicator-model results, not the noncompact-profile conclusion itself.

## Verification

The targeted local checks, axiom audit, and seven regression examples have
passed. [VERIFICATION.md](VERIFICATION.md) records their scope; the separate
GitHub workflow checks the published repository layout.

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
