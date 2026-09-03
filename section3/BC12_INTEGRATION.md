# BC12-free Section 3 endpoints

The public endpoints added by this integration are:

- `ShortRingAnchor.proposition36_cyclicShortRing_withoutBC12`
- `ShortRingAnchor.Proposition38.proposition38_withoutBC12`

Neither theorem takes a BC12 negative-moment conclusion, a Ginibre
log-determinant convergence conclusion, or a projection/correlation formula
as an argument. The earlier conditional assembly lemmas remain available
unchanged for API compatibility.

## Pinned proof dependency

`lakefile.toml` and `lake-manifest.json` pin
[`GinibreCorrelationIdentities`](https://github.com/hanyi162013-Yihan/ginibre-correlation-identities-lean)
to `403bab996ebc6b8331531bdf12b7a8c84bf61a4d`, using the same Lean 4.33.0
and mathlib revision as Section 3. It derives the actual Gaussian spectral
law and correlation identities from independent complex Gaussian entries.
It is a source dependency, not a new external mathematical interface.

## What is connected

1. `BC12/VerifiedKernel.lean` checks exact agreement of both explicit kernels,
   squared weights, and empirical densities, and constructs the weighted
   projection interface from Gaussian orthogonality.
2. `BC12/VerifiedStatistics.lean` proves genuine L2 integrability of the
   actual statistic by finite Cauchy--Schwarz, converts the upstream
   covariance into the centered-square integral, and divides by `n²`.
3. `BC12/VerifiedMatrixStatistics.lean` compares characteristic-polynomial
   root multisets. Thus the proved Schur statistics also apply to the
   arbitrary eigenvalue enumeration already used by Section 3, without
   assuming that arbitrary ordering is measurable.
4. `BC12/GaussianEntryLawBridge.lean` identifies the planar density with two
   independent real Gaussians and checks the `1/sqrt(2)` normalization.
   `BC12/GaussianMatrixLawBridge.lean` then proves that the old Gaussian-column
   law and the new independent-entry law are the same actual matrix law.
5. The existing small-ball and Hermitization-counting proofs in
   `BC12/GinibreNegativeMoments.lean` yield negative-moment tightness with
   the concrete exponent `p = 1/128`. This is the previously agreed short
   route, not a claim to reconstruct every estimate in BC12.
6. The existing weighted-density limit, logarithmic integrability, disk
   potential, and concentration proofs now yield full logdet convergence
   from the specified Ginibre law. Both final proposition wrappers supply
   these internally proved inputs to the old assembly.

All shifts `z : ℂ` are allowed. No fixed numerical bound on `|z|` is added.

## Remaining assumptions, stated explicitly

`hGinibre` says the reference matrix has the *specified Gaussian law*.
This is a model specification, not a spectral estimate. Merely having
matching low moments would not justify applying the Gaussian identities.
There are not two unrelated Gaussian-law premises: their equivalence is
proved in `normalizedGinibreLaw_flatten`.

- Both propositions retain the explicit BBV comparison arguments for the
  actual ring and dense models, as before.
- The new Proposition 3.6 endpoint asks for the dense BBV comparison at all
  positive imaginary heights, rather than only the old local-bulk height.
  The negative-moment shortcut also uses the dense counting height. This
  is an extra specialization of the same retained comparison result,
  not an undisclosed BC12 premise.
- Proposition 3.6 retains the old theorem's real geometric Brascamp--Lieb
  premise, model/moment/density assumptions, and deterministic scale conditions.
- Proposition 3.8 retains the explicitly authorized Proposition 3.2 and
  Cook Theorem 1.12 inputs and the original subgaussian/model/scale assumptions.

No claim is made that these remaining literature premises are proved by
the Ginibre integration or by a kernel axiom audit.

## Verification and isolation

The Section 3 workflow builds the pinned Ginibre import closure serially,
then all Section 3 modules, runs a normal `lake --no-cache build`, and checks
exact `#print axioms` reports. `BC12/VerifiedAudit.lean` includes all new
bridge theorems and both BC12-free endpoints. The audit parser rejects any
axiom outside `propext`, `Classical.choice`, and `Quot.sound`, and rejects
missing reports or Lean errors.

Only a successful workflow on the final integration commit certifies this
integration; an earlier upstream or kernel-only run is not that certificate.
No proof-checking limits are increased by the new modules. Large dependency
downloads and the full project build take place on the remote runner.

The proof changes are confined to `section3/` and its workflow. The root
dependency files also register the same pin because the root project
compiles Section 3 source directly. The Section 5 and 6 lockfiles inherit
that same pin: without those entries Lake rejects their root dependency
as absent from the manifest. No downstream proof source is changed. This does not move,
rewrite, or replace the vendored trees in later chapters. Existing downstream
conditional interfaces are preserved.
