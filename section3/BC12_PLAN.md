# BC12: exact-formula route and remaining target

This document records the **historical conditional route**. The new
entry-to-spectrum integration and BC12-free Proposition 3.6/3.8 endpoints
are documented in [BC12_INTEGRATION.md](BC12_INTEGRATION.md). In particular,
the finite formulas are no longer assumptions of those new endpoints.

The two BC12 inputs can be developed independently of Proposition 3.6.
The current implementation takes the user-authorized route of treating
exact finite-dimensional Ginibre formulas as explicit hypotheses.  It does
not derive those formulas from Gaussian matrix entries or a Schur Jacobian.

Primary source: Charles Bordenave and Djalil Chafaï, *Around the circular
law*, Probability Surveys 9 (2012), 1--89,
[published text](https://emis.de/ft/46860).

## 1. Implemented logarithmic-determinant route

The matrix-facing result is
`BC12.ginibre_matrix_logdet_convergesInProbability_of_formulas`.  For an
arbitrary positive dimension sequence tending to infinity and **every
fixed complex `z`**, it proves

```text
normalizedShiftLogDet (G n sample) z -> circularLogPotential z
```

in probability, conditional on the exact formulas below.  This is precisely
the `hBC12Full` premise accepted by the Proposition 3.6 matrix assembly.
The assembly's generic public signature is retained; callers can now
discharge that premise with the new theorem.

### Exact external boundary

All random-matrix formula hypotheses for this route are in
`ShortRingAnchor/BC12/KnownFormulas.lean`:

1. `GinibreCorrelationFormulas.firstMoment`: the mean of a normalized
   eigenvalue statistic is its integral against
   `rho_n(w) = exp(-n |w|²) sum_{k<n} (n |w|²)^k/k! / pi`.
2. `GinibreCorrelationFormulas.secondMoment`: its centered second moment
   is the exact difference-square integral against `|K_n(w,v)|²/(2n²)`.
3. `GinibreProjectionIntegralFormula.weightedProjection`: the symmetric
   weighted integral of `|K_n|²` is `2n` times the corresponding integral
   against `rho_n`.

These are integrated versions of the finite correlation/projection
identities associated with BC12 Theorem 3.3.  The displayed kernel includes
the Gaussian weight and uses variance-normalized eigenvalues.  The
interfaces include the relevant finite-integrability clauses.  They have
**no convergence, tail-estimate, or inequality fields** and are not axioms.
Their validity for the actual Ginibre ensemble remains external.

### Deductions supplied internally

- From the finite exponential sum: `0 <= rho_n <= 1/pi`, a uniform Gaussian
  envelope, and pointwise convergence off the unit circle.  The circle's
  planar nullity is proved, not assumed.
- Weighted dominated convergence for unbounded Gaussian-integrable tests.
- From the two-point and projection identities: variance at most
  `2/n * integral f² rho_n`, followed by Chebyshev and probability convergence.
- Gaussian integrability of both `|log |w-z||` and its square, including
  the singularity at `w=z`; the dominating constant may depend on `z`.
- Polar integration and circle averaging identify the limiting logarithmic
  integral with the manuscript's piecewise formula (2.1).
- A characteristic-polynomial root enumeration is constructed for every
  complex matrix, with multiplicity; no factorization hypothesis is needed
  in the matrix-only theorem.
- The first-moment formula applied to a singleton proves that a fixed `z`
  is almost surely avoided by every eigenvalue.  Thus no separate
  nonsingularity hypothesis is needed to expand the logarithm of the
  determinant, despite Lean's total convention `Real.log 0 = 0`.

The earlier weak-law warning still matters: BC12 Theorem 3.5 alone does not
justify testing against an unbounded logarithm.  The square-integrability
and variance argument above supplies that missing step explicitly.

## 2. Remaining negative singular-value moment

For each fixed `z`, prove that for some `p > 0` the normalized negative
`p`-moment of the singular values of `G_M - z I` is bounded in probability.
The relevant BC12 argument is Section 4.2, equation (4.9), Lemmas 4.11--4.12,
and the summation following those estimates.  The exponent is chosen below
`min (gamma / b, 1)` in that argument.

The user-authorized shorter route is now:

1. Reuse `GinibreLSV.normalizedShiftedGinibre_leastSingularValue_lt_le`
   from the existing published Ginibre project (source snapshots in `Vendor`).
   Its nonoptimal polynomial bound suffices: after variance normalization,
   a least-value cutoff `N^(-4)` has failure probability `O(N^(-3/2))`.
2. Reuse the v3 count for normalized Ginibre (`B=N`) with cutoff `N^(-1/16)`.
   This step retains the explicit BBV comparison, but needs no intermediate
   singular-value theorem or noncentral Wishart formula.
3. Use `normalizedNegativeMoment_le_of_count` and the explicit specialization
   `normalizedNegativeMoment_one_div_128_le` in `NegativeMomentCounting.lean`.
   The elementary balance is `a ell^(-p) <= 1` for `p=1/128`.
4. Use `negativeMomentTightness_of_count_and_lower`. Bounds are needed only
   on the good events; no uniform expectation on exceptional samples is assumed.

Steps 3--4 are new internal deductions. Steps 1--2 still need the distribution
and matrix adapters to the main theorem. Source snapshots alone do not
remove the existing `hBC12Negative` parameter from its public signature.

The Gaussian specialization avoids the general-atom inverse
Littlewood--Offord machinery.  The logarithm-versus-power estimates and
conversion to the lower logarithmic tail in formula (3.14) already exist in
`GinibreLowerEdge.lean`.

The new `BC12.negativeMomentTightness_of_uniform_integral_bound` proves the
Markov-to-tightness step once a uniform integrable negative-moment estimate
is available.  It **does not prove that estimate, choose a positive
exponent, or eliminate the negative-moment BC12 premise**.

An alternative exact-density route must use the singular values of
`G-zI`, not the Ginibre eigenvalues or the **unshifted** Laguerre density.
For nonzero arbitrary `z`, the required noncentral singular-value formulas
and their hard-edge estimates are substantially more involved.  No such
formula is silently substituted in this project. The shortest next task
is to finish the local port of the already located Ginibre source and
connect its shifted Gaussian law and the v3 count to the new tightness adapter.

## Integration cautions

- `normalizedDenseMatrixProcess` only divides arbitrary entries by
  `sqrt M`; it does **not** assert a Gaussian distribution.
- `DenseAtomMomentCopies21` supplies marginal moment facts, not Gaussianity
  or independence.  These facts alone cannot imply the BC12 inputs.
- The new logdet theorem explicitly asks for the exact formulas on the
  matrix eigenvalue statistics.  An unconditional-from-entries theorem
  still needs an actual Gaussian law and a derivation of those formulas.
- BC12 uses the negative-logarithmic-potential convention.  This project's
  `circularLogPotential` has the opposite sign: `(abs(z)^2 - 1)/2` inside
  the unit disk and `log abs(z)` outside it.
- Keep `z` arbitrary and fixed; constants may depend on `z`.  Uniformity in
  `z` is not required by the current target.

## New source files

All paths below are relative to `ShortRingAnchor/BC12/`:

- `GinibreKernel.lean`: explicit finite density and uniform bounds.
- `GinibreDensityLimit.lean`: exponential-sum estimates and density limit.
- `WeightedDensityConvergence.lean`: Gaussian-weighted convergence.
- `ScalarConcentration.lean`: Chebyshev and moment-to-tightness deductions.
- `KnownFormulas.lean`: the centralized external exact-formula boundary.
- `CorrelationConvergence.lean`: variance estimate and general statistic limit.
- `LogIntegrability.lean`: arbitrary-shift absolute/squared-log integrability.
- `PolarAverage.lean`: integrable polar lift and radial circle-average formula.
- `DiskPotential.lean`: explicit circular logarithmic potential.
- `EigenvalueLogdet.lean`: root enumeration, fixed-point avoidance, determinant bridge.
- `LogdetConvergence.lean`: the final conditional BC12 logdet theorems.

The root import, main README, and `ShortRingAnchor/Audit.lean` are updated
to include and document these modules.  No manuscript was modified and no
cache was deleted.  Additional required mathlib modules were compiled
locally, without downloading a replacement mathlib cache.
