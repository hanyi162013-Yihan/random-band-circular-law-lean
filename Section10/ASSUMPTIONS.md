# Section 10: mathematical inputs and trust boundary

The source-connection work exposed and corrected an uninhabitable upstream
density record caused by an automatically generalized `top` identifier.
See [DENSITY_SCHEMA_CORRECTION.md](DENSITY_SCHEMA_CORRECTION.md) for the
cloud-printed evidence, exact impact, correction and pending revalidation.
Older conditional axiom audits do not establish that the former density
record could be instantiated.

## Source-connected extension (awaiting cloud verification)

The new `BernoulliSection10Source.planar_density_circular_law` and
`BernoulliSection10Source.real_density_circular_law` instantiate the actual
Section 3 proofs. They expose `BBVComparisonInput`, `BC12GinibreInput`, and
real-only `RealFiniteGeometricBrascampLieb`, alongside the original density,
moment and bandwidth assumptions. BBV includes the source's canonical
Gaussian/free-transform comparison; BC12 is restricted to literal circular
Ginibre. No `Section3Inputs`, high-band, model, LSV or counting certificate
is a public argument. This is a statement of the written interfaces, not
yet a successful compilation claim. See `BernoulliSection10Source/AxiomAudit.lean`.

The remainder of this document records the previously verified real
conditional endpoint and must not be read as saying that Section 3's BBV,
BC12 or geometric Brascamp--Lieb inputs have themselves been eliminated.

## Previously verified conditional real endpoint

The final entry point is
`BernoulliSection10.density_circular_law` in
`BernoulliSection10/DensityCircularLaw.lean`. Its verification status is
recorded in `AUDIT.md`; the list below describes its explicit statement,
not a substitute for the compilation and axiom audit.

## Model assumptions retained by the final theorem

1. `μ : Measure ℝ` is a probability law with mean zero, second moment one,
   and density bounded by `L`. These are the fields of
   `IsBoundedDensityAtom μ L`; density is expressed as domination by
   `L` times Lebesgue measure.
2. `Integrable (fun x : ℝ => |x| ^ 3) μ` is the finite third moment.
3. `W s : ℕ → ℕ`, with `0 < W n` for every `n` and `W → ∞`.
   There are `m_n = s n + 3` block sites and `N_n = m_n W_n` scalar rows.
   The paper assumes at least four sites; this implementation also permits
   three, where the three cyclic neighbors are still distinct.
4. `Section3Inputs μ L` supplies precisely the four paper theorems listed
   below. It is an ordinary proposition-valued theorem parameter, **not a
   Lean axiom**.

The conclusion is convergence in probability against each bounded continuous
real function on `ℂ`, for the empirical eigenvalue law of the literal normalized
three-neighbor cyclic full-block matrix. A single infinite IID real sequence
is used to realize the entries. This does not impose independence between
matrices of different sizes; convergence in probability to a deterministic
law only depends on each matrix's marginal distribution.

## The four permitted inputs

All numbering refers to [arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1).
The complete Lean statements are in `BernoulliSection10/Section3Inputs.lean`.
They are specialized to the fixed real IID atom law, which is sufficient here.

| Field | Paper theorem | Retained hypotheses and supplied conclusion |
|---|---|---|
| `leastSingularValue` | Theorem 3.1 | A nonnegative doubly stochastic variance profile; maximum variance at most `C/W`; variance at least `c/W` at scalar cyclic distance at most `W`; `W ≥ N^(1/2+χ)`; `0<κ<χ/4`; fixed positive `K_z,R`. For all large dimensions, uniformly over `‖z‖≤K_z` and `t>0`, the probability of `s_min(X-zI)≤t exp(-N^(3κ)N/W)` **and** `‖X‖_HS≤R√N` is at most `D t + exp(-N^(1+κ/4))`. |
| `mesoscopicCounting` | Proposition 3.3 | Doubly stochastic variance profile, finite third moment, inverse maximum entry variance `b≥N^c`. For fixed `z,τ>0`, every interval in `[-5,5]` of length at least `b^(-1/8)N^τ` has at most `C_z N` times its length Hermitized eigenvalues, except on an event of probability at most `N^(-10)`. |
| `localBulk` | Lemma 3.4 | The same variance and moment hypotheses. On each fixed `[0,R²]`, the difference between the squared-singular-value distribution functions of the model and normalized circular Ginibre is `O_P(N^(-ζ))` for some `ζ>0`. |
| `scalarAnchor` | Proposition 3.5 | The literal scalar indicator ring with admissible weights, finite third moment, and `W≥N^(8/9+ω)`, `0<ω<1/9`, `W,N→∞`. Its normalized shifted log determinant tends in probability to the circular logarithmic potential. |

These statements do not include a full-block high-band theorem, pressure
calibration, the target ring's log limit, or its circular law. Those are the
results to be deduced. The two uses of Lemma 3.4 compare to the same canonical
Ginibre array, so its bulk term cancels. No separate Ginibre circular-law or
Ginibre log-potential-limit hypothesis is required. Section 4 theorem inputs
are permitted by the task but not needed as additional parameters here.

## Data and claims discharged internally

- The physical block entries, their independence and normalization, the
  variance profile, scalar band ellipticity, and second-moment estimates.
- The least-singular-value cutoff removal, singular-value truncation, and
  the genuine scalar-indicator comparison ensemble for Proposition 10.1.
- The anchor dimension, optimizing exterior degree, singular frames,
  decomposable reset tests, and all finite-product changes of coordinates.
- Almost-sure invertibility and integrability of the actual endpoint,
  core, past, reset, remainder, and seam objects.
- Conditional reset integration, mean stitching, simultaneous concentration,
  the remainder estimate, and the long/direct branch assembly.
- The matrix energy identity and its weak law, using only the second moment
  for that energy conclusion; no fourth moment is assumed.
- Tao–Vu replacement: imported **proved source**, with an internally proved
  dimension-sequence adapter. Its reference ensemble is an IID uniform-disk
  diagonal matrix, constructed in this library along with its spectral,
  energy, and logarithmic-potential limits. Auxiliary randomness is removed
  from the final statement.

The replacement input's provenance and the reused generic short-ring analysis
are documented in `PROVENANCE.md` and the two `vendor/` provenance files.
None is declared as an additional mathematical axiom.

## Scope boundary

The atom law is real and identically distributed. Planar-complex laws,
directional conditional-density alternatives, and heterogeneous atom laws in
the broad versions of 10.2–10.3 are not asserted here. Complex-valued matrices
and complex shifts are already included; they should not be confused with
complex-valued random atoms.

The audit allowlist is `propext`, `Classical.choice`, and `Quot.sound`.
These are Lean's standard logical foundations, not random-matrix assumptions.
An allowed axiom list alone does not certify that a theorem matches the paper:
the explicit signatures and `FORMALIZATION_MAP.md` are also part of the audit.
