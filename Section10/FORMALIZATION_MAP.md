# Section 10 formalization map

## Scope and source alignment

The authoritative publication source is
[arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1), submitted 1 September
2026, specifically `part2_block.tex` in its source archive. Page numbers below
refer to that 89-page PDF. The chapter and theorem numbering were checked
against the rendered PDF as well as the TeX labels.

Source fingerprints (SHA-256): `part2_block.tex` is
`9ad6009606b66d6a02afbe7df56872276f98e9196ecf66522032f91de86c1fbc`;
the downloaded v1 PDF is
`c09843c706aebf8a33358d870a7c9d11d7c52926b0132605fa2ffd7eed4f512d`.
The manuscript itself is not duplicated in this source-only release.

This library covers the nine local proof chains in **10.2--10.10**:
four lemmas, one corollary, and four propositions. The high-band
Proposition 10.1 is outside this chapter library's scope.

**Coverage qualification:** the probabilistic implementation uses one
law `μ : Measure ℝ` and its finite i.i.d. products. It covers the real i.i.d.
specialization of the statements below. ArXiv v1 also allows planar-complex
and directional conditional-density alternatives; those are not implemented
here. The non-identically-distributed generality of Lemma 10.2 and Corollary
10.3 is likewise not asserted by the single-law public APIs. This document
does not equate the completed real branch with the full extended statements.

`BernoulliLinearAlgebra` is imported from the shared repository's `Section9/`
library. No local absolute dependency path is part of this release.

Status vocabulary:

- **complete (real i.i.d.)**: the stated real i.i.d. specialization is proved
  without `sorry`, `admit`, or
  a new axiom, and every auxiliary datum constructible from the paper's
  concrete packet objects is discharged; the exact conditioned-outside and
  frame-coordinate representations are recorded below;
- **partial**: a verified, substantive part is present, but the printed
  caller-facing conclusion still has an explicitly listed missing step;
- **not covered**: a mathematically substantive part of the printed result
  is absent.  Equivalent reformulations and explicit constants are not
  classified as gaps.

## Item-by-item map

All names in this index belong to the namespace `BernoulliSection10`.

| arXiv v1 item | Public entry point | Implementation module |
|---|---|---|
| Lemma 10.2 | `lemma_10_2_rho_lintegral_le`, `lemma_10_2_resampling_integral_le_of_pos` | `AffineLog.lean` |
| Corollary 10.3 | `corollary_10_3` | `MultiAffine.lean` |
| Lemma 10.4 | `clearedStepCompound_isAffineInPhysicalRow` | `PhysicalRows.lean` |
| Lemma 10.5 | `lemma_10_5` | `RowConcentration.lean` |
| Lemma 10.6 | `oneSiteMaxHodgeEnvelope_lintegral_le_W_log_eW`, `intervalMaxHodgeEnvelope_lintegral_le_W_log_eW` (plus the control and second-moment theorems below) | `HodgeFamilyGrowth.lean`, `IntervalHodge.lean` |
| Proposition 10.7 | `proposition_10_7_periodic_seam` | `SeamProbability.lean` |
| Proposition 10.8 | `proposition_10_8_integrated_endpoint_comparison` | `PacketComparisonGrowth.lean` |
| Proposition 10.9 | `proposition_10_9` | `PacketProbability.lean` |
| Proposition 10.10 | `proposition_10_10_packet_reset` | `PacketReset.lean` |

### 10.2 — Scale-free concentration of random affine logarithms

- **Source:** arXiv v1 p. 69 and pp. 78--79; `part2_block.tex` label
  `lem:dens-affine-log` (statement starts at line 3447; proof at line 4359).
- **Printed assumptions:** independent centered, variance-one atoms with
  real or planar-complex density bounded by `L`, or the directional alternative
  in Remark 2.11; a nonzero affine map
  `G(x) = v₀ + ∑ xₛvₛ` into a finite-dimensional real or complex
  normed space (complex scalar inputs require a complex space).
- **Printed conclusions:** an `L²` bound for the difference of two
  independent log norms, and an `L²` bound relative to
  `ρ² = ‖v₀‖² + ∑ ‖vₛ‖²`, both of order
  `C_L log²(e p)` and independent of scale, dimension, and center.
- **Lean representation:** `IsBoundedDensityAtom μ L` records exactly the
  density domination, probability mass, centering, and second moment.
  `affineValue` uses the canonical product measure `Measure.pi`; the final
  theorems use an explicit constant depending only on `L` and the finite
  coordinate count.  The proof is stated for finite-dimensional real normed
  spaces, including complex normed target spaces by restriction of scalars.
  Its inputs are independent copies of one real law; the additional atom-law
  alternatives in the printed statement are not claimed.
- **Modules:** `BoundedDensity.lean`, `AffineLog.lean`.
- **Dependencies:** interval small-ball bounds, Hahn--Banach norming
  functional, Markov/Chebyshev, logarithmic layer-cake integration, finite
  product Fubini.
- **Status:** **complete (real i.i.d.)**.  The scale-free `L²` integral and resampling
  bounds, integrability, and almost-everywhere nonvanishing are proved.

### 10.3 — Evaluation of a row-multiaffine coefficient tensor

- **Source:** arXiv v1 pp. 69 and 79; `part2_block.tex` label
  `cor:dens-coefficient-evaluation` (statement line 3485; proof line 4457).
- **Printed assumptions:** a nonzero complex polynomial separately affine
  in `n_grp` independent groups, each containing at most `p` atoms satisfying
  10.2.
- **Printed conclusions:**
  `E |log |P| - log ‖Coeff P‖₂| ≤ C_L n_grp log(e p)` and
  `P ≠ 0` almost surely.
- **Lean representation:** a finite dependent coefficient tensor with one
  `Option`-selected atom per group.  Its evaluation and Euclidean coefficient
  norm are defined directly; sequential evaluation makes the coefficient
  norm at one stage the `ρ` of 10.2 at the next.  The public theorem also
  supplies the almost-sure nonvanishing conclusion.
- **Modules:** `MultiAffine.lean`.
- **Dependencies:** 10.2, finite-product measure decomposition, tower/Fubini,
  Cauchy--Schwarz.
- **Status:** **complete (real i.i.d.)**.  The dependent row tensor, recursive evaluation,
  coefficient norm identity, representation theorem, one-row `L²` estimate,
  recursive Tonelli/telescoping `L¹` expectation bound, and
  almost-everywhere nonvanishing are proved.  The caller-facing
  `corollary_10_3` constructs its coefficient tensor internally and accepts
  only the printed nonzero-function assumption.  A recursive global `L²`
  estimate is neither asserted by the paper nor needed for this conclusion.

### 10.4 — Separate affinity in every physical row

- **Source:** arXiv v1 p. 70; `part2_block.tex` label
  `lem:dens-row-affinity` (statement line 3534, followed by proof).
- **Printed assumptions:** one site with blocks `B`, `D = A - zI`, and `C`;
  a degree `0 ≤ r ≤ 2W`; a physical row group containing the three
  corresponding rows.
- **Printed conclusion:** every entry of
  `(det B) ⋀^r T` is affine in each physical row group, and independent
  left/right multiplication preserves the property.
- **Lean statement:**
  `clearedStepCompound_isAffineInPhysicalRow` and
  `independent_mul_clearedStepCompound_mul_isAffineInPhysicalRow`.
  The object is the literal denominator-free `clearedStepCompound` from the
  stable base, so no assumption `det B ≠ 0` is introduced.
- **Modules:** `PhysicalRows.lean`.
- **Dependencies:** complementary minors, determinant row multilinearity,
  the concrete Cauchy--Binet/Jacobi clearing already proved in
  `BernoulliLinearAlgebra.ConcreteClearedTransfer`.
- **Status:** **complete (deterministic)**; both stated theorems are in the
  buildable root, without any restriction to real random atoms.

### 10.5 — Concentration by physical rows

- **Source:** arXiv v1 p. 71; `part2_block.tex` label
  `lem:dens-row-concentration` (statement line 3609; proof line 3627).
- **Printed assumptions:** a product of cleared exterior operators over `s`
  consecutive sites; all scalar entries have the atom law of 10.2.
- **Printed conclusions:** uniformly over `0 ≤ r ≤ 2W`,
  `Var Y_r(I) ≤ C_L sW log²(eW)` and
  `E max_r |Y_r(I)-E Y_r(I)| ≤ C_L √(W(sW)) log(eW)`.
- **Lean representation:** canonical finite product of the `sW` physical-row
  groups, coordinate replacement by `Function.update`, Efron--Stein first
  for the bounded clipping `clip T`, followed by the `L²` limit.  The
  concrete row-resampling theorem composes 10.2, 10.4, and 10.6; the finite
  degree maximum is bounded by the Euclidean sum of centered variances.
- **Modules:** `EfronStein.lean`, `MultiAffineSecondMoment.lean`,
  `HodgeIntegrability.lean`, `RowConcentration.lean`.
- **Dependencies:** 10.2, 10.4, 10.6, product-measure Efron--Stein, clipping,
  dominated `L²` convergence, Jensen/Cauchy--Schwarz.
- **Status:** **complete (real i.i.d.)**.  Exact coordinate resampling, clipping-based
  Efron--Stein, variance, and finite-degree maximum-deviation theorems are
  proved.  `intervalDegreeLog_memLp_two` constructs the
  `MemLp` input from the concrete interval product: recursive row
  multiaffinity, its coefficient tensor, a fixed nonzero identity
  configuration, and the flat/recursive product-measure equivalence are all
  discharged internally.  The caller-facing `lemma_10_5` retains only the
  printed atom-law assumptions and `W>0`; its explicit finite sums are the
  stated `C_L sW log²(eW)` and
  `C_L sqrt(W(sW)) log(eW)` bounds before harmless constant simplification.

### 10.6 — One-site integrated Hodge control

- **Source:** arXiv v1 pp. 71--72 and 79--80; `part2_block.tex` label
  `lem:dens-integrated-Hodge` (statement line 3680; proof line 4478).
- **Printed assumptions:** one site of the concrete block model at fixed
  `z`, with bounded-density, centered, variance-one entries.
- **Printed conclusions:** an explicit one-site envelope controlling every
  forward and inverse exterior degree, with first moment
  `C_{L,z} W log(eW)` and finite second moment; submultiplicativity gives the
  corresponding interval bound.
- **Lean representation:** a concrete envelope built from the three
  Hilbert--Schmidt block norms and the negative log determinants of `B` and
  `C`.  Determinant logarithms are obtained by 10.3 applied to determinant
  row groups.  The exact inverse relation is certificate-free; the core
  results are `stepTransfer_nonsing_inv`, `compound_nonsing_inv`, and
  `clearedStepCompound_inverse_norm_eq`.
- **Modules:** `IntegratedHodge.lean`, `EndpointDeterminant.lean`,
  `HodgeEnvelope.lean`, `HodgeFamily.lean`, `TensorCornerBound.lean`,
  `HodgeFamilyGrowth.lean`, `ProductMarginal.lean`, `IntervalHodge.lean`.
- **Dependencies:** 10.2--10.3, concrete complementary-minor expansion,
  Hadamard, compound submultiplicativity, exact Jacobi/Hodge theorem from the
  stable base.
- **Status:** **complete (real i.i.d.)**.  Exact nonsingular inverse, determinant modulus,
  compound inverse, and complementary-degree Frobenius-norm identities are
  proved, together with a concrete nonzero identity witness.  Recursive
  second-moment arguments prove finite `L²` for both the operator-norm
  interval logarithms used by 10.5 and the Frobenius logarithms used by the
  exact Hodge identity.  `oneSiteHodgeEnvelope` is an actual nonnegative
  random variable built from the literal three blocks: almost surely it
  simultaneously controls the sum of forward and inverse positive-log norms
  in every degree; `oneSiteHodgeEnvelope_lintegral_le` gives a finite explicit
  first-moment bound with no caller-supplied coefficient or nonvanishing
  certificate; and `oneSiteHodgeEnvelope_memLp_two` proves its finite second
  moment.  The `B` and `C` determinant losses have explicit
  `O_L(W log(eW))` bounds obtained from concrete tensor lower bounds.
  `OneSiteClearedFamily` packages every exterior degree into one dependent
  finite product with the sup norm.  Thus
  `oneSiteClearedFamily_log_deviation` invokes Corollary 10.3 only once, while
  `oneSiteMaxHodgeEnvelope` controls every forward/inverse degree by a
  maximum rather than a sum over `2W+1` degrees.  Its first moment, finite
  second moment, integrability, and almost-sure control are all proved.
  The interval layer is also constructed rather than assumed:
  `measurePreserving_pi_restrict_embedding` proves the general finite-product
  marginal theorem, `intervalSiteRestriction_measurePreserving` identifies
  every physical site with the one-site law, and `intervalHodgeEnvelope` is
  the sum of the literal one-site envelopes.  It has finite `L²` and is
  integrable; `intervalHodgeEnvelope_lintegral_le` gives the exact linear-in-`s`
  first-moment bound, while `intervalClearedProduct_hodgeLoss_le_ae` proves
  simultaneous almost-sure forward/inverse control of every degree for the
  interval product.  Thus the submultiplicative interval corollary is
  formalized with the same explicit one-site bound.  Moreover,
  `intervalMaxHodgeEnvelope` inherits the improved maximum-over-degrees
  construction, finite `L²`, integrability, exact linear-in-`s` first moment,
  and caller-facing almost-sure product control.
  The simultaneous tensor's deterministic complementary-minor estimate is
  constructed in `HodgeFamilyGrowth.lean`: zero/one-hot corners give
  normalized atom bounds, standard determinant estimates control both
  complementary and ordinary minors, and finite matrix sums give explicit
  degree and family bounds.  Consequently
  `norm_oneSiteClearedFamilyTensor_le`,
  `oneSiteClearedFamily_posLog_lintegral_le_explicit`,
  `oneSiteMaxHodgeEnvelope_lintegral_le_explicit`, and
  `intervalMaxHodgeEnvelope_lintegral_le_explicit` contain no coefficient or
  nonvanishing certificates.  The factorial/binomial expression is further
  reduced to the explicit constant `oneSiteTensorLogConstant z` in
  `posLog_norm_oneSiteClearedFamilyTensor_le_W_log_eW`; hence
  `oneSiteClearedFamily_posLog_lintegral_le_W_log_eW` proves the forward
  `C_z W log(eW)` term literally.  Finally,
  `oneSiteMaxHodgeWLogConstant L z` combines the repeated-row cost, forward
  tensor term, and both interface-determinant terms into an explicit
  `C_{L,z}` independent of `W` and the interval length.
  `oneSiteMaxHodgeEnvelope_lintegral_le_W_log_eW` and
  `intervalMaxHodgeEnvelope_lintegral_le_W_log_eW` are the caller-facing
  one-site and interval `C_{L,z} s W log(eW)` first-moment conclusions.
  Together with the almost-sure envelope control,
  integrability, and finite `L²`, these cover the real i.i.d. specialization
  of every assertion of Lemma 10.6;
  no coefficient, probability, or deterministic Hodge certificate remains.

### 10.7 — Periodic seam comparison

- **Source:** arXiv v1 p. 73; `part2_block.tex` statement line 3857,
  conclusion label `eq:dens-periodic-seam-comparison`.
- **Printed assumptions:** the three-site packet is independent of the
  outside arc; all nine packet blocks have the bounded-density atom law;
  the outside transfer is used as the boundary relation.
- **Printed conclusion:** conditional packet expectation of the absolute
  difference between `log |det(X-zI)|` and the outside exterior pressure is
  at most `C_{L,z} W log(eW)`.
- **Lean representation:** the concrete first-three-site Floquet split and
  global boundary polynomial from `BernoulliLinearAlgebra` are composed with
  10.8, 10.9, and the deterministic Gram-volume/exterior-pressure comparison.
  The Floquet sign is removed by its unit modulus, not by an assumed phase
  certificate.
- **Lean statement:** `proposition_10_7_periodic_seam`.  Its fixed outside
  inputs `c` and `R` are exactly the outside determinant scalar and outside
  transfer after conditioning on the complementary arc. The inner integral
  is over the `3W` physical rows of the seven internal packet blocks, and
  the outer integral is over the two independent endpoint blocks. The
  signature explicitly requires `c ≠ 0` and `IsUnit R.det`.
- **Modules:** `SeamComparison.lean`, `PacketTensorReverse.lean`,
  `SeamProbability.lean`.
- **Dependencies:** concrete Block Floquet identity, 10.8, 10.9, Gram volume
  versus maximal exterior operator growth.
- **Status:** **complete (real i.i.d.)**.  The normalized physical-row tensor is compared
  in both directions with the raw squarefree coefficient norm.  The reverse
  direction uses a general squarefree evaluation estimate and the fact that
  a zero/one-hot packet corner activates at most one atom in each of the
  `3W` physical rows; its logarithmic loss is therefore
  `O(W log(eW))`, not `O(W²)`.  `packetSeam_fixed_endpoints` combines this
  bridge with 10.9 and the deterministic Gram-volume/exterior-pressure
  bound.  `proposition_10_7_periodic_seam` then uses almost-sure endpoint
  invertibility and 10.8 to integrate all nine packet blocks.  The result has
  the explicit constant `packetProposition107WLogConstant L z`, independent
  of `W` and of the conditioned outside data.  The base project's concrete
  first-three-site Floquet identity identifies the evaluated boundary
  polynomial with the cyclic determinant; its sign has norm one.

### 10.8 — Polynomial coefficient to plane wedge

- **Source:** arXiv v1 pp. 73 and 80--81; `part2_block.tex` label
  `prop:dens-reset-seam` (statement line 3896; proof line 4588).
- **Printed assumptions:** invertible endpoint blocks `C_L`, `B_R`; an
  invertible boundary relation `Θ`, deterministic or independent of the
  packet.
- **Printed conclusion:** endpoint expectation of the absolute difference
  between log coefficient norm and
  `(1/2) log det(I+Θ*Θ)` is at most `C_{L,z} W log(eW)`.
- **Lean representation:** `packetBoundaryPolynomial` is the literal
  seven-block `globalBoundaryDetPolynomial`; its coefficient norm is the
  complete squarefree tensor norm from the base.  The pointwise theorem
  `packetCoefficient_log_gramVolume_pathwise` proves the stronger
  multiplicative comparison before endpoint integration, with the endpoint
  loss given explicitly by `packetEndpointComparisonConstant`.
- **Modules:** `PacketBoundary.lean`, `EndpointExteriorGrowth.lean`,
  `EndpointConditioningGrowth.lean`, `EndpointConditioningScale.lean`,
  `PacketComparisonGrowth.lean`.
- **Dependencies:** fully instantiated terminal coefficient comparison,
  chart perturbation/continuity, exact endpoint exterior conditioning, 10.6
  for integrability of endpoint loss.
- **Status:** **complete (real i.i.d.)**.  The concrete coefficient-norm/Gram-volume
  pointwise logarithmic comparison, exact three-block translation factor,
  and explicit finite matching bound are proved.  The actual normalized
  endpoint factor is packaged as one simultaneous multiaffine family over
  its `2W` physical rows.  `endpointPairRowsMeasurableEquiv` and
  `endpointPairRows_measurePreserving` identify that recursive row model
  with the literal product law of the left and right endpoint blocks.
  Corner estimates bound its canonical tensor by an explicit
  `C W log(eW)` term.  Hodge--Jacobi then expresses every inverse compound
  norm by the complementary forward compound and the determinant inverse;
  the latter is integrated using the two concrete determinant polynomials.
  `endpointExteriorConstant_log_lintegral_le_W_log_eW` combines all degrees
  into an explicit `C_L W log(eW)` bound for the exact exterior-conditioning
  constant.  The packet matching and spectral-translation losses are also
  reduced to that scale.  Finally,
  `proposition_10_8_integrated_endpoint_comparison` is the caller-facing
  endpoint expectation theorem for every fixed invertible `Theta`, retaining
  only the paper's density and boundary-invertibility assumptions.  Endpoint
  invertibility and all Hodge, coefficient, and measure-transport
  certificates are constructed internally.

### 10.9 — Conditional evaluation of the packet polynomial

- **Source:** arXiv v1 pp. 73 and 81; `part2_block.tex` label
  `prop:dens-packet-coeff-evaluation2` (statement line 3913; proof line 4679).
- **Printed assumptions:** fixed invertible `Θ` and endpoint blocks; seven
  fresh packet blocks, divided into `3W` physical row groups of at most `3W`
  atoms.
- **Printed conclusion:** conditional expected difference between the log
  evaluated packet determinant polynomial and the log coefficient norm is
  at most `C_L W log(eW)`.
- **Lean representation:** the concrete global boundary polynomial is shown
  affine in precisely the `3W` packet row groups, its nonzero coefficient
  tensor is derived from the fully instantiated pathwise lower bound, and
  10.3 is applied directly.  No nonvanishing certificate is accepted from the
  caller.
- **Modules:** `PacketMultiaffine.lean`, `PacketProbability.lean`.
- **Dependencies:** 10.3, determinant row affinity, concrete nonzero
  coefficient bound from 10.8.
- **Status:** **complete (real i.i.d.)**.  Exact packet row grouping, separate affinity,
  and concrete nonzero coefficient data are proved.  `PacketProbability`
  realizes the `3W` physical rows as a flat product law (padding the two
  `2W` endpoint row types with unused atoms), proves that the restriction of
  the nonzero complex packet polynomial to normalized real atom inputs is
  still nonzero, applies `corollary_10_3`, and transports the result back from
  recursive rows.  The caller-facing `proposition_10_9` gives both the
  expected absolute logarithmic coefficient-evaluation bound and almost-sure
  nonvanishing with only the printed endpoint and boundary invertibility
  assumptions.

### 10.10 — Fixed-degree packet reset estimate

- **Source:** arXiv v1 pp. 74 and 81--82; `part2_block.tex` statement
  line 3944 and proof line 4723; conclusion label `eq:dens-reset-L1`.
- **Printed assumptions:** a fixed exterior degree and deterministic or
  outside-measurable decomposable unit wedges `u,v`; nine packet blocks with
  the bounded-density atom law.
- **Printed conclusion:** the packet expectation of
  `log₊(1/|⟨u,Q^(r)v⟩|)` is at most `C_{L,z} W log(eW)`.
- **Lean representation:** the coefficient-volume limit is taken at the
  deterministic coefficient level.  The formal proof uses the pointwise
  multiplicative inequality extracted from the proof of 10.8, then applies
  10.3 to the scalar matrix coefficient and integrates the endpoint loss.
- **Lean statement:** `proposition_10_10_packet_reset`.
- **Modules:** `PacketBoundary.lean`, `PacketFrame.lean`,
  `PacketFrameProbability.lean`, `MultiAffineGrowth.lean`,
  `RademacherTensor.lean`, `SquarefreeRademacher.lean`,
  `PacketTensorScaling.lean`, `PacketReset.lean`.
- **Dependencies:** 10.3, 10.6, 10.8, concrete frame/large-parameter limit from
  the stable base.
- **Status:** **complete (real i.i.d.)**.  The formal inverse, literal coefficient
  expansion, frame coefficient-vector limit, exact normalized Gram-energy
  limit, coefficient-norm lower bound, scalar-polynomial nonvanishing, and
  preservation of physical-row affinity through the frame limit are all
  proved.  `exists_squarefree_rademacher_norm_le_eval` supplies, for every
  concrete squarefree scalar polynomial, a real sign assignment whose
  evaluation dominates the full Euclidean coefficient norm.  Rescaling that
  assignment to the paper's normalized physical rows gives
  `packetScalarMatrixCoefficientNorm_le_evaluationFactor_mul_tensor`, with
  an explicit `O(W log(eW))` logarithmic factor.  The pointwise endpoint
  comparison then bounds the inverse normalized tensor norm.  Finally,
  `packetScalarCoefficientTensor_posLog_inv_lintegral_le_W_log_eW` integrates
  the two endpoint blocks and `proposition_10_10_packet_reset` combines it with
  Corollary 10.3 over the `3W` packet rows.  Endpoint invertibility is derived
  almost surely from the concrete endpoint determinants.  `U`, `V`, and `s`
  are the literal unitary-frame coordinates of the paper's decomposable unit
  wedges, not proof certificates; all frame-limit, coefficient, and
  multiaffinity obligations are constructed internally.

## Source notes

The arXiv v1 proof of 10.10 explicitly uses the pointwise estimate (10.72),
exponentiates it, and then passes to the deterministic frame limit. The final
averaging step contains both the internal-block expectation and the endpoint
expectation. The Lean proof uses this pointwise estimate and this literal
iterated integral.

One small typesetting issue occurs in v1's proof of 10.5: in
`part2_block.tex` the two squared terms in the bound on `|Y-Y'|²` are missing
an intervening `+`. The Lean resampling proof uses the valid sum bound.
No manuscript file is altered by this upload.

## Not covered by this chapter library

- Proposition 10.1 (the high-band asymptotic input).
- Sections 10.4--10.6 (anchor, pressure lifting, and final asymptotic circular law).
- Planar-complex and directional conditional-density atom laws.
- The heterogeneous independent-law version of 10.2--10.3.
- An additional wrapper stated on a global random outside probability space:
  10.7 here is the uniform fixed-outside-data integral inequality, with
  explicit `c ≠ 0` and `IsUnit R.det`. Likewise 10.10 is presented in unitary
  frame coordinates, not as a new abstract exterior-algebra API.

These are explicit scope boundaries, not axioms added to the proved theorems.

## Checkpoint audit

The current build and trust status is recorded in `AUDIT.md`. The nine
real-atom proof chains are documented above. Their completion must be read
together with the atom-law and representation qualifications above, and is
not a claim that all of arXiv v1's Section 10 has been formalized.
