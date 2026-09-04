# Section 10 formalization map

The item-by-item real proof descriptions below retain the historical
`BernoulliSection10` interface. The current final real and planar entry
points instead live in `BernoulliSection10Source` and construct those
Section 3 connections internally. Their original BBV/BC12 interface and
real-only geometric Brascamp–Lieb input passed scoped cloud run
`33719162307` at `362c47f`. The current branch also constructs the BC12
compatibility proposition internally, leaving BBV and real-only geometric
Brascamp–Lieb; these signatures and the 502 chapter reports passed at
`c4e8078`, while the whole-chapter regression is pending. See
[SOURCE_CONNECTION_AUDIT.md](SOURCE_CONNECTION_AUDIT.md) for both final
signatures and [COMPLEX_FORMALIZATION_MAP.md](COMPLEX_FORMALIZATION_MAP.md)
for the planar counterpart of every item. Historical 857-report/full-root
claims below refer only to the earlier release, not this verification run.

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

This library covers the real-IID bounded-density branch from
**Proposition 10.1 through Proposition 10.10**, the subsequent equations
**10.30–10.57**, and their assembly into **Theorem 2.10**. The final
theorem retains only the original model hypotheses and the exact permitted
Section 3 inputs; all concrete auxiliary conditions are discharged.
The clean full-release build and all 857 repository-wide axiom reports have
passed. The verified commit and detailed trust-audit record are in `AUDIT.md`.

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
| Proposition 10.1 | `density_high_band_ring_log_limit`, `SourceInputs.fullBlockHighBand_profile_log_limit` | `DensityPressureLimit.lean`, `FullBlockHighBandProfile.lean` |
| Lemma 10.2 | `lemma_10_2_rho_lintegral_le`, `lemma_10_2_resampling_integral_le_of_pos` | `AffineLog.lean` |
| Corollary 10.3 | `corollary_10_3` | `MultiAffine.lean` |
| Lemma 10.4 | `clearedStepCompound_isAffineInPhysicalRow` | `PhysicalRows.lean` |
| Lemma 10.5 | `lemma_10_5` | `RowConcentration.lean` |
| Lemma 10.6 | `oneSiteMaxHodgeEnvelope_lintegral_le_W_log_eW`, `intervalMaxHodgeEnvelope_lintegral_le_W_log_eW` (plus the control and second-moment theorems below) | `HodgeFamilyGrowth.lean`, `IntervalHodge.lean` |
| Proposition 10.7 | `proposition_10_7_periodic_seam` | `SeamProbability.lean` |
| Proposition 10.8 | `proposition_10_8_integrated_endpoint_comparison` | `PacketComparisonGrowth.lean` |
| Proposition 10.9 | `proposition_10_9` | `PacketProbability.lean` |
| Proposition 10.10 | `proposition_10_10_packet_reset` | `PacketReset.lean` |
| Equations 10.30–10.57 | See the continuation table below | Pressure, remainder, limit, and energy modules |
| Theorem 2.10, real-IID branch | `density_circular_law` | `DensityCircularLaw.lean` |

### 10.1 — Finite-third-moment high-band limit for full-block rings

- **Source:** arXiv v1 pp. 68–69; `part2_block.tex`, label
  `prop:density-block-high-band`, statement line 3361.
- **Printed assumptions:** the actual normalized cyclic full-block model,
  centered variance-one IID atoms with bounded density, finite third moment,
  `0<ω<1/9`, `W≥N^(8/9+ω)`, and `W,N→∞`.
- **Lean statement:** `density_high_band_ring_log_limit` gives the same
  normalized log-determinant limit for the literal finite physical-row laws.
  Its only extra theorem parameter is `Section3Inputs μ L`, the explicitly
  permitted statements of 3.1, 3.3, 3.4, and 3.5; see `ASSUMPTIONS.md`.
  `N=(s+3)W`, so `N→∞` follows from `W→∞` and is not a missing premise.
- **Modules and dependencies:** `PhysicalProfile`, `ScalarBandGeometry`,
  `ScalarReferenceProfile`, `VarianceProfiles`, `ProfileMoments`,
  `CutoffRemoval`, `Section3HardEdge`, `Section3Counting`, `Section3Bulk`,
  `ReferenceTruncation`, `FullBlockHighBandProfile`, and `PhysicalInputLaw`.
- **Proof representation:** both variance profiles and scalar band lower
  bounds are computed from their entries. The 3.1 Hilbert–Schmidt cutoff is
  removed using the actual normalized energy expectation. A deterministic
  cutoff `min(1,N^(τ−β/8))` is used in place of the paper's profile-specific
  cutoff; it eventually exceeds the counting threshold, and its hard-edge
  error still tends to zero. Two applications of 3.4 cancel the same
  Ginibre reference. The comparison model is the genuine scalar-indicator
  ring of width `floor((N−1)/2)`, whose full-log limit is precisely 3.5.
  Thus no separate Ginibre log-limit or negative-moment theorem is assumed.
- **Status:** **complete (real i.i.d.)**. No full-block high-band,
  integrability, variance-profile, or reference-model certificate remains.

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

## Continuation: equations 10.30–10.57 and the final circular law

The following rows are proved in the real-IID scope. The complete public
proof chain has passed the clean release-root build and fresh axiom audits;
the exact verification record is maintained in `AUDIT.md`.

Common notation: real IID law `μ`, mean zero, second moment one, density
bounded by `L`; fixed `z : ℂ`; `W ≥ 1`; `m=s+3` block sites; dimension
`N=mW`. The paper assumes `m≥4`; the implementation also allows `m=3`.
Third-moment integrability and the exact Section 3 inputs are used only in
the high-band limit and the subsequent results which depend on that limit.

| Source item | Original hypotheses / conclusion | Lean representation and dependencies | Status |
|---|---|---|---|
| Proposition 10.1 | Finite third moment, `0<ω<1/9`, `W≥N^(8/9+ω)`, `W,N→∞`; normalized log determinant tends to circular potential | `density_high_band_ring_log_limit` on literal finite row laws; `SourceInputs.fullBlockHighBand_profile_log_limit`, `VarianceProfiles`, `Section3HardEdge`, `Section3Counting`, `Section3Bulk`, `ReferenceTruncation` | Proved |
| 10.30 | `s_W=ceil(W^(1/200))`, `c_W=s_W+3`, `ell_W=c_W W` | Literal `densityCoreSites`, `densityCellSites`, `densityAnchorSize`; lower/upper power bounds in `AsymptoticScales` | Proved |
| 10.31 | Actual chronological cleared exterior product over `s_W` sites; finite mean | `densityCorePressure`, `densityMaxCorePressure`, `intervalDegreeLog_integrable`; `ConcretePressure` | Proved |
| 10.32 | The actual anchor ring of size `ell_W`; third-moment high-band input | `DensityPressureLimit` applies `fullBlockHighBand_profile_log_limit` at `ω=1/20`, with `eventually_density_anchor_highBand` and exact law transport | Proved |
| 10.33 | Anchor log determinant differs from maximum core mean by `O_L1(W log(eW)+sqrt(W ell_W)log(eW))` | `cyclicPressure_L1_bound`, `cyclicPressure_normalized_L1_bound`; actual joint terminal packet and outside coordinates, no seam certificate | Proved |
| 10.34 | Divide the preceding error by `ell_W`; both displayed power-log terms vanish | `densityCore_fluctuation_div_anchor_le`, `tendsto_densityAnchor_seam_scale`, `tendsto_densityAnchor_fluctuation_scale`, `tendsto_cyclicAnchorPressureError` | Proved |
| 10.35 | Deterministic maximum mean divided by `ell_W` tends to circular potential | `densityCorePressureDensity_limit`; `PressureCalibration` discharges deterministic calibration, `DensityPressureLimit` supplies the concrete anchor internally | Proved |
| 10.36 | Choose the least maximizing exterior degree | `densityOptimizingDegree_maximizes`, `densityOptimizingDegree_minimal`; exact minimum of the finite argmax | Proved |
| 10.37 | Decomposable singular wedges give the scalar-reset lower test | `exists_cleared_exterior_product_scalar_test`, `interval_product_scalar_test_ae`; `SingularFrames`, `ExteriorSingularFrames`, `ClearedSingularTest` | Proved |
| 10.38 | Conditional/fiber lower bound across a fresh three-site reset | `resetSandwichDegreeLog_integral_bounds_ae`, lower half; proved for the actual frozen core and past operators, sufficient to integrate the mean recurrence directly | Proved |
| 10.39 | Complementary upper cell-mean estimate | Upper half of `resetSandwichDegreeLog_integral_bounds_ae`; `IntervalMeanHodge` and submultiplicativity | Proved |
| 10.40 | Lower mean bound for `K` cells at the fixed maximizing degree | `densityCorePressure_mean_stitching` plus `densityOptimizingDegree_maximizes`; a two-sided bound is proved for every degree | Proved |
| 10.41 | Upper mean bound for `K` cells, all degrees | `intervalPressure_complete_cells`, `densityCorePressure_mean_stitching`; exact independent concatenation, Fubini, and induction | Proved |
| 10.42 | Maximum whole-product log norm is `K F_*` plus the stated probability error | `stitchedPressure_L1_bound`, `stitchedPressure_markov`; stronger explicit L1 form at the same scale, using one whole-product concentration bound | Proved |
| 10.43 | Chronological remainder product on `q<c_W` sites | `intervalClearedProduct` restricted by `intervalSuffixRows`; exact factorization in `IntervalRestriction` / `IntervalConcatenation` | Proved |
| 10.44 | Simultaneous forward/inverse exterior control on the full-measure invertible event | `intervalClearedProduct_det_isUnit_ae`, `interval_remainder_log_change_le_ae`; actual summed Hodge envelope from 10.6 | Proved |
| 10.45 | Two-sided pathwise change in log operator norm after multiplying by the remainder | `matrix_logNorm_mul_bounds`, `abs_matrix_logNorm_mul_sub_le_hodgeLoss`; no probabilistic premise in the matrix inequality | Proved |
| 10.46 | Maximum over degrees changes by at most a common remainder envelope | `interval_remainder_max_change_le_ae`, `intervalRemainderMaxDifference_le_ae`; finite-maximum perturbation with no degree-count loss | Proved |
| 10.47 | Expected remainder envelope is at most `C qW log(eW)`, hence `C ell_W log(eW)` | `suffixHodgeEnvelope_integral_le`, `intervalRemainderMaxDifference_L1_bound`; exact suffix marginal | Proved |
| 10.48 | Markov probability bound for normalized remainder | `intervalRemainderMaxDifference_normalized_markov` | Proved |
| 10.49 | Normalized remainder tends to zero on the long branch | `densityRemainder_normalized_tendsto`; `tendsto_densityRemainderErrorScale` | Proved |
| 10.50 | Long-branch condition `N>W^(101/100)` | `density_long_ring_log_limit` is proved under the slightly weaker eventual non-strict inequality | Proved |
| 10.51 | Integer division of the outside arc into `K_N` complete cells and remainder `q_N` | `densityCellCount`, `densityRemainderSites_eq_sub`, `densityRemainderSites_lt`, `densityCell_partition` | Proved |
| 10.52 | Occupied-cell dimension ratio tends to one | `densityCell_dimension_ratio`, `tendsto_densityCell_dimension_ratio`; exact three-site seam deficit and remainder bound | Proved |
| 10.53 | Actual long-ring normalized log determinant tends to circular potential | `density_long_ring_log_limit` on finite row laws; `density_long_profile_log_limit` on the explicit Section 3 product space | Proved |
| 10.54 | The five explicit normalized error terms vanish, with the anchor limit remaining qualitative | Literal `densityTargetErrorScale`; `cyclicStitchedPressureError_div_le`, `tendsto_cyclicStitchedPressureError_div`, `tendsto_densityTargetErrorScale`. No rate for the Section 3.5 anchor limit is asserted | Proved |
| 10.55 | Direct-branch condition `N≤W^(101/100)` | `densityDirectCondition`, `density_direct_highBand` | Proved |
| 10.56 | Direct-branch log limit and closure for every `W→∞` sequence | `densityDirectAuxSites_highBand`, `density_profile_log_limit`, `density_ring_log_limit`; pointwise branch selection covers oscillating sequences as well | Proved |
| 10.57 | Actual normalized Hilbert–Schmidt square is the average of `3WN` atom squares and tends to one; only second moment one | `densityCyclicMatrix_normalized_energy`, `density_ring_energy_limit_of_second_moment`; `PhysicalAtomEnergy`, `FiniteIIDLawOfLargeNumbers`, `DensityEnergyLimit` | Proved |
| Theorem 2.10, real IID density branch | Original model assumptions, finite third moment, `W→∞`; circular empirical spectral limit | `density_circular_law`, for every real bounded continuous test function, on the actual real-IID infinite-sequence realization. Only `IsBoundedDensityAtom`, third moment, exact `Section3Inputs`, and dimensions remain | Proved |

### Representation qualifications, not additional mathematical inputs

- Independent physical coordinates are identified with square-array and
  infinite-IID realizations by explicit measure-preserving maps. A single
  probability space is a realization choice, not an independence condition
  between different matrix sizes.
- The mean-stitching proof freezes core and past, chooses singular frames
  pointwise, and integrates the measurable operator-norm statistic. This
  proves the required recurrence without assuming a measurable frame-selection
  theorem or accepting a frame certificate from the caller.
- Tao–Vu is proved code. A diagonal IID uniform-disk comparison ensemble,
  its logarithmic potential, energy, and spectral limit are constructed
  internally; its auxiliary sample is removed from the conclusion.
- The circular-law conclusion is formulated through all bounded continuous
  real test functions (weak convergence in probability), not merely compactly
  supported tests. The compact cutoff controlling escape of mass is proved.
- The planar-complex/directional atom extensions and heterogeneous-law
  generality of local 10.2–10.3 remain outside the agreed real-IID branch.

## Not covered by this chapter library

- Planar-complex and directional conditional-density atom laws.
- The heterogeneous independent-law generality of local 10.2–10.3.
- Other chapters' final theorems, except for the proved dependencies or
  exact Section 3 statements explicitly documented here.

There is no remaining pressure, seam, reset, remainder, comparison-ensemble,
energy, or replacement-principle assumption in `density_circular_law`.
The theorem is conditional on the permitted Section 3 statements and the
paper's original real-IID model hypotheses; it does not assert an
assumption-free proof of those Section 3 statements.

The fixed-outside-data form of the earlier 10.7 API is supplemented by the
actual random outside construction and integration in `PhysicalSeam` and
`CyclicSeamAssembly`. The unitary-frame form of 10.10 is instantiated using
singular frames in `ClearedSingularTest` and `ConditionalReset`. These are
proved concrete applications, not remaining mathematical gaps.

## Verification and explicit assumptions

See `AUDIT.md` for build and axiom-check records, and `ASSUMPTIONS.md` for
the exact final trust boundary. `CompletionAxiomAudit.lean` checks the full
explicit types of the principal endpoints as well as their transitive axioms.
Equivalent coordinate realizations, explicit constants, and test-function
formulations are not counted as proof omissions.
