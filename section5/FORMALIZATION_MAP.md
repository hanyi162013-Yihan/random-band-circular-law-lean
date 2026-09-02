# Sections 5--6 formalization map

## Current Section 5 extension — integrated and extended checks passed

The current source-to-theorem and trust-boundary table is
[SECTION5_COVERAGE.md](SECTION5_COVERAGE.md). The older status descriptions below
are preserved as a historical interface catalogue, not as current missing-work
claims. In particular, this extension supplies the real original-sample pipeline,
the polynomial taper branch, exact complementary exterior norm equality, actual
forward/inverse logarithmic costs, interval-uniform calibration, all-cell-count
pressure lifting, and bounded-continuous test conclusions.

`OriginalRealFullEndpoints` accepts Section 3/4 preinputs on original real arrays;
`SourceRealFullEndpoints` additionally reuses the existing Assumption 2.1 record
and derives the moment obligations needed by Section 5. No planar density is
required for real atoms. Complex and real taper endpoints derive constants from
the actual profile with a width-dependent lower weight. The comparison disk
ensemble is proved locally, not a new convergence premise.

The remaining accepted mathematical preinputs are the displayed Section 3 short
anchors, finite quantitative Section 4 estimates, and the model assumptions.
The compiled `TaperShortRingSource` constructs an actual taper short-ring
conclusion from the named Section 3 least-singular-value, counting, local
comparison and existing dense-reference inputs. Its elementary moments and
actual cutoff are derived internally. The main endpoints retain the short-anchor
packaging; Section 3's analytic estimates are not claimed to be re-proved here.
Section 6 remains deferred. The root build passed with 4079 jobs; all 65 new
modules passed strict re-elaboration. The exhaustive audit passed for 1561 public
declarations (1215 theorems), and all 15 boundary regressions passed. The extra
whole-prefix kernel replay passed with exact coverage of all 118 Section 5
modules. The final clean audit phase and cached integrated rebuild also passed;
the current coverage table records the logs and verified boundaries.

The later upstream inspection also located the existing high-band LSV project
for the manuscript's Theorem 3.1. See [UPSTREAM_INPUTS.md](UPSTREAM_INPUTS.md) for
its exact scope and the remaining model/norm/measure adapter boundary. Statements
below about not finding that project describe the earlier audit only.

## Historical updates and original interface catalogue

## 2026-09-02: Section 5 disk-reference circular-law endpoint (verified)

The new `Section5.LiteralCircularLaw` endpoint has the actual circular-area
integral as its limit, for continuous compactly supported real tests.  It no
longer stops at an ESD difference or requests any comparison ensemble theorem.

`DiskReferenceLaw` reuses the locally proved `ShortRingAnchor.BC12` disk-potential
integral, proves the normalized disk probability law, and applies the IID strong
law. `DiagonalDiskReference` proves diagonal spectral identification, expected
energy at most one, the log-potential limit, and the ESD limit.  There are no
random-matrix convergence hypotheses in these reference-ensemble theorems.
`CircularLawFromPotential` uses an independent product space for replacement and
then removes the auxiliary factor from the conclusion.

`literalShortLogPotential` masks the long branch with the deterministic target:
the Section 3 target-size input does NOT assert convergence of the entire actual
matrix sequence. `complex_literal_indicator_circularLaw_of_section34` receives
two finite Section 4 pressure estimates, constructs the ledger itself, invokes
the pressure proof, and removes the original finite-prefix matrix filler.

This closes the comparison-ensemble / actual-limit boundary for the complex
indicator branch, conditional on the accepted Section 3/4 inputs and displayed
model/geometry assumptions. It does not finish the complete real-atom pipeline,
the tapered-profile corollary, or the exact complementary-degree norm equality.
Section 6 work is deferred. Older descriptions of comparison-limit premises
below refer to the older generic endpoints, not this new entry point.

Verification: all four new modules (638 Lean lines) compiled without new-module
warnings; the full build passed (3975 jobs including cache hits). The strict
144-entry axiom audit passed, including the concrete finite-input endpoint:
only `propext`, `Classical.choice`, and `Quot.sound` occur. No dependencies were
downloaded or copied. The final local build cache is about 266 MB, approximately
31 MB above the previous 235 MB snapshot. Ordinary theorem hypotheses remain
exactly the explicit trust boundary described above; an axiom audit does not
discharge them.

## 2026-09-02: complementary inverse bound and literal model identification

`CompanionInverseNorm` proves the inverse-companion reversal identity and the
degree-uniform cleared inverse bound, including degrees zero and the top degree.
`LiteralComplementaryInverse` specializes it to the weighted physical row and
derives the former Section 4 inverse premise and almost-sure invertibility from
the actual atom marginals. `LiteralTerminalPressure` proves the one-row and finite
terminal costs for genuine IID open-product expectations.

`Section6.LiteralModelIdentification` selects the calibration rows from the first
`m` physical rows and identifies the full-size selection with the actual Section 4
suffix. It proves the IID restriction law and mean-pressure identity. Its finite
ledger constructor derives cells, terminal endpoints, and increments from two
completed Section 4 pressure inputs. The actual-band replacement endpoint supplies
the model/observable identification and the band-model energy bound internally.

All four new modules (789 Lean lines) have compiled without new warnings. The full
umbrella build succeeded (3912 jobs including cache hits). The strict 131-entry axiom
audit passed, using only `propext`, `Classical.choice`, and `Quot.sound`; the inverse
bound, literal ledger, replacement endpoint, and filler removal are included. No
dependencies were downloaded or copied; the local build cache grew by about 13 MB.
Section 3 anchors,
the two Section 4 finite pressure inputs, geometric/growth conditions, and the
comparison ensemble's own limit remain explicit. Older boundary descriptions
below are historical where superseded by this update.

This report compares `SECTION5_INVENTORY.md`, `SECTION6_INVENTORY.md`, and the Lean
sources currently present under `outputs/CircularLawSections56/`.  At the snapshot used
for this final draft, both section umbrellas import all implementation modules and the
top-level umbrella imports both sections.

All unqualified Lean names below live in either
`CircularLawSections56.Section5` or `CircularLawSections56.Section6`, as indicated by
the table in which they occur.

## 1. Status vocabulary and trust boundary

### Latest boundary update

The current user-authorized convention treats completed Section 4 as an explicit
finite preinput, alongside the already accepted Section 3 anchors. The new entry
`replacement_of_completedSection4` constructs the Section 5 certificate rather than
requesting one. `LiteralFreshMeanBound` proves the missing fresh-cell mean;
`Section4CompletedInverse` derives row moments, telescoping, finite maxima and the
balanced normalized remainder from the named complementary-inverse bound.
`Section4CompletedAssembly` proves every physical receiver normalization/rate field;
`CompletedSection4UniformInputs` supplies one constant, literal cell bounds and actual
matrix-path increments. No new axioms or final-convergence premises are introduced.

Concrete restrictions, terminal-path endpoint identifications and a.e.-spectral
parameter input assembly still have to be instantiated for a fully specified model.
The comparison ensemble's own limit and Section 6 direct/cutoff estimates remain
external. This is conditional closure, not an unconditional manuscript theorem.

The previous six-module update (historical boundary table) was:

| Boundary | New proved layer | Still explicit |
|---|---|---|
| inverse-row | `MatrixInverseRowCost`: actual matrix comparison, four-term log cost, expectation and finite-row telescope; `LiteralRowLogMoments`: actual positive row-log and weighted endpoint negative-log moments | complementary-degree inverse-norm upper bound and physical terminal-row sequence assembly |
| uniform constants | `UniformPaperConstants`: cardinalities, projective/determinant coefficient losses, fresh positive/negative losses, fiber variance; one fixed constant controls raw `W log(eW)` and fiber `log²(eW)` | actual fresh-cell mean contribution to `cellError` and complete receiver sequence/rate instantiation |
| replacement/model | `PhysicalReplacementBridge`, `TriangularReplacement`, `LiteralIndicatorModel`: actual band matrix, normalized HS expectation `≤1`, finite-prefix filler, canonical coupling, exact normalization, Markov tightness and actual ESD replacement | Section 3/a.e.-spectral-parameter certificates and the comparison ensemble's concrete log-potential / ESD limit |

`TaoVuReplacement.ReplacementPrinciple` is compiled from an existing local source
tree with shared cached mathlib. Its theorem is no longer an assumed implication in
the new matrix endpoint. Older scalar wrappers remain unchanged for compatibility;
their `hReplacement` parameters are not the new endpoint's trust boundary.
The full manuscript theorem is still not claimed to be unconditional/end-to-end.
The updated full build passed (3903 jobs including cache hits); the strict axiom
audit checked 102 declarations and found only `propext`, `Classical.choice`, and
`Quot.sound`. There were no new-module warnings and no placeholder proofs.

The status labels are intentionally strict.

- **proved locally**: the displayed Lean implication or deterministic calculation has a
  proof in this project.  If the theorem accepts a substantive paper estimate as a
  hypothesis, only the implication from that hypothesis is locally proved.
- **explicit Section3 preinput**: a high-band/short-ring statement from Section 3 is an
  ordinary theorem hypothesis.  The current project does not prove it.
- **Section4-derived literal adapter**: the declaration imports proved local Section 4
  APIs and establishes the stated literal expression, measure transport, integrability,
  or finite-cell implication.  This label does not mean that its hypotheses have already
  been assembled into the physical `W,N` sequence consumed by `NearEndToEnd.lean`.
- **external RMT/analytic input**: a cited random-matrix theorem or a nontrivial analytic
  result is supplied as an ordinary hypothesis.  Applying such a hypothesis is locally
  proved; the hypothesis itself is not.
- **not yet formalized**: no current declaration proves even the required project-level
  adapter or implication.

Consequently, declarations such as `indicator_circularLaw_of_branchwise_errors`,
`compact_gaussian_core`, and `gaussian_profile_circularLaw_of_replacement` are honest
conditional closure theorems.  They must not be cited as completed formalizations of
`thm:indicator`, `prop:compact-gaussian-core`, or `thm:gaussian-profile` without also
listing their hypotheses.

The integration run reported for this snapshot completed
`lake build CircularLawSections56`.  In addition, `AxiomAudit.lean` prints the logical
dependencies of representative theorems from every layer; its output contains only the
standard Lean/mathlib principles `propext`, `Classical.choice`, and `Quot.sound`, with no
project-defined axiom.  This trust audit concerns the proofs of the conditional
implications themselves.  It does not turn any explicit theorem hypothesis into a
locally proved matrix, probability, or RMT input.

## 2. Section 5 named statements

| Paper statement | Actual Lean declarations | Classification | Exact boundary |
|---|---|---|---|
| `lem:inverse-row` | `pathwise_remainder_log_inequality`; `pathwise_remainder_log_of_inverse_identity`; `pathwise_remainder_log_telescope`; `uniform_step_cost_telescope`; `mean_pressure_remainder_of_one_row_cost` | **proved locally**, scalar consequence only; Section4-targeted explicit invertibility/determinant input; remaining matrix identity **not yet formalized** | The positive-real log comparison and finite telescope are proved.  The exterior compound inverse identity, equality of operator norms in complementary degree, and the expected `O(log(eW))` row cost are not proved.  `hinverseIdentity` is explicitly passed to the wrapper. |
| `thm:indicator` | fixed-space declarations `indicator_logPotential_tendstoInMeasure_of_section3_and_long`, `indicator_circularLaw_of_probability_inputs`; triangular-array declarations `TendstoInProbabilityTri`, `deterministic_center_tendsto_of_tri_anchor_and_two_L1_seams`, `indicator_logPotential_nearEndToEnd_tri`, `indicator_circularLaw_nearEndToEnd_tri_of_replacement`; literal adapter modules listed in Sections 3--4 below | fixed-`z` near-end conditional assembly **proved locally**; **explicit Section3 preinput**; substantial **Section4-derived literal adapters**; **external replacement input** | On varying probability spaces the project proves the abstract Markov/calibration/pressure/remainder/final-closure chain.  Literal determinant/FreshZ identities, sample and pressure transport, normalization/fillers, complex/real finite-cell telescopes, centered random `B*Q` telescope, and concrete scale limits are now local.  Physical complex `B*Q` rows, their IID flattening, and automatic product integrability are now local.  `literalNearEndToEndCertificate` assembles varying-degree finite model estimates into a final L¹ certificate and mean-pressure limit, allowing interleaved branches.  The finite seam/pressure constants, inverse-row remainder, actual observable identity, Section 3, a.e.-`z`, empirical measures, and replacement remain explicit boundaries. |
| `cor:tapered-indicator` | `taperedNormalizer`; `taperedNormalizedWeight`; `taperedNormalizedWeight_bounds`; `sum_taperedNormalizedWeight_eq_one`; `selected_product_ge_edgeLower_pow_card`; `selected_taperedNormalizedWeight_product_lower_bound` | deterministic finite normalization **proved locally**; Section 3/4 taper inputs and final corollary **not yet formalized** | The project proves transport of already-supplied raw/normalizer bounds and the selected-product loss.  It does not derive the polynomial-in-`W` bounds from the BV profile, rebuild the taper-specific Section 3/4 estimates, convert the product bound to the manuscript's exponential loss, or conclude the circular law. |

## 3. Section 5 key equations and proof steps

### 3.1 Mesoscopic calibration

| Inventory item | Actual Lean mapping | Status and missing content |
|---|---|---|
| `eq:cell-decomposition` | `literalPaperExteriorCell`; `literalPaperExteriorCellWithLeft`; `literalRandomOutsideExteriorCell`; `paperIndicatorCyclicStartExteriorCell_eq_freshClearedProduct`; `iidMatrixCellProduct_literalPaperExteriorCell_eq_openProduct`; `iidMatrixCellProduct_literalRealCell_eq_openProduct` | The reserved fresh product `Q`, actual fixed/random-outside cell `B*Q`, and arbitrary-start fresh cleared-row product are **proved locally**.  `LiteralPhysicalMesoscopicCellAdapter` also realizes each outside as `ell` IID rows and identifies `q` cells with exactly `q*(d+1+ell)` chronological open rows.  The complete ring's row split and terminal remainder still need the final model dictionary. |
| `eq:det-versus-random-pressure` | arbitrary-start determinant/FreshZ identities; `complex_literalPhysicalDeterminant_absLog_seam_withDensity`; `TwoStepL1ApproximationTri.seam*` | Determinant-to-FreshZ is **proved locally for every cyclic start**.  The complex physical start-zero wrapper now proves the actual full-flat determinant-versus-suffix-max absolute L¹ bound, including measure reassembly and target integrability.  Uniform paper constants and the common-space `W,N` sequence specialization remain to be assembled. |
| `eq:random-versus-mean-pressure` | `LiteralPressureAdapter`; `LiteralOutsidePressureBridge`; `Section4NormalizationAndFillers`; `mesoscopic_calibration_*` | Finite random maximum versus maximum of coordinate means, integrability, literal complex/real pressure bounds, start-zero outside/suffix identification, normalization, and inactive fillers are **proved locally**.  The normalized/inactive-filled receiver construction is now in `LiteralNearEndToEndAssembly`; the manuscript's physical row dictionary and finite quantitative hypotheses still need instantiation. |
| deterministic limit from convergence in probability plus concentration/`L¹` closeness | `TendstoInProbabilityTri`; `tendstoInProbabilityTri_of_L1`; `deterministic_center_tendsto_of_tri_anchor_and_close`; `deterministic_center_tendsto_of_tri_anchor_and_two_L1_seams` | The varying-space Markov and uniqueness-of-probability-limits bridges are **proved locally**.  `literalNearEndToEndCertificate` now constructs the normalized two-step receiver and deterministic mean limit from finite physical estimates, with dependent degree types and active-only branch hypotheses.  The Section 3 endpoint remains an explicit preinput. |
| `eq:mesoscopic-calibration` | `mesoscopic_calibration_error_bound`; `mesoscopic_calibration_tendsto`; `paperMesoscopicCellLength`; `paperFinalSeamRate`; `paperBalancedRemainderRate`; `paperMesoscopicScaleChoice_of_tendsto_of_eventually_longBranch` | The three-error scalar/Tendsto closure and concrete paper rates are **proved/defined locally**.  From `0<δ<γ<1/8`, `W→∞`, and eventual `W^(1+γ)<N`, the last theorem proves all three limit fields of `PaperMesoscopicScaleChoice`; no separate positivity assumptions are needed.  These growth hypotheses and the Section 3 endpoint remain explicit inputs. |

### 3.2 Global pressure lifting

| Inventory item | Actual Lean mapping | Status and missing content |
|---|---|---|
| `eq:cell-lower` | `complex_literalPaperExteriorCell_hOneLower`; `real_literalPaperExteriorCell_hOneLower`; `complex_literalPaperExteriorCellWithLeft_vector_hOneLower`; `complex_literalRandomOutsideExteriorCell_oneCellInputs`; AE matrix-cell telescope receivers | Projective lower inputs, full atom-law integration, norm-attaining adapted directions, and fixed/random-outside centered lower bounds are **proved locally** under the displayed density/profile/second-moment, measurability, AE-unit, and integrability hypotheses. |
| `eq:cell-upper` | `complex_literalPaperExteriorCell_oneCellInputs`; `real_literalPaperExteriorCell_oneCellInputs`; `complex_literalRandomOutsideExteriorCell_oneCellInputs` | Positive-half/open-pressure integrability and one-cell operator-norm upper bounds are **proved locally**.  The older fresh-only packages are centered at zero and retain raw expected fresh pressure inside `max`; the random `B*Q` theorem instead centers at `∫ log ‖B‖`. |
| `eq:pressure-lift-r` | scalar telescopes `cell_telescope_sum_bounds`, `repeated_cell_telescope_*`, `pressure_lift_degree`; fresh-only genuine products `complex_literalPaperExteriorCell_expectedLog_telescope`, `real_literalPaperExteriorCell_expectedLog_telescope`; centered `complex_literalRandomOutsideExteriorCell_expectedLog_telescope_autoUnits`; physical `complex_literalPhysicalMesoscopicCell_expectedLog_telescope` | Finite scalar, complex/real fresh-only, and random-outside centered `B*Q` chronological-product telescopes are **proved locally**.  Generic outside families still expose integrability, but the physical complex IID-row wrapper proves it automatically.  `complex_literalPhysicalPressureSequence_cell_bounds` supplies the cumulative varying-degree receiver and derives coordinate-mean identification by measure transport. |
| `eq:pressure-lift-max` | `finiteSignedMax_cell_bounds`; `max_pressure_lift`; `max_pressure_lift_of_cell_telescopes` | **proved locally** at the exact finite-degree scalar level, assuming the degreewise cell bounds.  Pressures may be signed and the normalized error is `cellError / m`. |
| `eq:global-pressure-multiples` | fixed-degree theorems `max_pressure_lift_difference_tendsto_zero`, `global_pressure_on_cell_multiples`; varying-degree eventual forms; `literalNearEndToEndCertificate` | The sequence-level implication is **proved locally**.  The literal constructor now supports dependent exterior-degree types and active-only finite estimates, derives normalized error convergence from a uniform cell bound, and fills inactive indices.  The uniform finite bound remains a model input. |

### 3.3 Remainder and target pressure

| Inventory item | Actual Lean mapping | Status and missing content |
|---|---|---|
| `eq:pathwise-remainder` | `log_sub_log_le_posLog_of_le_mul`; `pathwise_remainder_log_inequality`; `pathwise_remainder_log_of_inverse_identity` | The abstract positive-real norm consequence is **proved locally**.  A matrix-norm theorem and the complementary compound identity are absent. |
| append/remove-row pressure bound | `abs_telescope_le_sum_cost`; `pathwise_remainder_log_telescope`; `uniform_step_cost_telescope`; `mean_pressure_remainder_of_one_row_cost` | The scalar finite telescope is **proved locally**.  `lem:inverse-row` must still supply the actual per-row expected cost. |
| `eq:balanced-cell-division` | `balancedCellCount`; `balancedCellLength`; `balancedCellRemainder`; `balanced_cell_division_spec`; `balanced_cells_add_remainder` | The exact natural-number decomposition under `0 < m₀` and `2m₀ ≤ n` is **proved locally**.  Eventual scale hypotheses are not. |
| `eq:mean-pressure-remainder` | `balanced_remainder_cost_le`; `mean_pressure_remainder_of_one_row_cost`; `balanced_physical_normalized_remainder_le_paperRate` | The finite telescope, physical length ratio, denominator cancellation and normalized paper-rate bound are **proved locally**.  The actual `C log(eW)` row-cost bound remains explicit; geometry does not prove it. |
| `eq:target-mean-pressure` | `target_pressure_error_bound`; `target_pressure_tendsto`; `literalNearEndToEndCertificate` | The final inequality and Tendsto squeeze are **proved locally**.  Actual outside/lifted pressure sequences, their cumulative cell bound, and full-cell length bookkeeping are supplied by the physical adapters; model constants and the inverse-row cost still need instantiation. |

### 3.4 Final indicator closure

| Inventory item | Actual Lean mapping | Status and missing content |
|---|---|---|
| `eq:final-seam` | `final_closure_error_bound` / `final_closure_tendsto`; `TwoStepL1ApproximationTri.seam*`; determinant/FreshZ declarations in `LiteralDeterminantFreshAdapter` and `LiteralCyclicStartAdapter`; `LiteralFreshCoordinateTransport`; `Section4NormalizationAndFillers` | The real-error composition and the literal determinant/measure/normalization pieces are **proved locally**, including arbitrary cyclic start.  A final physical-sequence constructor still has to choose the actual row split and discharge its model and scale hypotheses. |
| `eq:final-pressure-fluctuation` | the same scalar declarations; `LiteralPressureAdapter`; `LiteralOutsidePressureBridge`; `Section4NormalizationAndFillers` | Random finite maximum versus maximum of expectations, required integrability transport, literal pressure bounds, suffix-law transport, normalization, and inactive fillers are **proved locally**.  Concrete asymptotic use remains conditional on the displayed `W,N` growth and paper error bounds. |
| `indicator_logdet_tendstoInProbability` | `TendstoInProbabilityTri`; `longBranch_tendstoInProbabilityTri_of_L1_seams`; `tendstoInProbabilityTri_branchSelected`; `indicator_logPotential_nearEndToEnd_tri` | A fixed-`z` abstract theorem is **proved locally** from the three high-level certificates.  `indicator_logPotential_literal_nearEndToEnd_tri` now constructs the Section 4/pressure receivers from named finite physical estimates and explicit growth assumptions; no long-branch limit is assumed.  Section 3, remaining model estimates, actual observable identification, and a.e.-`z` synchronization stay explicit. |
| `eq:HS-tightness-indicator` | `uniform_hs_square_bound_of_eq_one` | The implication “identity `=1` gives a uniform bound” is **proved locally**.  The matrix expectation identity itself and Markov tightness are not. |
| `indicator_profile_lifting` | `replacement_principle_closure`; `indicator_circularLaw_of_probability_inputs`; `indicator_circularLaw_nearEndToEnd_tri_of_replacement` | Applying a supplied implication is **proved locally**.  The new wrapper turns an assumed scalar identity `normalizedExpectedHSSquare n = 1` into a uniform bound and invokes an arbitrary supplied implication.  Matrix-level HS identity/tightness, empirical measures, a.e.-`z`, and the actual replacement principle are not formalized. |

### 3.5 Taper branch

| Inventory item | Actual Lean mapping | Status and missing content |
|---|---|---|
| `eq:tapered-discrete-bounds` | `taperedNormalizedWeight_bounds`; `sum_taperedNormalizedWeight_eq_one` | Transport from raw bounds and mass bounds is **proved locally**.  The BV/pointwise-profile argument yielding `Z_W ≍ W`, global `W^(-1-κ)` lower bounds, and inner `W⁻¹` bounds is **not yet formalized**. |
| tapered short-ring anchor | no declaration | **explicit Section3 preinput**; the inner-band adapter is not present. |
| tapered isolated-weight loss | `selected_product_ge_edgeLower_pow_card`; `selected_taperedNormalizedWeight_product_lower_bound` | The uniform finite-product lower bound is **proved locally**.  The specialization to square-root weights, cardinality `2W`, and the estimate `exp(-Cκ W log(eW))` are not assembled. |
| tapered projective/fresh-closure/operator-affine/inverse-row wrappers | no taper-specific declarations | **not yet formalized**.  Generic Section 4 components may be reused, but the deteriorating endpoint lower bound prevents direct instantiation of fixed-`c₀` paper wrappers. |
| tapered indicator profile lifting | no declaration | **not yet formalized**; it requires the preceding taper adapters and the same conditional top-level closure as `thm:indicator`. |

## 4. Audited Section 3/4 sources and current literal adapters

The earlier local Section 3 audit found the matching Lean project
`finite-moment-short-ring-anchor`.  It defines
`ShortRingAnchor.Proposition36Conclusion` using `TendstoInMeasure` and proves substantial
hard-edge, clipped-log, upper-edge, Ginibre-lower-edge, and probability-calculus
post-processing.  It does **not** contain a theorem proving that final endpoint, and no
local theorem for the manuscript's high-band LSV was found.  Consequently the fixed-space
helper in this project uses the matching `Section3ShortRingAnchorInput` as an explicit
ordinary premise.  The
related Han2410 Proposition 3.4 / Corollary 3.5 project supplies additional comparison
post-processing, with its own visible BBV theorem parameter; it does not close the
short-ring log-determinant endpoint.

`Section3ShortRingAnchorInput` belongs to the older fixed-space helper.  The near-end
assembly separately assumes `Section3IndicatorAnchorsTri` on varying finite-measure
spaces.  No current theorem transports the former interface to the latter or constructs
the literal auxiliary/target observables.

### Section 4 APIs

The following are genuine proved Section 4 APIs identified by the inventory/API audit.
Section 5 now imports and invokes them through the literal adapter modules shown in the
last column.  The remaining gap is no longer “Section 4 is not imported”; it is the final
model-specific assembly of these checked pieces into all fields of `NearEndToEnd.lean`.

| Needed paper input | Existing Section 4 declaration(s) | Current receiving interface |
|---|---|---|
| periodic determinant identity | `paperXSubZI_det_eq_clearedSignedCompoundTrace`; literal variants `paperIndicatorXSubZI_det_eq_clearedSignedCompoundTrace` and `paperIndicatorXSubZIOfReal_det_eq_clearedSignedCompoundTrace` | `LiteralDeterminantFreshAdapter` proves start-zero, and `LiteralCyclicStartAdapter` proves arbitrary-start trace rotation plus determinant/FreshZ and log-norm identities without an external split premise |
| past-dependent fresh closure | `PaperIndicatorWeights.complex_paperIndicatorFlatFreshZ_joint_absLog_condExp_withDensity`; `PaperIndicatorWeights.real_paperIndicatorFlatFreshZ_joint_absLog_condExp_withDensity` | `LiteralAdaptedCellJointAdapter`, `LiteralFreshCoordinateTransport`, and normalization wrappers transport integrability and quantitative bounds; the final physical sequence remains caller-supplied |
| projective cell lower bound | `PaperIndicatorWeights.exists_paperProjectiveFreshVector_complex_integral_log_ge_withDensity_andSecondMoment`; `PaperIndicatorWeights.exists_paperProjectiveFreshVector_real_integral_log_ge_of_intervalBound_andSecondMoment`; `condExp_past_ae_ge_of_freshIntegral_ge` | `LiteralProjectiveCellInputAdapter`, the complex/real telescope packages, and `LiteralCenteredMatrixCellAdapter` provide complete atom-law and genuine-product receivers; the centered theorem retains actual `B*Q` |
| pressure concentration / expected finite maximum | `PaperIndicatorWeights.integral_max_complex_paperIndicatorFlatOpenPressure_le_auto`; `PaperIndicatorWeights.integral_max_real_paperIndicatorFlatOpenPressure_le_auto`; generic `pressure_maximal_concentration_of_variance` | `LiteralPressureAdapter` proves max/mean identification, integrability, complex/real wrappers, and receiver transport; `LiteralOutsidePressureBridge` identifies the start-zero suffix pressure |
| companion and compound invertibility | `ae_paperIndicatorTransferMatrix_all_isUnit_complex_withDensity`; `ae_paperIndicatorTransferMatrix_all_isUnit_real_withDensity`; companion determinant declarations in `PaperCompanionInvertibility.lean` | `LiteralIidCellInvertibilityAdapter` and `LiteralRealCellPackage` transport AE invertibility to exact cell laws; the complementary-degree norm identity needed by inverse-row is still absent |
| Efron--Stein aggregation for continuous iid samples | `variance_iidMeasure_le_half_sum_raw_memLp` and its bounded/raw-coordinate variants | `hEfronStein` in `efronStein_variance_le_of_uniform_row_cost`; the exact import/adapter is not yet present |

Section 4 does not currently provide the complementary exterior operator-norm identity
needed by `lem:inverse-row`; that obligation remains open rather than a Section 4 reuse.

## 5. Section 6 named statements

| Paper statement | Actual Lean declarations | Classification | Exact boundary |
|---|---|---|---|
| `CYCLIC5.1` | `cyclicGaussianBandMatrix`; `cyclicGaussianBandMatrix_eq_zero_of_not_mem`; `cyclicGaussianBandMatrix_apply_of_mem`; `IsNormalizedCyclicWeights`; `HasPositiveDiagonalVariance`; `cyclicRowVarianceMass` | deterministic constructor and predicates **proved locally** | The cyclic entry formula and weight bookkeeping are present.  No Gaussian probability measure, independence, standard-circular law, or moment theorem is constructed. |
| `lem:compact-Gaussian-concentration` | `efronStein_variance_le_of_uniform_row_cost`; `gaussian_logdet_variance_le`; `gaussian_logdet_normalized_variance_le`; `normalized_variance_tendsto_zero_of_bound`; `deviation_probability_tendsto_zero_of_variance_to_probability` | finite-sum aggregation **proved locally**; Section4-targeted explicit input with adapter absent; Gaussian inputs **not yet formalized** | The bound follows from explicit `hEfronStein` and uniform `hRowCost`.  Cofactor nonvanishing, row-affine Gaussian log `L²`, measurability/integrability, the actual row-resampling theorem application, and Chebyshev/convergence in probability remain premises or absent. |
| `prop:compact-gaussian-core` | `deterministic_center_tendsto_of_section3_anchor`; `compactCore_raw_expectation_tendsto`; `compactCore_cutoff_expectation_tendsto`; `compact_gaussian_core`; `section5_long_l1Approximation`; `section5_long_expectation_tendsto`; `compact_gaussian_core_of_section5_finalClosure` | probability-to-center bridge, Section 5 expectation bridge, and scalar branch assembly **proved locally**; **explicit Section3 preinput** and **external RMT/analytic inputs** | Section 5's two absolute-integral bounds and mean-pressure limit now imply actual L¹ and expectation convergence assuming only AE strong measurability of the long observable.  The raw long error is constructed, including a fixed additive shift for scaling; its identification with the physical raw expectation remains explicit.  Matrix-level direct concentration, high-band cutoff comparison, block periodicization, Mirsky stability, and cutoff uniform integrability are not derived here. |
| `lem:Riemann-masses` | `normalizedCoreMass_tendsto_of_riemannSums`; `normalizedCoreTailMass_tendsto_of_riemannSums`; `rawCoreTailMass_tendsto_of_riemannSums`; radius-exhaustion theorems; finite core normalization/comparability theorems | quotient, complement, monotonicity, and finite normalization **proved locally**; BV mesh convergence is **external RMT/analytic input** | The two Riemann-sum limits are explicit hypotheses.  The centered representative enumeration, BV mesh estimate, exhaustion using `N/W → ∞`, integrable-tail estimate, and identification with `∫_{-R}^R f` are not proved. |
| `lem:radial-monotonicity` | `jensenRootExpression_mono`; `jensenRootExpression_monotoneOn`; `jensenRootExpression_one_ge_log_norm_constantTerm`; `circleMean_radial_monotone_of_eq_jensenRootExpression`; `circleMean_one_ge_log_norm_constantTerm_of_eq_jensenRootExpression` | finite root-side algebra **proved locally**; Jensen circle-average identity is **external RMT/analytic input** | The circle mean is an arbitrary real function and `hJensen` is a hypothesis.  Polynomial factorization, the circle integral formula, integrability at roots, and conversion from `p.eval 0` to the displayed root product are not formalized. |
| `thm:gaussian-profile` | `gaussian_profile_logPotential_error_bound`; `gaussian_profile_logPotential_tendsto`; `gaussian_profile_circularLaw_of_replacement`; preferred concrete-HS wrapper `gaussian_profile_circularLaw_of_uniform_hs_bound` | scalar sparse/dense closure **proved locally**; dense law and replacement are **external RMT/analytic inputs** | The theorem accepts the sparse mean/fluctuation and dense comparison as error hypotheses and applies a supplied replacement implication.  The preferred wrapper exposes a uniform normalized expected HS-square bound.  It does not formalize subsequence dichotomy, a.e.-`z` synchronization, random probability measures, empirical spectra, or either RMT branch theorem. |

## 6. Section 6 key equations and supporting identities

| Paper equation / step | Actual Lean mapping | Status and missing content |
|---|---|---|
| definitions `L₀`, `L_a` | `rawLogPotential`; `truncatedLogPotential`; zero-dimensional simp lemmas | Finite scalar definitions are **proved locally**.  They take a supplied `Fin n → ℝ`, not matrix singular values.  The raw determinant identity and a.e. nonvanishing bridge are absent. |
| `L₀ ≤ L_a` and cutoff monotonicity | `rawLogPotential_le_truncatedLogPotential_any_cutoff`; `rawLogPotential_le_truncatedLogPotential`; `truncatedLogPotential_sub_rawLogPotential`; `truncatedLogPotential_mono_cutoff` | **proved locally** for positive supplied singular values. |
| `U_cir`, `U_v` | `circularRadialPotential`; `varianceScaledRadialPotential`; branch simp lemmas | Scalar target definitions are **proved locally**.  Continuity as `v → 1` and identification with shifted-Ginibre singular laws are absent. |
| `eq:core-raw-limit` | no varying-radius/phase theorem; `compactCore_raw_expectation_tendsto` only assembles explicit branch errors; `sparse_mean_limit_of_core_mass` receives `hPotential` | **not yet formalized**.  Common-phase invariance, integrability, countable exceptional sets, fixed-radius compact-core limits, and the monotone radius sandwich are missing. |
| `eq:core-cut-limit` | `compactCore_cutoff_expectation_tendsto` | Only branchwise scalar convergence from supplied errors is **proved locally**.  Varying normalization, Mirsky comparison, and fixed-cutoff compact-core RMT estimates are **external RMT/analytic inputs** or absent. |
| `eq:varying-normalization-La` | no declaration | **not yet formalized**. |
| `eq:tail-Jensen-lower` | appears as `hLower` in `meanSqueeze_*` and `sparse_mean_limit_*` | **external RMT/analytic input** at present.  The local Jensen root lemma is insufficient without phase invariance, tail/core independence, determinant nonvanishing, and Fubini/integrability. |
| `eq:tail-Mirsky-upper` | appears as `hUpper` in the same squeeze theorems | **external RMT/analytic input**.  Mirsky/Hoffman--Wielandt and the expected Frobenius tail estimate are not proved. |
| truncated-potential/CDF identity | `cdfCutoffIntegral`; `cutoffError_nonneg_and_le_of_linear_mass`; `cutoffError_le_of_linear_cdf` accept `hCutoffIdentity` | Given the identity and a linear CDF bound, the `O(a)` calculus is **proved locally**.  The layer-cake/Tonelli identity itself is an **external analytic input**. |
| shifted-Ginibre hard edge `F(t) ≤ Ct` | accepted as `hLinear` | **external RMT/analytic input**. |
| `eq:mean-squeeze` | `meanSqueeze_error_bound`; `meanSqueeze_fourthRoot_bound`; `meanSqueeze_fourthRoot_tendsto` | The quantitative real squeeze, fourth-root optimization, and Tendsto closure are **proved locally**, conditional on lower/upper/cutoff/potential premises. |
| `eq:sparse-mean-limit` | `sparse_mean_limit_of_core_mass`; `sparse_mean_limit_of_tail_bound` | The final scalar squeeze is **proved locally**.  Core/tail RMT comparisons and potential convergence remain explicit hypotheses. |
| `eq:Gaussian-logdet-concentration` | `gaussian_logdet_normalized_variance_le`; `normalized_variance_tendsto_zero_of_bound`; `deviation_probability_tendsto_zero_of_variance_to_probability` | Normalized real inequalities are **proved locally**.  The actual variance bound depends on `hEfronStein`/`hRowCost`; the final probability theorem is passed as `hVarianceToProbability`. |
| sparse/dense full-sequence closure | `gaussian_profile_logPotential_error_bound`; `gaussian_profile_logPotential_tendsto` | A branch-selected scalar error squeeze is **proved locally**.  The subsequence dichotomy and the construction of errors from the sparse and dense matrix branches are absent. |
| replacement-principle conclusion | `gaussian_profile_circularLaw_of_replacement`; `gaussian_profile_circularLaw_of_uniform_hs_bound` | Applying the supplied implication is **proved locally**; the latter exposes the concrete uniform normalized HS-square premise.  Han2410 Theorem 4.1, the actual HS identity/tightness proof, Ginibre comparison, and empirical-measure topology are **external RMT/analytic inputs** or absent. |

## 7. Responsibilities of the current Lean files

### Section 5

| File | Current responsibility |
|---|---|
| `Section5/BalancedDivision.lean` | Exact Euclidean division into balanced cells, length bounds, remainder identity, and scalar remainder-cost comparison. |
| `Section5/BalancedPhysicalScaleAdapter.lean` | Covered-length ratio, normalized remainder rate, and exact full-cell/outside identity `b+ell=m`, retaining the analytical row cost as a premise. |
| `Section5/CalibrationAndClosure.lean` | Three-error real inequalities and ordinary `Tendsto` closures for mesoscopic calibration and the final seam/fluctuation/mean comparison. |
| `Section5/PressureLifting.lean` | Signed finite maxima, finite telescopes of supplied cell increments, degreewise pressure lift, and normalized max-pressure error. |
| `Section5/PressureAsymptotics.lean` | Sequence-level vanishing lift difference and global pressure convergence on complete cell multiples, including varying-degree forms with eventual lifting hypotheses. |
| `Section5/InverseAndRemainder.lean` | Positive logarithm, abstract multiplicative log comparison, explicit inverse-identity premise, and finite row-cost telescopes. |
| `Section5/TargetPressure.lean` | Complete-cell/full-strip/length-ratio three-error bound and its ordinary `Tendsto` squeeze. |
| `Section5/TaperedWeights.lean` | Finite taper normalizer, normalized weight bounds, total mass one, and selected-product lower bounds. |
| `Section5/IndicatorClosure.lean` | Explicitly provenance-labelled short/long scalar errors, branchwise `Tendsto`, a uniform HS bound from an assumed identity, and application of a supplied replacement implication. |
| `Section5/ProbabilityInputs.lean` | Probability-level Section 3 preinput, arbitrary short/long `TendstoInMeasure` interleaving, and a concrete-HS-bound replacement wrapper. |
| `Section5/ProbabilityBridges.lean` | Fixed-space first/second-moment Markov--Chebyshev bridges and deterministic-center reattachment. |
| `Section5/TriangularProbability.lean` | A finite-measure convergence notion, with `L¹` Markov, two-step calibration, final-seam closure, and branch selection under probability-measure instances. |
| `Section5/NearEndToEnd.lean` | Abstract fixed-`z` near-end conditional chain from supplied Section 3/4-targeted certificates through scalar varying-degree pressure, remainder, an assumed HS identity, and a supplied replacement implication. |
| `Section5/Section4NormalizationAndFillers.lean` | Divides raw two-step `L¹` bounds by a positive deterministic scale and supplies canonical zero-error inactive-branch fillers. |
| `Section5/LiteralDeterminantFreshAdapter.lean`; `Section5/LiteralCyclicStartAdapter.lean` | Cleared trace/FreshZ and determinant/log-norm identification at start zero and every cyclic start; arbitrary-start full-IID fresh-coordinate transport and telescope. |
| `Section5/LiteralFreshCoordinateTransport.lean` | Exact full-sample fresh/nonfresh measurable equivalence, marginal maps, and triangular `L¹` pullback wrappers. |
| `Section5/LiteralPressureAdapter.lean`; `Section5/LiteralOutsidePressureBridge.lean` | Finite-max/mean pressure identification, complex/real integrability and concentration wrappers, and start-zero outside/suffix open-pressure transport. |
| `Section5/LiteralAdaptedCellJointAdapter.lean` | Past-dependent centered scalar FreshZ one-cell and cumulative bounds; it intentionally does not identify the scalar cumulative quantity with a matrix product. |
| `Section5/LiteralProjectiveCellInputAdapter.lean`; `Section5/LiteralCenteredMatrixCellAdapter.lean` | Exact atom-law projective/open-pressure inputs and the paper-centered fixed-outside `B*Q` one-cell bound at base `log ‖B‖`. |
| `Section5/LiteralCenteredMesoscopicTelescope.lean` | Random-outside `B*Q` one-cell inputs and genuine finite chronological-product telescope centered at `∫ log ‖B‖`; generic actual-product integrability is explicit. |
| `Section5/LiteralPhysicalMesoscopicCellAdapter.lean` | Physical complex outside/fresh row reassembly, exact IID laws, arbitrary finite open-pressure integrability, AE units, and actual `q*(d+1+ell)` open-pressure telescope. |
| `Section5/LiteralPhysicalPressureSequence.lean` | Varying-dimensional actual pressure sequences, derived coordinate-mean identification, exact full-cell row count, and the cumulative final receiver bound. |
| `Section5/LiteralPhysicalPressureFluctuation.lean` | `MemLp 2`, coordinate means, and centered maximum transport along noninjective measure-preserving restrictions, with a literal Section 4 finite-bound corollary. |
| `Section5/LiteralAERawSeamAdapter.lean` | Absolute joint fresh-log error from AE outside positivity using fixed-family Section 4 bounds and Fubini. |
| `Section5/LiteralPhysicalDeterminantSeam.lean` | Continuous matrix/measurable raw logdet, exact full-flat sample reassembly and law, and the actual determinant-versus-suffix-max absolute L¹ seam with derived integrability. |
| `Section5/LiteralNearEndToEndAssembly.lean` | Dependent-degree, active-branch finite estimates to a final two-step L¹ certificate and mean-pressure limit; normalized cell, seam, fluctuation, remainder, and ratio limits are constructed. |
| `Section5/LiteralIidMatrixCellProductAdapter.lean`; `Section5/LiteralIidMatrixCellAEAdapter.lean` | Genuine chronological iid matrix-product telescope, automatic norm-attaining directions, and AE-invertibility receiver. |
| `Section5/LiteralIidCellInvertibilityAdapter.lean`; `Section5/LiteralGlobalIntegrabilityAdapter.lean`; `Section5/LiteralIidCellTelescopeAdapter.lean` | Exact complex cell-law AE invertibility, open-row reassembly/global integrability, and final bounded-density finite-cell telescope. |
| `Section5/LiteralRealCellPackage.lean` | Real atom-law measure transport, projective/open-pressure inputs, AE invertibility, complexified open-row reassembly, global integrability, and genuine finite-cell telescope. |
| `Section5/LiteralPressureAsymptoticClosure.lean` | Centered component-scale receivers, complete-cell/target-pressure closure, and the manuscript's concrete cell/seam/remainder rate definitions. |
| `Section5/PaperMesoscopicScaleLimits.lean` | Proves `log(eW)/W^a → 0` and constructs all three `PaperMesoscopicScaleChoice` limits from `0<δ<γ<1/8`, `W→∞`, and the eventual long-branch inequality. |
| `Section5.lean` | Public Section 5 umbrella for the scalar spine and literal adapter modules. |

### Section 6

| File | Current responsibility |
|---|---|
| `Section6/CyclicBand.lean` | Deterministic cyclic band matrix formula and normalized/positive-diagonal weight predicates. |
| `Section6/Potentials.lean` | Finite raw/truncated scalar log potentials, basic order identities, and radial circular-law target functions. |
| `Section6/ProfileMasses.lean` | Quotient/complement limits from supplied Riemann sums, radius-exhaustion algebra, finite core renormalization, and comparable normalized weights from supplied raw bounds. |
| `Section6/GaussianConcentration.lean` | Scalar Efron--Stein finite-sum aggregation, explicit normalized variance bound, squeeze to zero, and an application wrapper for a supplied variance-to-probability implication. |
| `Section6/DeterministicCentering.lean` | Probability-level Section 3 anchor plus centered concentration implies ordinary convergence of deterministic centers. |
| `Section6/CompactCoreAssembly.lean` | Direct/long branch scalar error assembly for raw and fixed-cutoff compact-core expectations. |
| `Section6/Section5LongBranchBridge.lean` | Section 5 quantitative two-step certificate to actual L¹ and expectation convergence; nonnegative vanishing long error and shifted raw/cutoff compact-core wrappers. |
| `Section6/LiteralCompactCoreBridge.lean` | Direct consumption of the literal assembly certificate, with active-only raw measurability and physical shifted expectation identification. |
| `Section6/RadialAndCutoff.lean` | Jensen root-expression monotonicity, conditional circle-mean wrappers, conditional CDF cutoff estimate, fourth-root algebra, and mean-squeeze closure. |
| `Section6/SparseMean.lean` | Joins core-mass exhaustion to the conditional fourth-root mean squeeze. |
| `Section6/GaussianProfileClosure.lean` | Final scalar sparse/dense error composition and supplied replacement implication, including a concrete uniform-HS-bound wrapper. |
| `Section6.lean` | Public Section 6 umbrella; imports all eleven current Section 6 implementation modules listed above. |
| top-level `CircularLawSections56.lean` | Imports both complete section umbrellas, so the current implementation declarations are exposed through the public entry point. |

The umbrella facts above describe the public imports; substantive new modules are
included in the project's integration and axiom audit.

## 8. Remaining matrix/probability/analytic obligations

### 8.1 Section 5 deep inputs

1. Instantiate the remaining finite physical model estimates in the literal sequence
   constructor: the raw seam/pressure bounds with uniform paper constants, the inverse-row
   remainder, and the actual observable equality.  The high-level receiver construction,
   dependent degree types, inactive fillers, and all rate limits are now local.
2. The physical complex outside/fresh row realization and chronological pressure
   telescope are proved, including all actual-product integrability and AE-unit facts.
   The actual full-flat determinant seam and noninjective pressure-restriction transport
   are also proved. A canonical common probability space is now constructed by
   `TriangularReplacement`; assembling the calibration/target row restrictions
   remains a final model-specialization obligation.
3. The complementary-degree exterior operator-norm identity and its denominator-cleared
   form.  Section 4 supplies determinant identities and invertibility, but not this norm
   equality.
4. The expected inverse-row cost still needs its complementary-norm estimate and the
   actual row-sequence assembly. Positive row-log and weighted endpoint negative-log
   moments are now proved uniformly, including the required density integrability.
5. The model-specific quantitative bounds used by the concrete scale layer: centered
   cell error `≤ C W log(eW)`, the corresponding finite-`N` seam estimate, and uniformity
   over the entire balanced-length window.  The pure real-asymptotic limits are now proved
   by `PaperMesoscopicScaleLimits`; the probabilistic/model inequalities feeding them are
   still separate obligations.
6. The Section 3 finite-moment short-ring anchor, its real/complex specializations, and
   an adapter from the existing fixed-space endpoint to the two triangular-array anchor
   fields.  These remain explicit preinputs.
7. Generic inactive-regime and finite-prefix fillers are proved, but the physical
   observable equality `hActual` and their instantiation for every final sequence remain.
8. The sufficient HS second-moment upper bound `≤1` for the actual non-aliasing band
   matrix and Markov tightness are now proved. Finite-prefix fillers and canonical
   coupling are also supplied; an exact `=1` identity is not needed by the new endpoint.
9. The taper profile structure (BV, support, pointwise power bounds), derivation of the
   discrete `W`-dependent constants, the inner-band Section 3 adapter, taper-specific
   Section 4 wrappers, and the exponential isolated-weight calculation.
10. Deriving the a.e.-`z` hypotheses from the complete original model and instantiating
    the concrete comparison ensemble remain. The new endpoint supplies the proved
    replacement principle and actual empirical spectral test-function conclusion.

### 8.2 Section 6 deep inputs

1. Construction of the circular complex Gaussian product law, row independence,
   phase invariance, tail/core independence, and all measurability/integrability facts.
2. Almost-sure cofactor nonvanishing and the one-variable complex-Gaussian affine-log
   second-moment theorem.  These are required before the local Efron--Stein sum becomes
   `lem:compact-Gaussian-concentration`.
3. The concrete Section 4 row-resampling/Efron--Stein adapter and an actual Chebyshev or
   convergence-in-probability theorem, rather than the current scalar implications.
4. BV uniform-mesh estimates, centered even/odd displacement enumeration, normalizer and
   truncated-core Riemann sums, integrable-tail exhaustion, and the global boundedness
   estimate for `f`.
5. Polynomial factorization and the analytic circle-average identity
   `avg log|r e^{iθ}-ζ| = log(max r |ζ|)`, including zero-set/integrability care.
6. The physical raw compact-core expectation identification: the Section 5 long-branch
   `L¹`/expectation interface and shifted scalar assembly are now proved.  The actual
   determinant/potential identity, measurable physical observable, and direct Section 3
   anchor plus matrix-level Gaussian concentration still need model instantiation.
7. The cutoff compact-core proof: Han2410 Theorem 3.6, block periodicization, changed-row
   count, Mirsky/Hoffman--Wielandt, block singular-value bookkeeping, uniformity over the
   mesoscopic window, and cutoff-log uniform integrability.
8. The varying-radius raw-core sandwich, common countable exceptional set, varying
   cutoff normalization, and continuity `U_v(z) → U_cir(z)` as `v → 1`.
9. Tail Jensen lower and Mirsky upper inequalities, including determinant nonvanishing,
   Fubini, phase averaging, and the expected Frobenius tail bound.
10. The truncated-potential layer-cake identity and the shifted-Ginibre linear hard-edge
    bound near `v=1`.
11. Dense-profile comparability and Han2410 Theorem 1.5, plus the sparse/dense subsequence
    dichotomy and subsequence criterion in the topology of random probability measures.
12. Han2410 Theorem 4.1 replacement principle, normalized Ginibre circular law, HS
    tightness, and the final a.e.-spectral-parameter synchronization.

## 9. Historical bottom line (superseded by the current coverage table)

The present code proves a substantial deterministic and probability closure layer:

- exact balanced division;
- signed finite-max and finite-telescope pressure algebra;
- scalar remainder and target-pressure estimates;
- taper normalization and finite-product loss;
- finite potential order identities and core-mass normalization;
- scalar Efron--Stein aggregation;
- Jensen root-expression monotonicity and hard-edge consequences after explicit analytic
  identities are supplied; and
- compact-core, sparse-mean, indicator, and Gaussian-profile scalar error squeezes.

For Section 5 it additionally proves a near-end triangular-array assembly theorem from
ordinary certificate hypotheses named for Sections 3 and 4 through the scalar
varying-degree pressure/remainder chain to a supplied replacement implication.  The
literal layer is no longer merely a future target: it imports local Section 4 and proves
arbitrary-start determinant/FreshZ identities, full-sample probability transports,
complex/real genuine matrix-cell telescopes, the random-outside centered `B*Q`
chronological-product telescope, the physical IID open-row realization with automatic
integrability, and the concrete mesoscopic scale constructor.  Literal receiver assembly
now exposes both final L¹ and deterministic mean-pressure certificates, and Section 6
consumes these to derive actual L¹/expectation convergence with a fixed scaling shift.

It does **not** yet prove the paper's three Section 5 named results or the six mapped
Section 6 named items (the labelled definition, four local declarations, and the main
theorem) end to end at the literal matrix / empirical-measure level.  The current
top-level declarations are best viewed as checked scalar/probability closure plus a
substantial literal Section 4→5 matrix adapter, with a visible list of Section 3,
inverse-row, finite physical model estimates/identifications, and concrete comparison-model
inputs. The new literal band-model endpoint calls the proved local Tao--Vu theorem;
replacement itself is no longer an assumed implication there.
