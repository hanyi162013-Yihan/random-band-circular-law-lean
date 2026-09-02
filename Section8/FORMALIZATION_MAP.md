# Section 8 formalization map

This is the implementation companion to `SOURCE_MAP.md`, whose fixed v1
source hashes, printed labels, line numbers, and assumptions apply here.
It maps all four numbered results and all 69 displayed equations to
existing source declarations. A mapping may be a sufficient proved-code
variant of a displayed intermediate argument; those variants are stated
explicitly. Source presence is not compilation success.

## Scope, paths, and verification

The implemented model is the cyclic matrix with independent symmetric
Rademacher entries, physical factor `1/sqrt(3W)`, `m=s+3 >= 4`, and
`N=(s+3)W`. The public results are the Rademacher specialization of
Theorem 2.8, including the stronger every-fixed-z log-potential limit.
They do not assert the result for every real subgaussian atom.

Path abbreviations in the tables are:

- `S8/`: `Section8/BernoulliSection8/`, namespace `BernoulliSection8`.
- `S10/`: `Section10/BernoulliSection10/`, usually namespace
  `BernoulliSection10`; probability helpers use its `ProbabilityLimits`
  namespace. Importing generic code from this directory does not import
  a bounded-density premise.
- `LA/`: `Section9/BernoulliLinearAlgebra/`, namespace
  `BernoulliLinearAlgebra`.
- `S9/`: `Section9/BernoulliSection9/`, namespace `BernoulliSection9`
  or a subnamespace displayed in the source.

Verification is tied to
`../normal-lake-verification.log` relative to the repository root, i.e.
the task's `work/normal-lake-verification.log`. That run uses the normal
`scripts/build_serial.py` workflow and finishes with ordinary `lake build`.
The current snapshot for this map has reached target 79 of 426; the log
explicitly records successful normal builds of `LA/AllMinors.lean`,
`S10/FinitePressure.lean`, `S10/SingularFrames.lean`, and
`S8/ClippedLog.lean`, and `S8/MesoscopicScales.lean`, among the preceding
foundational modules. `MesoscopicScales` was target 50 and completed its
normal rebuild successfully.

`P` means **written-pending-check**: at least one required declaration in
the row has not yet been observed passing this normal build. `N` means
the cited local module passed that normal build; it does not certify the
downstream Section 8 result. `D` additionally records an earlier successful
development check, which does not replace normal verification. In
particular `CellConcentration`, `CellCoordinates`, and `Section3HighBand`
have development-check evidence, but their assembly rows remain `P`
unless normal-build evidence is recorded. All four final
numbered results below remain `P`. No release-complete claim is made.

## External mathematical inputs

| Input | Exact exposed object | Boundary |
| --- | --- | --- |
| Nguyen | `S9/ExternalInputs.lean`: `NguyenBottomSingularInput`; final caller also gives `1 <= subgaussianBound` | Authorized singular-value literature input. Concrete Rademacher IID squares, interface events, constants and all global uses are constructed in code. |
| Cook | `S9/ExternalInputs.lean`: `CookDeformedSquareInput` | Authorized deformed-square singular-value literature input. Concrete normalized physical packet, seven fresh blocks, conditioning and coefficient identifications are constructed. |
| Section 3 | `S8/Section3HighBand.lean`: `Section3SubgaussianHighBandInput rademacherLaw 1` | **Proposition 3.8**, `prop:subgaussian-block-high-band`, statement `main.tex` 1146–1161, proof 1163–1245, equations (3.18)–(3.19). Its high-band hypotheses are discharged separately for the exact many-cell anchor and the direct branch. |

There is no Section 4 paper-proposition input. Previously proved generic
code can be reused regardless of its directory. Reset, pressure, seam,
reference-law, replacement, independence and measurable-selector
certificates are not final caller inputs. The input structures above
remain genuine assumptions even when the Lean axiom audit is clean.

## Four numbered results

| Printed result | Actual entry points | Implementation and dependency | Status |
| --- | --- | --- | --- |
| Lemma 8.1, `lem:gb-cell-concentration` | `S8/CellConcentration.lean`: `lemma_8_1_independent_cores`; `S8/CellCoordinates.lean`: `lemma_8_1_interval_cells` | Literal clipped-core means under the original IID law; independent cores are constructed and transported from actual chronological row coordinates. Uses proved bounded-variable subgaussian/Hoeffding inequalities and the finite degree maximum, without conditioning on good interfaces. | P, D |
| Proposition 8.2, `prop:gb-roadmap` | `S8/RademacherLogPotential.lean`: `rademacher_rows_log_potential`, `rademacher_log_potential`; `S8/Section8Results.lean`: `section8_bernoulli_log_potential` | Actual cyclic log determinant for each fixed complex z. The two branches can alternate arbitrarily. Final parameters are only Cook, Nguyen, Section 3 and the model/width hypotheses. | P |
| Lemma 8.3, equation label `eq:gb-terminal-pressure` | `S8/RademacherSeamLimit.lean`: `rademacher_cyclicSeamDifference_tendstoInProbabilityTri`, specialized to `s=anchorCells W * cellSites W`; used by `S8/RademacherLogPotential.lean`: `rademacher_anchor_pressure_comparison` | Actual anchor determinant versus the complete-cell outside product. The second theorem also combines concentration/reset stitching and subtracts the deterministic anchor pressure center. Zero Fock values are explicitly included in the seam bad event. | P |
| Corollary 8.4, equation label `eq:gb-pressure-calibration` | `S8/RademacherLogPotential.lean`: `rademacher_normalizedCorePressure_tendsto`; internal algebra in `S8/PressureCalibration.lean`: `normalizedCorePressure_tendsto_of_anchor_comparison` | The internal comparison premise is supplied by `rademacher_anchor_pressure_comparison`; Proposition 3.8 is supplied by the exact physical-row anchor transport. No pressure convergence premise is left in the public calibrated result. | P |

## Equations (8.1)–(8.22): orientation, interfaces, polynomial transfers

| Equation | Existing declarations / files | Exact use or sufficient implementation variant | Status |
| --- | --- | --- | --- |
| 8.1 | `LA/ConcreteBoundaryExterior.lean`: `boundaryPacketTransfer`, `chronologicalProduct_boundaryCompanionSteps`, `boundary_step_recurrence`; `S10/PacketPhysicalIdentification.lean`: `intervalClearedProduct_packetPhysicalRows` | Three-site transfer has the later site on the left. The physical packet is identified with the actual three normalized site rows. | P |
| 8.2 | `S10/IntervalTransfer.lean`: `intervalTransferProduct`; `S10/PhysicalModel.lean`: `reverseMatrixProduct`; `S8/CyclicTerminalIdentity.lean`: `cyclicFockValue_terminalPacket` | The outside is the chronological prefix before the final three sites. Its orientation is enforced in the actual determinant identity, not assumed as an outside certificate. | P |
| 8.3 | `LA/CyclicFloquetConcrete.lean`: `concrete_block_floquet_packet_split`; `LA/BlockFloquet.lean`: `det_one_sub_transfer_comm`; `S8/PhysicalFock.lean`: `cyclicFockValue_eq_zero_iff` | Closure is implemented by the concrete determinant identity and its zero equivalence. There is no separate theorem introducing the paper's auxiliary wavefunction notation. Interface factors are nonzero only on the good event. | P |
| 8.4 | `LA/ConcreteBoundaryExterior.lean`: `polynomialClearedBoundaryTrace_eq_detProduct_mul_compatibility_of_units`, `concreteKTheta_det_eq_boundaryCompatibility_of_units` | Literal boundary relation is realized by the concrete packet boundary matrix and its compatibility determinant. | P |
| 8.5 | `S8/CyclicTerminalIdentity.lean`: `cyclicFockValue_terminalPacket`; `S8/RademacherSeam.lean`: `cyclicSeamBadEvent_probability_le` | Actual outside transfer is substituted after product-coordinate exposure. Uniform fixed-fiber estimates are integrated over the real outside law. | P |
| 8.6 | `S8/RademacherInterface.lean`: `rademacherSiteBadEvent_probability_le`, `rademacherInterfaceBadEvent_probability_le`, `rademacherInterfaceGoodEvent_compl_probability_le` | Nguyen is the explicit input. Three concrete normalized blocks are controlled per site; fixed factors and the reduced exponential rate are retained explicitly. | P |
| 8.7 | `S8/RademacherInterface.lean`: `rademacherInterface_controls`, `rademacherSite_norm_sum_le_of_good`, `rademacherInterface_dets_isUnit_of_good` | Actual normalized block norms and determinant lower/upper bounds. The code's event also controls the unshifted diagonal block, a harmless strengthening. | P |
| 8.8 | `S8/RademacherInterface.lean`: `rademacherInterface_controls`, `rademacherInterfaceGoodEvent_spec` | Exponential inverse bounds hold on the constructed finite good event. No almost-sure invertibility is asserted for Bernoulli interfaces. | P |
| 8.9 | `S9/TerminalUniformCook.lean`: `uniformCookFailureBound`; `S8/RademacherBoundarySmallBall.lean`: `rademacherBoundaryBadProbability`; `S8/RademacherTerminalRates.lean`: `tendsto_rademacherBoundaryBadProbability_mul_logScale` | Explicit sums of `C sqrt(9 log(3W)/W)+exp(-cW/4)` and `exp(-W)`. Their product with `log(eW)` tends to zero; constants depend only on the permitted Cook input. | P |
| 8.10 | `S8/RademacherEnergy.lean`: `rademacherLaw_ae_sign`, `rademacherRows_ae_sign`; `S8/RademacherIID.lean`: `rademacherPacketFamily`; `S8/TwoSidedTerminal.lean`: `terminal_logDeviation_probability_le_parseval` | Signs are bounded by one on the actual support. The final terminal upper tail uses the proved coefficient Parseval identity and Markov, giving `exp(-2T)` directly, so a separately assumed reverse maximum-entry event is unnecessary. | P |
| 8.11 | `LA/BlockFloquet.lean`: `stepTransfer`, `stepTransfer_eq_companion`; `S10/PhysicalModel.lean`: `intervalSiteBlocks` | The physical diagonal block contains the shift `A-zI`; companion formula requires the right interface to be invertible. | P |
| 8.12 | `LA/ConcreteClearedTransfer.lean`: `clearedStepCompound`, `clearedStepCompound_eq_det_smul_compound_stepTransfer`; `S10/PhysicalModel.lean`: `intervalClearedStep` | Polynomial minor construction on every sample; agreement with `det(B) * compound(T)` is invoked only on units. It is not defined by multiplying a totalized inverse by a zero determinant. | P |
| 8.13 | `S10/IntervalTransfer.lean`: `intervalClearedProduct_eq_clearing_smul_compound`, `list_prod_smul_compound` | Actual polynomial product equals scalar clearing factor times the exterior transfer product on interface units. | P |
| 8.14 | `S10/IntervalTransfer.lean`: `intervalTransferProduct`; `LA/CyclicFloquetConcrete.lean`: `concrete_block_floquet_identity` | Chronological cyclic monodromy is fixed by the list/product order and used in the actual matrix determinant identity. | P |
| 8.15 | `LA/ConcreteClearedTransfer.lean`: `polynomialClearedSignedCompoundTrace_listOfFn_eq_physical`; `S8/PhysicalFock.lean`: `cyclicFockValue_eq_signed_det`, `norm_cyclicFockValue` | Full polynomial Fock identity, including singular interfaces. The deterministic sign has unit modulus. | P |
| 8.16 | `LA/AllMinors.lean`: `det_one_sub_eq_signedCompoundTrace`, `compound_mul` | Determinant/exterior expansion and exterior functoriality are already proved generically. | N: AllMinors; downstream P |
| 8.17 | `S8/CyclicTerminalIdentity.lean`: `cyclicFockValue_terminalPacket`; `S10/PhysicalBoundaryExpression.lean`: `packetBoundaryEval_eq_physical` | Cut polynomial equals outside clearing factor times actual terminal boundary evaluation. Fresh packet interfaces may be singular; only the exposed outside transfer is required to be defined on units. | P |
| 8.18 | `S8/RademacherTransferBounds.lean`: `oneSiteForwardMaxLoss_le_of_bounded_atoms`, `oneSiteMaxHodgeEnvelope_le_of_bounded_atoms` | Polynomial compound bounds on bounded Rademacher entries; sufficient fixed `C W log(eW)` envelope. | P |
| 8.19 | `S10/IntegratedHodge.lean`: `norm_stepTransfer_det_eq`, `stepTransfer_det_isUnit` | The determinant's absolute-value ratio is proved and is the form needed by the later bounds; the isolated sign from the printed formula is immaterial. | P |
| 8.20 | `LA/JacobiConcrete.lean`: `compound_inverse_norm_eq_of_isUnit`; `S10/IntegratedHodge.lean`: `compound_nonsing_inv` | The reusable complementary-minor norm identity is in Frobenius norm. The implementation uses it as an envelope and separately proves the required operator-norm estimates; it does not identify Frobenius and operator norms. | P |
| 8.21 | `S10/IntegratedHodge.lean`: `clearedStepCompound_inverse_norm_eq_complement`; `S8/RademacherTransferBounds.lean`: `rademacherInterval_hodgeLoss_le_of_good` | Exact complementary cleared inverse identity in the envelope norm, then the actual two-sided Hodge loss bound. This is a sufficient norm-envelope variant of the printed operator identity. | P |
| 8.22 | `S8/RademacherTransferBounds.lean`: `rademacherInterval_abs_logNorm_le_of_good`, `rademacherInterval_abs_logNorm_le_on_measurable_good`, `rademacherInterval_norm_pos_of_good` | Explicit actual L2 operator log-norm bound. `log(eW)` is used instead of `log W`; the large-width comparison is proved where clipping is chosen. | P |

## Equations (8.23)–(8.35): exact scales and independent concentration

| Equation | Existing declarations / files | Exact use or sufficient implementation variant | Status |
| --- | --- | --- | --- |
| 8.23 | `S8/MesoscopicScales.lean`: `coreSites`, `cellSites`, `cellLength`, `rpow_le_cellLength`, `cellLength_le_five_mul_rpow` | Exact ceiling exponent `1/200`, three reset sites, and physical scalar cell size. | N: MesoscopicScales |
| 8.24 | `S8/MesoscopicScales.lean`: `anchorCells`, `anchorSites`, `anchorSize`, `anchorSize_eq`, `rpow_le_anchorSize`, `anchorSize_le_thirteen_mul_rpow`, `eventually_anchor_highBand` | Exact `K_W=ceil(W^(1/200))`, `M_W=W(K_W c_W+3)`; explicit power bounds suffice for Proposition 3.8. | N: MesoscopicScales; anchor probability P |
| 8.25 | `S8/CellCoordinates.lean`: `completeCellReset`; `S8/CellResetLoss.lean`: `cellResetProducts` | Literal first-three-site restriction and its cleared product. | P; coordinates D |
| 8.26 | `S8/CellCoordinates.lean`: `completeCellCore`; `S8/CellResetLoss.lean`: `cellCoreProducts` | Literal suffix after three reset sites and its cleared product. | P; coordinates D |
| 8.27 | `S8/CellCoordinates.lean`: `completeCellProduct_split`, `intervalClearedProduct_flatten_core_reset` | Actual cell is `core * reset`, and the complete interval is the reverse chronological product of these matrices. | P, D |
| 8.28 | `S10/IntervalTransfer.lean`: `intervalTransferProduct`, `intervalClearingFactor`; `S8/RademacherInterface.lean`: `rademacherIntervalTransfer_representation_of_good` | Apply to each literal `completeCellCore`; representation and scalar nonvanishing follow on the concrete core-good event. | P |
| 8.29 | `S10/IntervalTransfer.lean`: `intervalClearedProduct_eq_clearing_smul_compound`; `S8/CellPressureSandwich.lean`: `interval_product_det_isUnit_of_good` | Cleared core representation with units established from Nguyen's actual interface event. | P |
| 8.30 | `S8/ClippedLog.lean`: `clippedLog`, `clippedLog_zero`, `abs_clippedLog_le`, `continuous_clippedLog`, `clippedLog_eq_log_of_log_bounds` | Needed symmetric clipping is implemented as `min B (log(max(exp(-B)) x))`; a zero norm is assigned `-B` exactly. | N: ClippedLog; downstream P |
| 8.31 | `S10/PhysicalModel.lean`: `intervalDegreeLog`; `S8/CellConcentration.lean`: `clippedCoreLog` | Raw `Real.log` is totalized; the probabilistic core observable clips the norm before this convention can disagree with clipping an extended logarithm. | P |
| 8.32 | `S8/CellPressureLimit.lean`: `cellClipBound`; `S8/CellPressureSandwich.lean`: `clippedCoreLog_eq_log_on_good`; `S8/CellResetRates.lean`: `rademacherCellClipConstant`, `rademacherCellClipBound_ge_budget` | Actual cap is `C ell_W log W`; the chosen constant proves clipping inactive on the actual good event for sufficiently large W. | P |
| 8.33 | `S8/CellConcentration.lean`: `clippedCorePressure`, `clippedMaxCorePressure`, `integrable_clippedCoreLog`, `integral_clippedCoreLog_eval` | Expectation under the original unconditioned IID interval law, with actual coordinate mean identities. | P, D |
| 8.34 | `S8/CellConcentration.lean`: `clippedCoreOptimizingDegree`, `clippedCoreOptimizingDegree_maximizes`, `clippedCoreOptimizingDegree_minimal` | Least maximizing degree is a deterministic function of the law, width, cap and fixed z, independent of samples. | P, D |
| 8.35 | `S8/CellConcentration.lean`: `bounded_cells_max_tail`, `lemma_8_1_independent_cores`; `S8/CellCoordinates.lean`: `completeCellsCores_measurePreserving`, `lemma_8_1_interval_cells`; `S8/CellPressureLimit.lean`: `completeCellCoreFluctuation_tendsto` | Finite degree Hoeffding bound, actual complete-cell coordinate law, then simultaneous fluctuation divided by `K ell_W`. The quantitative condition `K >= coreSites W` is explicit. | P; finite concentration/coordinates D |

## Equations (8.36)–(8.51): actual matrix-prefix resets and pressure

| Equation | Existing declarations / files | Exact use or sufficient implementation variant | Status |
| --- | --- | --- | --- |
| 8.36 | `S8/ResetTelescoping.lean`: `resetPrefixProduct`; `S8/CellResetLoss.lean`: `intervalClearedProduct_cellPastRows_eq_resetPrefixProduct` | **Variant:** telescope actual matrix-prefix norms instead of constructing the paper's recursively normalized random wedge. The prefix is an actual product, and its physical-row identity is proved. | P |
| 8.37 | `S10/ExteriorSingularFrames.lean`: `exists_top_exterior_singular_frame`; `S10/ClearedSingularTest.lean`: `exists_cleared_exterior_product_scalar_test` | Top singular frames of the frozen core and past are chosen inside a fixed-fiber proof. No global measurable frame selector is assumed. | P |
| 8.38 | `S10/SingularCoefficient.lean`: `singular_sandwich_coefficient_le`, `exists_exterior_product_scalar_test`; `S10/ClearedSingularTest.lean`: `exists_cleared_exterior_product_scalar_test` | Absolute scalar-test inequality includes both core and past norms and both complex clearing factors. It supplies the needed consequence of the source adjoint-pairing identity. | P |
| 8.39 | `S8/RademacherFrameSmallBall.lean`: `rademacherPacketFrameCoefficient`, `packetScalarCoefficientEval_eq_scaled_raw`, `rademacherPacketFrameCoefficient_parseval`, `rademacherPhysicalPacketCoefficient_capped` | Actual scalar test and normalized coefficient norm in the seven fresh Rademacher blocks. Normalization is an equality, not a generalized weighted-packet assumption. | P |
| 8.40 | `S8/RademacherEndpointInterface.lean`: `rademacherEndpointGoodEvent`, `rademacherEndpointGoodEvent_spec`, `rademacherEndpointGoodEvent_compl_probability_le` | Actual two exposed endpoint blocks. Code retains the harmless larger bound `9 exp(-cW/2)` obtained from a concrete packet good event. | P |
| 8.41 | `S10/PacketFrame.lean`: `packetScalarMatrixCoefficientNorm_bounds_and_pos`; `S8/RademacherFrameSmallBall.lean`: `rademacherPacketFrameCoefficient_lower_and_pos`; `S8/RademacherBoundaryGrowth.lean`: `neg_log_rademacherBoundaryInverseGamma_le_on_endpoint_good` | Raw frame coefficient has finite two-sided endpoint bounds. The physical lower exponential bound and positivity are packaged explicitly, which is the half needed for capped resets. No claim is made that a separate S8 theorem reproduces the unused physical upper exponential bound verbatim. | P |
| 8.42 | `S10/ClearedSingularTest.lean`: `exists_cleared_exterior_product_scalar_test`; `S8/ConditionalCappedReset.lean`: `physicalCappedResetLoss_fresh_integral_le` | **Variant:** `norm(core) * norm(past) * abs(test) <= norm(core * reset * past)`. This directly controls the actual matrix-prefix loss, including the case where the scalar test vanishes. | P |
| 8.43 | `S8/CappedReset.lean`: `cappedSpliceLoss`, `measurable_cappedSpliceLoss`, `integrable_cappedSpliceLoss`; `S8/CellResetLoss.lean`: `cellIntervalResetLoss`, `prefixResetLoss_eq_cellIntervalResetLoss` | Actual norm loss is capped and assigned the cap when any required norm is zero. It is distinct from the scalar test loss. `S8/CellResetRates.lean`: `rademacherResetCap`, `rademacherResetCap_ge_budget` make the cap sufficient on the good event. | P |
| 8.44 | `S8/ResetAveraging.lean`: `resetLossFlat`, `measurable_resetLossFlat`, `resetLossFlat_integral_le`; `S8/IntervalResetLoss.lean`: `measurable_intervalResetLoss` | **Variant:** core and past good fibers plus endpoint-good fibers are integrated separately. All measurability belongs to the actual norm-loss observable; auxiliary frame selection stays inside frozen fibers. | P |
| 8.45 | `S8/ConditionalCappedReset.lean`: `physicalCappedResetLoss_fresh_integral_le`; `S8/CappedReset.lean`: `integral_cappedSpliceLoss_le` | Uniform fixed-fiber integral bound `D + baseLoss + p_W T`. `D` is subsequently instantiated by the proved endpoint coefficient bound. This integral/Fubini form replaces explicit conditional-expectation notation. | P |
| 8.46 | `S8/ResetAveraging.lean`: `physicalCappedResetLoss_reset_integral_le`, `resetLossFlat_integral_le`; `S8/IntervalResetLoss.lean`: `intervalResetLoss_integral_le`; `S8/CellResetLoss.lean`: `cellIntervalResetLoss_integral_le` | **Variant:** mean bound retains `[9+3(p+q)] exp(-cW/2) T` for a p-site core and q-site past. This is weaker than the printed width-only exceptional term, but is bounded by the ambient site-count exponential budget and vanishes under the standing logarithmic bandwidth hypothesis. Cook's `p_W` is not multiplied by the number of cells. | P |
| 8.47 | `S8/CappedAveraging.lean`: `summed_loss_probability_le`; `S8/CellResetRates.lean`: `normalizedCellResetLoss_tendsto`; `S8/AveragedRates.lean`: `tendsto_averagedResetError` | Actual losses are summed first, then one Markov inequality is applied. Proved base, Cook-log, and ambient interface error limits supply the result at every deterministic degree, including the optimizer. | P |
| 8.48 | `S8/CellCoordinates.lean`: `intervalClearedProduct_flatten_core_reset`; `S8/ResetTelescoping.lean`: `reverseMatrixProduct_eq_resetPrefixProduct`; `S8/CellResetLoss.lean`: `intervalClearedProduct_flatten_eq_resetPrefixProduct` | Exact full chronological cell product agrees with the Nat-prefix recurrence. | P; cell coordinates D |
| 8.49 | `S8/MatrixCappedReset.lean`: `matrix_log_product_ge_sub_cappedSpliceLoss`; `S8/ResetTelescoping.lean`: `resetPrefixProduct_log_lower`; `S8/CellPressureSandwich.lean`: `complete_cell_pressure_sandwich` | Lower bound at the deterministic optimizing degree uses the actual capped prefix losses. Hodge budgets and units prove finite logs and sufficient cap on the global good event. | P |
| 8.50 | `S8/ResetTelescoping.lean`: `resetPrefixProduct_log_upper`; `S8/CellPressureSandwich.lean`: `complete_cell_pressure_sandwich` | Upper bound for every degree uses actual core logs and a three-site reset norm budget. Core clipping agrees with the raw logs on good samples. | P |
| 8.51 | `S8/CellPressureLimit.lean`: `completeCellCoreFluctuation_tendsto`; `S8/CellResetRates.lean`: `normalizedCellResetLoss_tendsto`; `S8/CompleteCellPressureLimit.lean`: `completeCellPressureError_tendsto`, `intervalCompleteCellPressureError_tendsto`, `embeddedCompleteCellPressureError_tendsto` | Unconditioned actual maximal product pressure limit, with `K >= ceil(W^(1/200))` and ambient `log(mW)/W -> 0`. Includes the probability of all interfaces being good. Does not claim that bare `K -> infinity` suffices. | P |

## Equations (8.52)–(8.69): remainder, independent anchor, final result

The following entries retain the full concrete assembly details from the
source companion. Every row is still **written-pending-check** in the
normal verification run. The filenames in these rows are under `S8/`.

<!-- The eighteen assembly rows below are copied from the independently
checked source crosswalk; they are not generated Lean declarations. -->

| Equation | Existing declarations and role | Status |
| --- | --- | --- |
| 8.52: incomplete-cell cost | `RademacherRemainderLimit.lean`: `rademacher_prefix_maxPressure_change_le` gives the two-sided change on the actual good event; `targetCompleteCells_outside_restriction` identifies the literal complete prefix inside the target outside interval; `rademacherRemainderDifference_abs_le_on_good` and `rademacherRemainderDifference_tendsto` discharge the normalized remainder. | written-pending-check |
| 8.53: exact independent anchor | `MesoscopicScales.lean`: `anchorSites`, `anchorSize`, `anchorSize_eq`; `HighBandTransport.lean`: `anchorLogPotential` is defined on `intervalRowsLaw W (anchorSites W) rademacherLaw`, and `rademacher_anchor_log_potential` transports Proposition 3.8 to this exact law. No same-sample identification with a target prefix is used to invoke the high-band input. | written-pending-check |
| 8.54: anchor outside and terminal orientation | `CyclicTerminalIdentity.lean`: `cyclicFockValue_terminalPacket` places the last three physical sites against the preceding outside product; specialize its site count to `anchorCells W * cellSites W`. `RademacherLogPotential.lean`: `rademacher_anchor_pressure_comparison` invokes the same literal-ring comparison with precisely this specialization. | written-pending-check |
| 8.55: outside equals the complete-cell product | `CellCoordinates.lean`: `intervalClearedProduct_flattenCompleteCells` and `intervalClearedProduct_flatten_core_reset` identify the chronological product on actual flattened cell coordinates. `OutsidePressure.lean`: `intervalMaxDegreeLog_eq_outsidePressure_of_units` identifies its maximal cleared pressure with the boundary outside pressure on the interface-good event. | written-pending-check |
| 8.56: Lemma 8.3 terminal-to-pressure limit | `RademacherSeamLimit.lean`: `rademacher_cyclicSeamDifference_tendstoInProbabilityTri` / `rademacherCyclicSeamDifference_tendsto`, specialized to the anchor, give the normalized actual log determinant minus outside pressure limit. `RademacherLogPotential.lean`: `rademacher_anchor_pressure_comparison` combines that seam limit with the complete-cell pressure limit. The latter conclusion additionally centers by `K_W Phi / M_W`. | written-pending-check |
| 8.57: two literal anchor identities | `PhysicalFock.lean`: `cyclicFockValue_eq_signed_det` and `norm_cyclicFockValue`; `CyclicTerminalIdentity.lean`: `cyclicFockValue_terminalPacket`; `OutsidePressure.lean`: `intervalMaxDegreeLog_eq_outsidePressure_of_units`. These are the actual physical determinant, packet evaluation, and cleared outside product identities used by the seam argument, not caller-supplied replacement identities. | written-pending-check |
| 8.58: coefficient/value comparison | `RademacherSeam.lean`: `rademacherSeam_packet_probability_le`; `RademacherSeamLimit.lean`: `rademacherSeamBadEvent_probability_tendsto_zero` and `rademacherCyclicFock_zero_probability_tendsto_zero`. Their terminal bad event includes zero polynomial values, so the subsequent finite `Real.log` limit does not silently identify `log 0` with the paper's extended logarithm. | written-pending-check |
| 8.59: anchor pressure center | `CompleteCellPressureLimit.lean`: `completeCellPressureError_tendsto`, `intervalCompleteCellPressureError_tendsto`, and `embeddedCompleteCellPressureError_tendsto` derive actual product pressure from independent clipped cores and capped reset sums. `PressureCalibration.lean`: `anchorPressureCenter` is exactly `K_W Phi / M_W`. `RademacherLogPotential.lean`: `rademacher_anchor_pressure_comparison` states actual anchor log potential minus this center tends to zero, with only Cook and Nguyen inputs. | written-pending-check |
| 8.60: vanishing pressure errors | `CellPressureLimit.lean`: `completeCellCoreFluctuation_tendsto` controls the simultaneous centered deviation needed on both sides of the sandwich. `CellResetRates.lean`: `normalizedCellResetLoss_tendsto` sums actual reset losses before one Markov bound. `CompleteCellPressureLimit.lean`: `completeCellPressureError_tendsto` adds the global interface failure and reset norm overhead. `MesoscopicScales.lean`: `tendsto_coreOverhead`, `tendsto_cellConcentrationOverhead`; `RademacherTerminalRates.lean`: `tendsto_rademacherBoundaryBadProbability_mul_logScale`. The written assembly proves the required limits, without claiming a single theorem reproduces the paper's displayed `O_P` expansion verbatim. | written-pending-check |
| 8.61: Corollary 8.4 deterministic calibration | `PressureCalibration.lean`: `normalizedCorePressure_tendsto_of_anchor_comparison` is an internal bridge. Its comparison premise is discharged in `RademacherLogPotential.lean` by `rademacher_anchor_pressure_comparison`, yielding `rademacher_normalizedCorePressure_tendsto`. The public calibrated result takes Cook, Nguyen, and `Section3SubgaussianHighBandInput rademacherLaw 1`; it takes no pressure or anchor comparison certificate. | written-pending-check |
| 8.62: exact anchor rounding | `PressureCalibration.lean`: `anchorPressureCenter_factor` and `tendsto_anchor_dimension_ratio`, using `anchorSize_eq` from `MesoscopicScales.lean`. Calibration recovers `Phi / ell_W` by dividing the convergent anchor center by the positive filled ratio tending to one. This is an equivalent limiting argument and does not require an assumed pressure growth bound. | written-pending-check |
| 8.63: actual target complete-cell count | `MesoscopicScales.lean`: `targetCells`, `remainderSites`, `target_partition`, `target_scalar_partition`; `CellPressureLimit.lean`: `targetCompleteCellsEmbedding`; `RademacherLogPotential.lean`: `rademacher_long_log_potential_comparison` uses this exact floor count and physical prefix. | written-pending-check |
| 8.64: target count and rounding | `MesoscopicScales.lean`: `anchorCells_le_targetCells` proves the stronger `K_N >= K_W`, `tendsto_targetCells` proves divergence, and `target_dimension_ratio` gives exact rounding. `PressureCalibration.lean`: `tendsto_target_dimension_ratio` and `targetPressureCenter_factor` pass from normalized core pressure to the full target dimension. `tendsto_longBranchDimensionRatio` and `calibratedLongBranchCenter_tendsto` also handle arbitrarily alternating branch indicators. | written-pending-check |
| 8.65: actual target outside substitution | `CyclicTerminalIdentity.lean`: `cyclicFockValue_terminalPacket` and `RademacherSeam.lean`: `rademacherSeam_packet_probability_le` are applied to the target's literal outside rows and terminal packet. `RademacherSeamLimit.lean`: `rademacherCyclicSeamDifference_tendsto` supplies the resulting actual-ring limit to `rademacher_long_log_potential_comparison`; no frozen-deformation certificate is requested from the final caller. | written-pending-check |
| 8.66: target terminal pressure | `RademacherSeamLimit.lean`: `rademacherCyclicSeamDifference_tendsto`; `RademacherRemainderLimit.lean`: `rademacherRemainderDifference_tendsto`; `CompleteCellPressureLimit.lean`: `embeddedCompleteCellPressureError_tendsto`. Their sum is exactly the observable in `rademacher_long_log_potential_comparison` from `RademacherLogPotential.lean`; it includes the incomplete outside cells before reducing to the complete-cell center. | written-pending-check |
| 8.67: every fixed-z log potential and branch recombination | `RademacherLogPotential.lean`: `rademacher_long_rows_log_potential`, `rademacher_long_branch_log_potential`, `rademacher_rows_log_potential`, and `rademacher_log_potential`; `HighBandTransport.lean`: `rademacher_direct_branch_log_potential`. The two filled branch observables are recombined for every index, so no eventually fixed branch is assumed. `Section8Results.lean`: `section8_bernoulli_log_potential` exposes the paper's `W/log N -> infinity` hypothesis on the actual IID sequence law. | written-pending-check |
| 8.68: physical Hilbert--Schmidt energy | `RademacherEnergy.lean`: `rademacherCyclicMatrix_energy_eq_one_of_sign`, `rademacherCyclicMatrix_energy_ae_one`, `rademacher_ring_energy_limit`; `RademacherCircularReduction.lean`: `rademacherMatrix_energy_ae_one` transfers this exact energy identity to the actual infinite IID sequence model used by the public theorem. | written-pending-check |
| 8.69: replacement and weak circular law | `RademacherCircularReduction.lean`: `rademacher_circular_law_of_log_potential` invokes the already-proved generic circular-law reduction with the concrete Rademacher moment, energy, and law transport facts. The repository route uses its proved diagonal IID disk reference instead of a new Ginibre-reference assumption. `Section8Results.lean`: `section8_bernoulli_circular_law` discharges the remaining a.e.-z log-potential premise with `ae_of_all` applied to `section8_bernoulli_log_potential`, and concludes convergence for every bounded continuous real test function. | written-pending-check |

## Variants that matter when reading the final signature

1. Polynomial cleared operators exist on singular samples. Inverse
   representations and finite raw logarithms are used on actual good
   events. Terminal zero values are separately included in the bad event.
2. Actual matrix-prefix norms replace the recursive random wedge. This
   permits fixed-fiber singular frames and measurable actual norm losses,
   followed by proved product-law transport and Fubini. No random frame
   selector is an additional input.
3. The matrix-prefix route charges bad past interfaces as well as bad
   current core/endpoints. Its extra site-count exponential term is
   explicitly retained and killed by `log N / W -> 0`; it is not silently
   relabeled as a width-only exponential term.
4. The terminal upper tail follows from coefficient Parseval and Markov.
   The polynomial coefficient lower/capped estimate still uses Cook; zero
   terminal values remain part of the lower-tail event.
5. Frobenius complementary-minor identities provide envelopes; pressure
   uses separately bounded L2 operator norms. These norms are not equated.
6. Exact ceiling exponents are unchanged. Harmless variants include
   `log(eW)`, fixed polynomial RRQR losses, explicit constant multiples in
   exponential failures, and convergence estimates in place of a single
   verbatim `O_P` expansion.
7. Replacement uses the already-proved diagonal IID disk reference route.
   This is a proved reformulation of the source's final Ginibre reference
   argument, with no external reference or replacement certificate.

## Remaining verification work

The source and declaration correspondence is complete, including all
69 equation numbers and the four numbered results. This does **not** mean
that all corresponding Lean modules have passed. The normal serialized
build, its final ordinary `lake build`, and final axiom/caller-signature
audits are still pending. Earlier development oleans establish only the
limited `D` evidence recorded above. Any compiler error must be fixed and
its normal build repeated before promoting the affected entries.

The only intentionally external mathematical obligations are the three
explicit inputs listed above. An implementation entry marked `P` is a
verification status, not a new mathematical assumption or permission to
leave a reset, seam, pressure, or law-transport conclusion as a parameter.
