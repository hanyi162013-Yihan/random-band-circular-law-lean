# Section 9 small-ball formalization map

Reference: Yi Han, *The circular law for non-Hermitian random band matrices:
optimal bandwidth, periodic profile and discrete law*,
[arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1).
All section, theorem, and equation references below use this paper's numbering.
The relevant statements are in Section 7, with proofs in Section 9.

This file describes the interface-control, terminal small-ball, and
arbitrary-frame proof chains. The supporting all-minor, Floquet, and
double-elimination algebra is supplied by the bundled `BernoulliLinearAlgebra`
library. This is not a claim to formalize the entire paper. Stable TeX labels
are listed in [SMALL_BALL_REFERENCE_MAP.md](SMALL_BALL_REFERENCE_MAP.md).

The status terms mean:

- **implemented**: the declaration and its proof are present in the current
  source; publication-wide build and audit verification is pending;
- **external input**: a field of a literature-input structure in
  `ExternalInputs.lean`, supplied as a theorem parameter;
- **bundled dependency**: imported from the `BernoulliLinearAlgebra` library
  included in this repository.

## Explicit trust boundary

| Paper result | Lean declaration | Status |
|---|---|---|
| Cook deformed-square least-singular-value estimate, Lemma 9.2 / (9.11) | `CookDeformedSquareInput.unconditional` | external input |
| Cook estimate conditional on an independent sigma-field | `CookDeformedSquareInput.conditional` | external input |
| Nguyen fixed-index bottom-singular-value estimate, (9.2) | `NguyenBottomSingularInput.fixedIndex` | external input |
| Nguyen overcrowding estimate, (9.1) | `NguyenBottomSingularInput.overcrowding` | external input |

Each Cook input fixes `subgaussianBound`, `lowerWeight`, and `upperWeight`,
with `0 < lowerWeight <= 1 <= upperWeight`. Its constants `beta L`, `cookC L`,
and `cookc L` may depend on those fixed parameters and on the deformation
exponent `L`. Both estimate fields require
`S.subgaussianParameter <= subgaussianBound` and entrywise profile weights
in `[lowerWeight, upperWeight]`. The unit profile used by the concrete packet
is admissible by the bounds covering 1.

Each Nguyen input likewise fixes `subgaussianBound`. Every application of
`fixedIndex` or `overcrowding` requires the square's subgaussian parameter to
lie below that bound; the constants belong to that fixed range. There is no
assertion of one universal constant family for atoms with unbounded
subgaussian parameters or for arbitrarily small positive profile weights.

Cook and Nguyen occur as explicit theorem parameters. RRQR choices,
coordinate masks, CUR eliminations, square embeddings, and internal
conditioning sigma-fields are constructed inside the development rather than
supplied by the caller. The current-source build and placeholder/axiom audits
are tracked in [SMALL_BALL_AUDIT.md](SMALL_BALL_AUDIT.md).

## Section 9 opening: interface control

| Paper step | Lean declaration | Status |
|---|---|---|
| iid centered variance-one subgaussian square | `IidSubgaussianSquare`, `IidSubgaussianFamily` | implemented definitions |
| determinant as product of singular values | `norm_det_eq_prod_matrixSingularValue` | implemented |
| three Nguyen regimes and the cutoff | `nguyenInterfaceThreshold_fixed`, `nguyenInterfaceThreshold_medium`, `nguyenInterfaceThreshold_bulk`, `nguyenInterfaceCutoff` | implemented from Nguyen input |
| union bound for bad bottom indices | `nguyenInterfaceBadEvent_probability_exp_atCutoff` | implemented from Nguyen input |
| determinant lower bound on the good event | `exp_neg_detLoss_le_norm_det_normalized_of_good_atCutoff` | implemented |
| inverse bound on the good event | `norm_normalized_inv_le_exp_of_nguyenGood_atCutoff` | implemented |
| subgaussian operator-norm tail | `normalizedRawComplexMatrix_opNorm_tail` | implemented |
| combined operator/determinant/inverse event | `interfaceCombinedBadEvent`, `interfaceCombinedBadEvent_probability_exp` | implemented |
| caller-facing interface conclusion | `interfaceCanonicalDetUpperLowerInverseControl` | implemented |
| one explicit width threshold discharging positivity, cutoff, and all three union-bound regimes | `interfaceCanonicalLargeWThreshold`, `interfaceCanonicalLargeWConditions` | implemented; constructs all required scalar premises internally |
| interface pair and endpoint datum under that threshold | `interfacePairProbabilityAndPaperEndpointGoodCanonical` | implemented |

## Section 9.1.1: complex strong RRQR with a quantitative variant

The quantitative construction in `StrongRRQR.lean` uses two internal finite
maximum-Gram-volume selections. The witnesses are obtained by
`Classical.choose` from finite maxima (`maximalOrderedColumnSelection` and its
second-round use after transposition). Although the file also proves facts
about `lexFirstMaxMinorSelection`, that lexicographic object is **not** the
path used by the quantitative RRQR theorem.

This is a quantitative variant of arXiv v1 Lemma 9.1, not a proof of its
fixed exponent 4. The implemented construction has `strongRRQRExponent = 16`.
Its rank, coordinate selections, pivot and skeleton identities are literal;
the weaker polynomial exponent is sufficient for the terminal argument.

The selection and least-squares estimates are formulated for rectangular
complex matrices; the paper-facing theorem then specializes to the square
complex matrix `Q`.  Thus neither a real-only reduction nor a pre-supplied
RRQR certificate is hidden in this step.  In particular, min--max,
compression/interlacing, and both left/right multiplication singular-value
inequalities are proved as ordinary finite-dimensional complex linear
algebra lemmas.

| Equation/item | Lean declaration | Status |
|---|---|---|
| spectral expansion behind min--max | `spectral_re_inner_expansion`, `singular_norm_sq_expansion` | implemented over `ℂ` |
| Courant--Fischer subspace forms | `singularValue_le_iff_exists_submodule_bound`, `le_singularValue_iff_exists_submodule_lower_bound` | implemented |
| compression/interlacing | `singularValue_comp_le_of_opNorm_le_one`, `singularValue_comp_le_of_right_opNorm_le_one` | implemented |
| multiplication singular-value inequalities | `matrix_singularValue_mul_le_l2OpNorm_mul`, `matrix_singularValue_mul_le_mul_l2OpNorm` | implemented |
| first and second finite maximum-Gram-volume selections | `maximalOrderedColumnSelection`, `thresholdColumnSelection`, `thresholdRowSelection` | implemented |
| entrywise least-squares bounds from maximal volume | `maximalOrderedColumnSelection_leastSquares_entry_norm_le_one`, `maximumVolumeLeastSquaresMatrix_entry_norm_le_one` | implemented |
| `r = #{j : s_j(Q) > tau}` | `largeSingularValueCount`, `StrongRRQRConclusion.r_eq` | implemented |
| same-cardinality coordinate sets `I,J` | `PaperStrongRRQRConclusion.I`, `.J`, `.card_I`, `.card_J` | implemented |
| `K_piv = Q_{I,J}`, (9.3) | `PaperStrongRRQRConclusion.K_piv_eq` | implemented |
| invertible pivot, including total `0 x 0` convention | `StrongRRQRConclusion.pivot_isUnit`, `empty_pivot_convention`, `StrongRRQRConclusion.empty_pivot` | implemented |
| exact `X_skel,Y_skel,E0`, (9.4) | `thresholdSkeletonData`, `skeletonX`, `skeletonY`, `skeletonError` | implemented |
| literal block identity, (9.5) | `threshold_permutedMatrix_eq_skeletonMatrix`, `StrongRRQRConclusion.block_identity` | implemented |
| first-round residual estimate, (9.7) | `norm_thresholdResidual_le_scale_mul_nextSingularValue` | implemented |
| polynomial residual estimate | `norm_thresholdResidual_le_rrqrResidualScale_mul_tau` | implemented |
| pivot singular-value lower comparison | `pow_inv_mul_singularValue_le_thresholdPivot`, `StrongRRQRConclusion.pivot_singular_lower` | implemented quantitative variant: exponent 16, not Lemma 9.1's fixed 4 |
| `||X_skel|| + ||Y_skel|| <= n^C`, variant of (9.6) | `norm_thresholdSkeletonData_Xskel_add_Yskel_le_pow` | implemented with `strongRRQRExponent = 16`; paper exponent is 4 |
| `||E0|| <= n^C tau`, variant of (9.6) | `norm_thresholdSkeletonData_E0_le_pow_mul_tau` | implemented with `strongRRQRExponent = 16`; paper exponent is 4 |
| certificate-free polynomial-loss variant of Lemma 9.1 | `strongRRQRConclusion`, `exists_strongRRQRConclusion`, `paperStrongRRQRConclusion`, `exists_paperStrongRRQRConclusion` | implemented with exponent 16 |

## Section 9.1.2: scaling, literal CUR/Schur, and two Cook applications

| Equation/item | Lean declaration | Status |
|---|---|---|
| physical versus row-scaled matrices and polynomials, (9.12)--(9.13) | `rowScaled_threeBlockH_eq_smul_physical`, `rowScaled_threeBlockHPolynomial_eq_smul_physical`, `rowScaled_threeBlockDetPolynomial_eq` | implemented |
| exact coefficient/value common scale | `rowScaled_packetTerminalCoefficientNorm_eq`, `rowScaled_packetTerminalValue_eq`, `physicalPacketTerminalCoefficientNorm_eq_inv_mul_rowScaled`, `physicalPacketTerminalValue_eq_inv_mul_rowScaled` | implemented |
| capped-loss and zero-event scale invariance | `cappedLogLoss_physical_eq_rowScaled`, `physicalPacketTerminalValue_eq_zero_iff_rowScaled`, `physicalPacketTerminalZeroEvent_eq_rowScaled` | implemented |
| transfer of a row-scaled conclusion to the physical normalization | `physicalTerminalConclusion_of_rowScaled` | implemented directly |
| threshold rank and residual size, (9.14) | `packetStrongRRQRConclusion`, `terminalBalancedSize`, `terminalResidual_sideCount_eq` | implemented |
| reindexed perturbation and four blocks, (9.15)--(9.16) | `terminalBalancedPerturbation`, `delta11`, `delta12`, `delta21`, `delta22` | implemented |
| pivot perturbation, (9.18) | `pivot_add_det_lower_of_inv_mul_norm_le_half`, `norm_pivot_add_inv_le_two_mul_of_inv_mul_norm_le_half` | implemented |
| zero-centre extension of the skeleton | `terminalExtendedSkeletonData` | implemented |
| literal `H = skeleton + Delta` | `threeBlockH_reindexed_eq_skeleton_add_perturbation` | implemented |
| `G21,G12,F`, (9.19)--(9.20) | `G21`, `G12`, `F` | implemented definitions |
| literal three-factor CUR identity, (9.21) | `skeleton_add_eq_CUR` | implemented |
| literal determinant/Schur factorization | `det_skeleton_add_eq_det_KDelta_mul_det_residual`, `norm_threeBlockH_det_eq_pivot_mul_residual` | implemented |
| bounds for the CUR terms, (9.22)--(9.23) | `G21_norm_le`, `G12_norm_le`, `F_norm_le`, `terminalDelta_blocks_norm_le` | implemented |
| residual left/right counts, (9.24)--(9.26) | `outerResidualLeftCount`, `outerResidualRightCount`, `terminalResidual_sideCount_eq` | implemented |
| two complete square sizes, (9.26)--(9.27) | `balancedSquareSize`, `twoSquareDimensions`, `twoSquare_cardinalities` | implemented |
| two disjoint square embeddings | `firstSquareEntryEmbedding`, `secondSquareEntryEmbedding`, `squareEntryEmbedding_disjoint`, `terminalBalancedEntryEmbeddings_ne` | implemented |
| restricted iid Cook squares | `IidSubgaussianFamily.firstBalancedCookSquare`, `.secondBalancedCookSquare`, `.terminalFirstCookSquare`, `.terminalSecondCookSquare` | implemented |
| fresh/complement sigma-fields and independence | `coordinateSquareFresh_indep_conditioning`, `firstBalancedFresh_indep_conditioning`, `secondBalancedFresh_indep_conditioning` | implemented |
| literal random residual plus deformation | `terminalCURResidual_eq_random_add_deformation` | implemented |
| first Cook diagonal identity, (9.27) | `terminalCURResidual_toBlocks11_eq_profiled_add_deformation` | implemented |
| second Cook Schur identity, (9.32) | `terminalSecondCookSchur_eq_profiled_add_deformation` | implemented |
| conditioning measurability of both deformations | `terminalFirstCookDeformation_stronglyMeasurable`, `terminalSecondCookDeformation_stronglyMeasurable` | implemented directly |
| honest two-stage conditional Cook estimate, (9.30)--(9.35) | `coordinateTwoCook_probability_and_det`, `coordinateTwoCookTruncated_probability_and_det` | implemented |
| independent universes for the probability space and global coordinate type | `CoordinateConditionalCook`, `CoordinateTwoCook`, `CoordinateTwoCookTruncated` theorem APIs with `Omega : Type u`, `iota : Type v` | implemented; avoids restricting the public probability space to `Type 0` |
| residual determinant lower bound on the two-Cook good event, (9.35) | determinant conclusion of `coordinateTwoCookTruncated_probability_and_det` | implemented |
| uniformized two-Cook failure bound, with floor-safe `exp(-cW/4)` tail | `uniformCookFailureBound`, `cookFailureBound_le_uniform`, `twoCookFailureBounds_le_uniform_of_input` | implemented; uses `W / 3 <= n_i`, hence `W <= 4 n_i`, without the false rounded implication `W <= 3 n_i` |
| canonical scalar large-`W` conditions | `PacketTerminalCanonicalLargeWConditions` | implemented definition; independent of `Q` and realized matrices |
| explicit width threshold for the canonical choice `t = W` | `terminalCanonicalLargeWThreshold` | implemented; depends only on Cook, `Kz`, and the fixed subgaussian bound `Ksg` |
| derivation of every terminal scalar premise from that threshold | `packetTerminalCanonicalLargeWConditions_of_ge_threshold` | implemented; discharges the scalar conditions internally |
| uniform determinant-factor comparison | `terminalUniformDeterminantFactor_le_actualFactors` | implemented directly |
| Gram-volume/value-loss bridge for (9.36) | `exp_neg_terminalUniformValueLoss_mul_gramVolume_le` | implemented directly |
| deterministic exposure-event RRQR/CUR bounds | `PacketTerminalExposureBounds`, `packetTerminalExposureBounds` | implemented |
| first deformation, first-block inverse, and second deformation bounds | `terminalConcreteFirstDeformationNorm`, `terminalConcreteFirstResidualInverse`, `terminalConcreteSecondDeformationNorm` | implemented |
| honest truncated-Cook premise and control packaging | `CoordinateTwoCookTruncatedPremises`, `packetTerminalGoodEventControl_of_coordinateTwoCookTruncated`, `packetTerminalCanonicalCookPremises` | implemented; internal only |
| residual determinant to literal terminal value | `terminalConcreteValueLower_of_residualDet` | implemented |
| fully constructed good-event control | `packetTerminalConcreteGoodEventControl` | implemented; no caller certificate |
| final `Q`-uniform public terminal theorem | `TerminalAssembly.packetTerminalConcreteConclusion`, `section9TerminalSmallBall` | implemented |

The fixed-`Q` construction is uniform in `Q`.  The following additional
module turns that uniform theorem into the conditional statement made in the
paper, without attempting to make the internal RRQR selector measurable.

### Random outside `Q` and conditional terminal conclusion

| Paper item | Lean declaration | Status |
|---|---|---|
| complete fresh packet as one finite-dimensional random variable | `TerminalAssembly.packetFreshSample`, `measurable_packetFreshSample` | implemented |
| joint Borel measurability of the final determinant in `(Q,x)` | `continuous_packetTerminalValueFromSample` | implemented |
| continuity/measurability of the complete coefficient norm in `Q` | `coeffwiseContinuous_packetTerminalDetPolynomial`, `continuous_packetTerminalCoefficientNorm` | implemented |
| generic conditional-distribution/Fubini lift for an outside parameter independent of a fresh variable | `condDistrib_ae_eq_const_of_indepFun`, `condExp_parameterized_ae_eq_integral_map_of_indepFun`, `condExp_parameterized_ae_le_of_fixed_integral_bound` | implemented |
| conditional capped loss and zero probability for outside-measurable random `Q` | `PacketTerminalRandomQConditionalResult.capped`, `.zero_probability` | implemented |
| pointwise reverse estimate and conditional complement probability | `PacketTerminalRandomQConditionalResult.reverse`, `.reverse_event_compl_probability` | implemented |
| exact Parseval in every outside fiber | `PacketTerminalRandomQConditionalResult.parseval_fiber` | implemented; no global moment premise |
| certificate-free random-`Q` conditional theorem | `packetTerminalRandomQConditionalResult`, `section9TerminalSmallBallConditional` | implemented |
| optional Bochner conditional-expectation Parseval | `packetTerminalRandomQ_condExp_parseval` | implemented; correctly separated because it requires integrability of the random second moment |

The conditional theorem uses joint measurability of the final determinant,
loss, and coefficient functions, then applies the uniform fixed-`Q` theorem
fiber by fiber. It does not require measurability of the internal
maximum-volume or RRQR selector.

## Terminal coefficient comparison, reverse estimate, and Parseval

| Equation/item | Lean declaration | Status |
|---|---|---|
| partial-matching coefficient expansion, (9.37) | three-block squarefree expansion API | bundled dependency |
| all-minor coefficient comparison, Lemma 7.5 / (7.24), proved in (9.44)--(9.46) | `threeBlockTerminalCoefficientOnPacket_concreteComparison` | bundled dependency |
| threshold singular-product bounds, (9.41)--(9.42) | `threeBlockTerminalCoefficient_product_bounds` | implemented |
| threshold product to Gram-volume bridge | `gramVolume_le_threshold_factor_mul_canonicalLargeSingularProduct` | implemented directly |
| pivot inverse spectral bridge | `strongRRQRPivot_inv_norm_le_pow_div_threshold` | implemented directly |
| shift comparison | `ThreeBlockShiftTranslation` API | bundled dependency |
| coefficient-norm positivity | `packetTerminalCoefficientNorm_pos` | implemented |
| capped good/bad integration | `integral_cappedLogLoss_le_of_common_product_bounds`, `terminalSmallBallConclusion_of_capped` | implemented |
| zero probability from all caps | `terminal_cap_mul_zeroProbability_le_integral`, `zeroProbability_of_all_capped_bounds` | implemented |
| valid-matching count | `validMatchingIndexPolynomialCount` | implemented |
| reverse estimate | `packetTerminal_reverse_validMatching`, `packetTerminal_reverse_indexPolynomial` | implemented |
| maximum-coordinate tail | `packetCoordinateMaxThreshold`, `measureReal_compl_packetCoordinateMaxEvent_le` | implemented |
| exact squarefree Parseval | `integral_norm_evalSquarefree_sq_eq_coeffNorm`, `packetTerminal_parseval`, `integral_norm_threeBlockH_det_sq` | implemented |
| terminal result package | `PacketTerminalSmallBallResult`, `packetTerminalSmallBallResult_of_goodEventControl` | implemented; internal good-event package only |
| physical-normalization transfer | `physicalPacketTerminalSmallBallConclusion`, `section9PhysicalTerminalSmallBall` | implemented |

## Boundary passage before Section 9.2

| Paper step | Lean declaration | Status |
|---|---|---|
| global boundary polynomial equals squarefree evaluation | `eval_globalBoundaryDetPolynomial_eq_evalSquarefree` | implemented directly |
| chart factorization by `det Theta_11` | `eval_globalBoundaryDetPolynomial_eq_det_mul_packetTerminalValue` | implemented directly |
| common-scale transfer on the invertible upper-left chart | `chartBoundaryTerminalConclusion` | implemented directly |
| extension to every invertible boundary relation by dense chart perturbation | `literalCoordinateTerminalTheorem_of_packet` | implemented directly |

The boundary passage preserves capped loss, zero probability, and Parseval.
Its deterministic input is the `Q`-uniform packet theorem
`LiteralPacketTerminalTheorem`; random outside parameters are handled by the
separate conditional lift after final coefficients have been exposed.

## Section 9.2: arbitrary frames

| Equation/item | Lean declaration | Status |
|---|---|---|
| internal orthonormal completion of `U,V` | `completedFrameBasis`, `completedFrameMatrix`, `completedFrameMatrix_mem_unitary` | implemented |
| artificial `Theta_lambda^(r;U,V)`, (9.47) | `artificialTheta`, `literalArtificialTheta` | implemented |
| invertibility for nonzero `lambda` | `artificialTheta_det_isUnit`, `literalArtificialTheta_det_isUnit` | implemented |
| exterior diagonal expansion, (9.50) | `compound_diagonal_apply`, `normalizedArtificialCompound_eq`, `normalizedSelectedArtificialCompound_eq` | implemented |
| all degrees `k != r`, (9.51) | `normalizedArtificialCompound_otherDegree_tendsto`, `normalizedArtificialCompound_otherDegree_opNorm_tendsto`, `normalizedSelectedArtificialCompound_otherDegree_tendsto` | implemented; entrywise and Euclidean operator-norm convergence are both explicit |
| degree `r` rank-one limit, (9.52) | `normalizedArtificialCompound_rankDegree_tendsto`, `normalizedArtificialCompound_rankDegree_opNorm_tendsto`, `normalizedSelectedArtificialCompound_rankDegree_tendsto` | implemented; entrywise and Euclidean operator-norm convergence are both explicit |
| literal boundary exterior trace coefficient | `literalBoundaryExteriorTensor`, `coeff_globalBoundaryDetPolynomial_eq_exteriorTrace`, `literalBoundaryExteriorCoefficient_eq_coeff` | implemented |
| polynomial/value limit, (9.53) | `literalArtificialPolynomialValue_tendsto`, `literalArtificialRandomValue_tendsto` | implemented |
| exact graph-volume normalization and limit, (9.54) | `normalized_literalArtificialTheta_gramVolume`, `normalizedGraphProduct_tendsto` | implemented |
| coefficient and coefficient-norm limits, (9.53) and (9.55) | `literalArtificialCoefficient_tendsto`, `literalArtificialCoefficientNorm_tendsto` | implemented |
| scaled coefficient bounds | `literalArtificialCoefficientNorm_scaled_bounds` | implemented |
| bounded convergence of capped loss | `cappedIntegral_limit_le_of_uniform_bound`, `cappedIntegral_limit_le_of_uniform_bound_of_lower` | implemented |
| literal arbitrary-frame deduction | `literalArbitraryFrame_smallBall_deduction_of_scaled_bounds`, `literalArbitraryFrame_smallBall_deduction` | implemented directly |
| endpoint operator bound | `EndpointOperatorGood`, `norm_endpointFactor_le_endpointOperatorCrudeBound`, `gramVolume_endpointFactor_le_of_endpointOperatorGood` | implemented directly |
| paper endpoint datum, with invertibility derived internally | `PaperEndpointGood`, `PaperEndpointGood.CL_det_isUnit`, `.BR_det_isUnit`, `.endpointFactor_det_inv_norm_le` | implemented directly |
| quantitative Hodge comparison constant | `literalBoundaryHodgeComparisonConstant`, `endpointFactor_compound_norm_le_endpointCompoundCrudeBound` | implemented directly |
| endpoint-good coefficient bounds | `literalArtificialCoefficientNorm_scaled_bounds_of_endpointGood` | implemented directly |
| arbitrary-frame small-ball deduction on endpoint good event, Theorem 7.10 / (7.54)--(7.55), via (9.54)--(9.55) | `literalArbitraryFrame_smallBall_deduction_of_endpointGood` | implemented directly |
| internal packet-to-arbitrary bridge | `literalArbitraryFrameSmallBall_of_packetConcrete` | implemented; its packet-theorem parameter is hidden by the public wrappers |
| interface probability plus arbitrary-frame package | `InterfacePairLiteralArbitraryFrameSmallBallConclusion`, `interfacePairProbabilityAndLiteralArbitraryFrameSmallBall_of_packetConcrete` | implemented |
| caller-facing endpoint-good arbitrary-frame theorem | `section9ArbitraryFrameSmallBall` | implemented |
| caller-facing combined Nguyen/Cook theorem | `section9InterfaceAndArbitraryFrameSmallBall` | implemented; no terminal/RRQR/mask/deformation certificate |
| leading compound entry as a determinant of the prescribed frame columns | `directBoundaryFrameMinor`, `compound_boundaryCompletedFrameMatrix_leading` | implemented; eliminates the noncanonical completion |
| selected exterior rank-one operator in direct-minor form | `directBoundaryFrameExteriorRankOne`, `selectedBoundaryFrameExteriorRankOne_eq_direct` | implemented |
| literal limiting coefficient in completion-free form | `directLiteralFrameCoefficient`, `literalFrameCoefficient_eq_direct` | implemented |
| coefficient measurability from endpoint matrices and frame coordinates | `FrameCoordinateMeasurable`, `measurable_literalFrameCoefficient` | implemented; no measurable unitary completion premise |
| generic fiberwise-to-conditional squarefree lift | `RandomFrame.ConditionalResult`, `RandomFrame.conditionalResult_of_fiberwise` | implemented |
| conditional arbitrary-frame theorem for outside-measurable endpoint/frame data | `RandomFrame.literalRandomFrameConditionalResult_of_packetConcrete`, `section9ArbitraryFrameSmallBallConditional` | implemented; caller supplies only paper data plus ordinary measurability/independence |
| optional conditional-expectation Parseval | `RandomFrame.condExp_parseval` | implemented; global integrability is required only for this optional reformulation |

The exterior declarations prove the entrywise and Euclidean
`L2Operator`-norm limits along the cofinal sequence `lambda_q = q + 1`.  The
exact diagonal exponent identity is formalized by
`normalizedDiagonalCompound_apply`.  The sharper uniform operator-norm rates
`lambda^{-|k-r|}` for `k != r` and the `lambda^{-2}` rank-degree remainder are
not packaged as separate quantitative inequalities; the proved limit
statements are sufficient for the Section 9.2 deduction.

## Formalization conventions and scope

1. The RRQR construction uses rectangular complex maximum-volume and
   least-squares lemmas, together with complex min--max, compression
   interlacing, and multiplication inequalities. Its exponent is 16; it
   supplies the polynomial-loss variant needed for the terminal argument,
   not the fixed exponent 4 stated in Lemma 9.1.
2. The conditional random-`Q` proof is based on final-output joint
   measurability and the uniform fixed-`Q` estimate. Internal RRQR choices
   are not required to be measurable.
3. The exposure and two-Cook steps correspond to (9.17) and (9.28)--(9.35).
   `matrixNormTruncation` uses a measurable hard cutoff (zero above the
   norm threshold), rather than the radial truncation displayed in (9.29).
   It has the same required norm bound and equality on the exposure event.
   The proof bounds the first inverse on its good event and truncates the
   full second Schur deformation. Thus it realizes the two-Cook argument
   without separately defining the exact inverse-cutoff function in (9.31).
   `artificialSecondCookBottom` gives the corresponding determinant
   factorization, and the failure probabilities include the exposure cost.
4. The square-size comparison explicitly proves the floor-safe bound
   `W <= 4 n_i`; the uniform failure tail uses `exp(-c W / 4)`, as in the
   size comparison following (9.30).
5. Complex shifts are constrained through their norm, consistent with
   `|zeta_W| = sqrt(3W) |z|` in Proposition 7.3. Displays using `e^{\pm L}`
   are represented by separate lower and upper inequalities.
6. `interfaceCanonicalLargeWThreshold` discharges the small-index, cutoff,
   and large-width conditions of the three Nguyen regimes. Input
   admissibility retains the fixed subgaussian bounds explicitly.
7. Equations (9.51)--(9.52) are represented by entrywise and Euclidean
   operator-norm limit theorems along `lambda_q = q + 1`. Their sharper
   displayed rates are not separately packaged as quantitative inequalities.
8. The core conditional results include fiberwise Parseval. A Bochner
   conditional-expectation reformulation is separate and requires the
   random second moment to be integrable.

## Final caller-facing declarations and verification

`Section9Results.lean` exports the following paper-facing interfaces.  The
large-width hypotheses are single explicit thresholds; callers do not
supply `PacketTerminalCanonicalLargeWConditions` or the interface cutoff
inequalities.

| Result | Declaration | Explicit literature input |
|---|---|---|
| complex RRQR with exponent 16 (variant of Lemma 9.1) | `exists_paperStrongRRQRConclusion` | none |
| row-scaled terminal small ball | `section9TerminalSmallBall` | `CookDeformedSquareInput` |
| outside-measurable random-`Q` conditional terminal small ball | `section9TerminalSmallBallConditional` | `CookDeformedSquareInput` |
| physical-normalization terminal small ball | `section9PhysicalTerminalSmallBall` | `CookDeformedSquareInput` |
| arbitrary frames from a paper endpoint-good datum | `section9ArbitraryFrameSmallBall` | `CookDeformedSquareInput` |
| outside-measurable conditional arbitrary frames | `section9ArbitraryFrameSmallBallConditional` | `CookDeformedSquareInput` |
| interface control and arbitrary frames together | `section9InterfaceAndArbitraryFrameSmallBall` | `NguyenBottomSingularInput`, `CookDeformedSquareInput` |

The standalone arbitrary-frame result explicitly retains the paper-level
`PaperEndpointGood` premise.  Its conditional version requires that premise
for each outside parameter, together with the paper's outside-sigma-field
measurability and independence hypotheses.  Only the combined theorem
constructs endpoint goodness internally from Nguyen's interface input.  The
optional conditional-expectation Parseval reformulation additionally needs
integrability and is not part of the core conclusion.

Publication verification status: **pending**.

The publication tree must pass the complete `lake build`, the local-source
placeholder scan, and `Section9/SmallBallAxiomAudit.lean`. The audit prints
both foundational axiom dependencies and public theorem signatures. It must
confirm the explicit Cook/Nguyen input parameters and their admissibility
hypotheses, and the absence of caller-supplied RRQR, pivot, mask, elimination,
deformation, good-event, or measurable-completion certificates.

Cook and Nguyen are theorem parameters, so they do not appear in the
`#print axioms` lists; their visibility and quantifiers are inspected in the
accompanying `#print` signatures. Current verification results belong in
[SMALL_BALL_AUDIT.md](SMALL_BALL_AUDIT.md).
