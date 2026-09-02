# Section 9 small-ball reference map

Reference: Yi Han, *The circular law for non-Hermitian random band matrices:
optimal bandwidth, periodic profile and discrete law*,
[arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1).
This index uses the paper's current TeX labels and printed numbers. It maps
the local small-ball statements in Section 7 to their proof chains in
Section 9. Lean names are in `BernoulliSection9` unless identified as part
of the supporting `BernoulliLinearAlgebra` library.

The source correspondence below does not replace publication verification.
The complete build and public-signature audit passed on 2026-09-02; see
[SMALL_BALL_AUDIT.md](SMALL_BALL_AUDIT.md). For theorem hypotheses and precise
coverage, see [SMALL_BALL_FORMALIZATION_MAP.md](SMALL_BALL_FORMALIZATION_MAP.md).

## Named statements

| TeX label | Paper result | Lean entry point / scope |
|---|---|---|
| `lem:local-interface-control` | Lemma 7.1 | `interfaceCanonicalDetUpperLowerInverseControl`; Nguyen input is explicit |
| `prop:local-terminal` | Proposition 7.3 | `section9TerminalSmallBall`, `section9TerminalSmallBallConditional`, `section9PhysicalTerminalSmallBall` |
| `lem:local-all-minor` | Lemma 7.5 | `BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket_concreteComparison` |
| `lem:local-boundary-volume` | Proposition 7.7 | Supporting boundary Gram-volume comparison; used by `literalArtificialCoefficientNorm_scaled_bounds` |
| `corollary885` | Corollary 7.9 | `literalCoordinateTerminalTheorem_of_packet`, `chartBoundaryTerminalConclusion` |
| `thm:local-complex-frame` | Theorem 7.10 | `section9ArbitraryFrameSmallBall`, `section9ArbitraryFrameSmallBallConditional`, `section9InterfaceAndArbitraryFrameSmallBall` |
| `lem:local-rrqr` | Lemma 9.1 | `exists_paperStrongRRQRConclusion`: polynomial-loss variant with exponent 16; the paper fixes exponent 4 |
| `lem:local-cook-input` | Lemma 9.2 | `CookDeformedSquareInput.unconditional`, `.conditional`: explicit literature input |

Each Cook input fixes a subgaussian bound and a positive weight interval
containing 1. Its constants depend on those fixed parameters and the
deformation exponent. Each Nguyen input fixes a subgaussian bound.
Applications explicitly require the atom and profile to lie within those
fixed bounds. Neither structure demands uniform constants over all atom
parameters or all positive profile intervals.

## Local statement equations

| TeX label | Equation | Lean entry point / correspondence |
|---|---|---|
| `eq:local-interface-control` | (7.3) | `interfaceCanonicalDetUpperLowerInverseControl` |
| `eq:local-terminal-matrix` | (7.16) | Three-block matrix definitions in `BernoulliLinearAlgebra`; concrete packet matrices in `TerminalConcreteScaling.lean` |
| `eq:local-terminal-polynomial` | (7.17) | `packetTerminalValue` and supporting three-block determinant polynomial |
| `eq:local-terminal-coefficients` | (7.18) | `packetTerminalCoefficientNorm` |
| `eq:local-terminal-capped` | (7.19) | `PacketTerminalSmallBallResult`; `PacketTerminalRandomQConditionalResult.capped` |
| `eq:local-terminal-zero` | (7.20) | `zeroProbability_of_all_capped_bounds`; `PacketTerminalRandomQConditionalResult.zero_probability` |
| `eq:local-max-event` | (7.21) | `packetCoordinateMaxThreshold`, `measureReal_compl_packetCoordinateMaxEvent_le` |
| `eq:local-terminal-reverse` | (7.22) | `packetTerminal_reverse_validMatching`, `packetTerminal_reverse_indexPolynomial` |
| `eq:local-all-minor` | (7.24) | `BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket_concreteComparison` |
| `eq:local-DTheta` | (7.42) | `literalBoundaryExteriorTensor`, `coeff_globalBoundaryDetPolynomial_eq_exteriorTrace` |
| `eq:local-CTheta` | (7.43) | Coefficient norm of the literal boundary polynomial in `ArbitraryFrameConcrete.lean` |
| `eq:local-DTheta-det` | (7.44) | `eval_globalBoundaryDetPolynomial_eq_evalSquarefree`, `coeff_globalBoundaryDetPolynomial_eq_exteriorTrace` |
| `eq:local-LT` | (7.48) | `cappedLogLoss`, including the zero-value convention |
| `eq:local-boundary-capped` | (7.49) | `chartBoundaryTerminalConclusion`, `literalCoordinateTerminalTheorem_of_packet` |
| `eq:local-frame-coefficients` | (7.54) | `literalArtificialCoefficientNorm_scaled_bounds_of_endpointGood`, `literalArbitraryFrame_smallBall_deduction_of_endpointGood` |
| `eq:local-frame-capped` | (7.55) | `literalArbitraryFrame_smallBall_deduction_of_endpointGood`; public wrappers in `Section9Results.lean` |

## Interface control and complex RRQR

| TeX label | Equation | Lean entry point / correspondence |
|---|---|---|
| `eq:local-overcrowding` | (9.1) | `NguyenBottomSingularInput.overcrowding` |
| `eq:local-fixed-bottom` | (9.2) | `NguyenBottomSingularInput.fixedIndex` |
| `eq:local-Kpiv` | (9.3) | `PaperStrongRRQRConclusion.K_piv_eq` |
| `eq:local-skeleton-definitions` | (9.4) | `thresholdSkeletonData`, `skeletonX`, `skeletonY`, `skeletonError` |
| `eq:local-skeleton-identity` | (9.5) | `threshold_permutedMatrix_eq_skeletonMatrix`, `StrongRRQRConclusion.block_identity` |
| `eq:local-skeleton-bounds` | (9.6) | `StrongRRQRConclusion.pivot_singular_lower`, `.coefficient_bound`, `.error_bound`; quantitative variant with exponent 16 |
| `eq:first-rrqr` | (9.7) | `thresholdColumnSelection`, `norm_thresholdResidual_le_scale_mul_nextSingularValue`; finite maximum-volume construction |
| `eq:second-rrqr` | (9.8) | `thresholdRowSelection`, `pow_inv_mul_singularValue_le_thresholdPivot` |
| `eq:X-from-two-rrqr` | (9.9) | `thresholdSkeletonData`; `norm_thresholdSkeletonData_Xskel_add_Yskel_le_pow` |
| `eq:E-from-two-rrqr` | (9.10) | `norm_thresholdSkeletonData_E0_le_pow_mul_tau` |
| `eq:local-cook-input` | (9.11) | `CookDeformedSquareInput.unconditional`, `.conditional`, `cookFailureBound` |

The RRQR rank is `largeSingularValueCount`, with exact coordinate-cardinality,
pivot, skeleton, block-identity, and empty-pivot conventions. Min--max,
compression/interlacing, and multiplication inequalities are proved over
complex finite-dimensional spaces. The exponent-16 bounds are sufficient
for the polynomial-loss terminal proof; they do not establish the sharper
fixed-exponent-4 numerical statement of Lemma 9.1.

## Terminal CUR and the two conditional Cook steps

| TeX label | Equation | Lean entry point / correspondence |
|---|---|---|
| `eq:local-terminal-scaling` | (9.13) | `cappedLogLoss_physical_eq_rowScaled`, `physicalPacketTerminalZeroEvent_eq_rowScaled`; the common polynomial/value scale preceding it is in `TerminalConcreteScaling.lean` |
| `eq:local-r-nres` | (9.14) | `packetStrongRRQRConclusion`, `terminalBalancedSize`, `terminalResidual_sideCount_eq` |
| `eq:local-Delta-tilde` | (9.15) | `terminalBalancedPerturbation` |
| `eq:local-Delta-split` | (9.16) | `delta11`, `delta12`, `delta21`, `delta22` |
| `eq:local-pivot-exposure-event` | (9.17) | `PacketTerminalExposureBounds`, `packetTerminalExposureBounds` |
| `eq:local-pivot-det` | (9.18) | `pivot_add_det_lower_of_inv_mul_norm_le_half`, `rrqrPivot_det_lower_selectedProduct` |
| `eq:local-Gs` | (9.19) | `G21`, `G12` |
| `eq:local-F` | (9.20) | `F` |
| `eq:local-CUR` | (9.21) | `skeleton_add_eq_CUR`, `det_skeleton_add_eq_det_KDelta_mul_det_residual` |
| `eq:local-CUR-term-bounds` | (9.22) | `G21_norm_le`, `G12_norm_le`, `terminalDelta_blocks_norm_le` |
| `eq:local-F-bound` | (9.23) | `F_norm_le`, `F_norm_le_terminalFPolynomialScale` |
| `eq:local-counts` | (9.25) | `outerResidualLeftCount`, `outerResidualRightCount`, `terminalResidual_sideCount_eq` |
| `eq:local-n1` | (9.26) | `balancedSquareSize`, `twoSquareDimensions`, `twoSquare_cardinalities` |
| `eq:local-two-cook-blocks` | (9.27) | `terminalCURResidual_eq_random_add_deformation`, `terminalCURResidual_toBlocks11_eq_profiled_add_deformation` |
| `eq:local-full-exposure-event` | (9.28) | `CoordinateTwoCookTruncatedPremises`, `packetTerminalCanonicalCookPremises` |
| `eq:local-measurable-norm-truncation` | (9.29) | `matrixNormTruncation`, `norm_matrixNormTruncation_le`, `matrixNormTruncation_stronglyMeasurable_entry`: hard-cutoff implementation with the required norm and good-event equality properties |
| `eq:local-cook-one` | (9.30) | First probability bound in `coordinateTwoCookTruncated_probability_and_det` |
| `eq:local-truncated-inverse` | (9.31) | Corresponding good-event inverse control in `terminalConcreteFirstResidualInverse`; the proof truncates the full second deformation instead of packaging this exact inverse-cutoff function |
| `eq:local-second-schur` | (9.32) | `terminalSecondCookSchur_eq_profiled_add_deformation`, `terminalConcreteSecondDeformationNorm`; combined with norm truncation for the global Cook application |
| `eq:local-cook-two` | (9.33) | Second probability bound in `coordinateTwoCookTruncated_probability_and_det` |
| `eq:local-artificial-bottom-block` | (9.34) | `artificialSecondCookBottom`, used by `coordinateTwoCookTruncated_probability_and_det` |
| `eq:local-residual-det` | (9.35) | Determinant conclusion of `coordinateTwoCookTruncated_probability_and_det` |
| `eq:local-value-lower` | (9.36) | `terminalConcreteValueLower_of_residualDet`, `exp_neg_terminalUniformValueLoss_mul_gramVolume_le` |

The two complete iid squares and their independence are constructed by
`firstSquareEntryEmbedding`, `secondSquareEntryEmbedding`,
`squareEntryEmbedding_disjoint`, and the coordinate-conditioning results in
`FreshIndependence.lean`. The eventwise-to-global probability passage uses
bounded measurable deformations, with the exposure failure charged explicitly.

## Coefficients, reverse estimate, and Parseval

| TeX label | Equation | Lean entry point / correspondence |
|---|---|---|
| `eq:local-partial-permutation` | (9.37) | Three-block squarefree coefficient expansion in `BernoulliLinearAlgebra` |
| `eq:local-partial-permutation-count` | (9.38) | `validMatchingIndexPolynomialCount`, `card_validThreeBlockMatching_le_indexPolynomial` |
| `eq:local-coeff-upper-zero` | (9.39) | `threeBlockTerminalCoefficient_product_bounds` at zero shift |
| `eq:local-coeff-lower-zero` | (9.40) | `threeBlockTerminalCoefficient_product_bounds` at zero shift |
| `eq:local-coeff-upper` | (9.41) | `threeBlockTerminalCoefficient_product_bounds` |
| `eq:local-coeff-lower` | (9.42) | `threeBlockTerminalCoefficient_product_bounds` |
| `eq:local-parseval` | (9.43) | `integral_norm_evalSquarefree_sq_eq_coeffNorm`, `packetTerminal_parseval`, `integral_norm_threeBlockH_det_sq` |
| `eq:local-monomial-minor` | (9.44) | Supporting three-block matching/minor expansion in `BernoulliLinearAlgebra` |
| `eq:local-coefficients-to-minors` | (9.45) | Supporting all-minor coefficient comparison in `BernoulliLinearAlgebra` |
| `eq:local-all-minor-CB` | (9.46) | Supporting all-minor Gram identity in `BernoulliLinearAlgebra`; `matrix_largeSingularProduct_le_gramVolume` supplies the singular-product bridge |

## Arbitrary frames

| TeX label | Equation | Lean entry point / correspondence |
|---|---|---|
| `definetheframe` | (9.47) | `artificialTheta`, `literalArtificialTheta`; completion by `completedFrameBasis` |
| `eq:local-wedge-expansion` | (9.50) | `compound_diagonal_apply`, `normalizedArtificialCompound_eq`, `normalizedSelectedArtificialCompound_eq` |
| `eq:local-other-k-limit` | (9.51) | `normalizedArtificialCompound_otherDegree_tendsto`, `normalizedArtificialCompound_otherDegree_opNorm_tendsto` |
| `eq:local-right-r-limit` | (9.52) | `normalizedArtificialCompound_rankDegree_tendsto`, `normalizedArtificialCompound_rankDegree_opNorm_tendsto` |
| `eq:local-polynomial-limit` | (9.53) | `literalArtificialCoefficient_tendsto`, `literalArtificialPolynomialValue_tendsto`, `literalArtificialRandomValue_tendsto` |
| `eq:local-graph-limit` | (9.54) | `normalized_literalArtificialTheta_gramVolume`, `normalizedGraphProduct_tendsto` |
| `eq:local-coeff-limit` | (9.55) | `literalArtificialCoefficientNorm_tendsto` |

The exterior limits are proved along `lambda_q = q + 1` in the fixed
finite-dimensional spaces, including the Euclidean operator norm.
The sharper uniform rates displayed in (9.51)--(9.52) are not separately
packaged as quantitative inequalities. The coefficient and value limits,
together with bounded convergence for capped loss, give the Section 9.2
deduction through `literalArbitraryFrame_smallBall_deduction_of_endpointGood`.

For outside-measurable random frames, `directBoundaryFrameMinor` and
`literalFrameCoefficient_eq_direct` remove any dependence on a measurable
choice of unitary completion. `RandomFrame.literalRandomFrameConditionalResult_of_packetConcrete`
then supplies the conditional conclusion, with fixed input admissibility,
outside measurability, and fresh-packet independence stated explicitly.
