# 论文—Lean 对照表

本表对照 [arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1)
（2026-09-01）的 §9.3–9.5 与 §9.1.3。主要陈述在 Lemmas 7.5–7.8，
以及 Proposition 9.3、Corollary 9.4。章节与公式的定位见
[文献索引](PAPER_REFERENCES.md)。状态含义：

- `definition`：论文对象的字面定义；
- `generic proved`：可复用的抽象接口及其一般推论；
- `concrete proved`：所列 Lean 定理的矩阵、原始单位权重 mask 或排序
  已实例化，不要求调用者再传 certificate；不自动表示原文全部权重、
  常数依赖或概率结论已覆盖。

抽象 certificate 结构仍保留为 reusable API，但下表的最终 concrete
定理不依赖调用者提供 `MaskExpansionCertificate`、
`FloquetEliminationData` 或 `ComplementaryMinorCertificate`。

## Lemma 7.5：all-minor coefficient estimate 的确定性核心

陈述为式 (7.24)，证明在 §9.1.3。以下 concrete packet 的每个 fresh
变量以系数 1 进入矩阵；完整逐项权重及统一渐近界的范围限制见文末。

| TeX 标签/步骤 | Lean 定义或定理 | 状态 |
|---|---|---|
| 式 (7.11)–(7.12) 的七块 path mask、`Delta(x)` 与 `Emb_O(Q)`，取原始单位权重变量 | `threeBlockFresh`, `threeBlockDelta`, `threeBlockEmb`, `threeBlockH` | definition |
| 实际三块 determinant polynomial | `threeBlockDetPolynomial`, `eval_threeBlockDetPolynomial` | concrete proved |
| (9.44) `eq:local-monomial-minor` 的 Leibniz/matching 展开 | `threeBlockDetCoefficient_zero_eq_matchingExpansion`, `threeBlockDetCoefficient_zero_eq_pivot_det` | concrete proved |
| 有效 matching 的系数等于互补 outer minor（模相位） | `norm_threeBlockDetCoefficient_zero_eq_squareMinorValue` | concrete proved |
| 无效 matching 的系数为零 | `threeBlockDetCoefficient_zero_of_not_valid` | concrete proved |
| 每个 square minor 至少出现一次 | `threeBlockMatchingMinorIndex_surjective` | concrete proved；Hall matching 已构造 |
| (9.45) `eq:local-coefficients-to-minors` 的实际有限能量比较 | `threeBlockFullCoefficientEnergy_eq_validEnergy`, `gramVolume_le_threeBlockDetCoefficientNorm_zero`, `threeBlockDetCoefficientNorm_zero_le_sqrtCard_mul_gramVolume` | concrete proved |
| (9.46) `eq:local-all-minor-CB` | `all_minors_cauchy_binet`, `threeBlockMinorL2Norm_eq_gramVolume` | concrete proved |
| 零位移 terminal comparison | `threeBlockDetCoefficientNorm_zero_comparison`, `threeBlockTerminalCoefficientOnPacket_zero_comparison` | concrete proved |
| 三个对角块的 fresh shift list 无重复 | `threeBlockDiagonalShifts_nodup` | concrete proved |
| 任意 `z` 的精确多项式平移 | `threeBlockDetPolynomial_eq_translatePolynomialList` | concrete proved |
| 任意 `z` 的逐坐标系数恒等式 | `threeBlockDetCoeffVector_eq_translateCoeffList` | concrete proved |
| 平移前后系数范数的双向界 | `threeBlockDetCoefficientNorm_shift_lower`, `threeBlockDetCoefficientNorm_shift_le` | concrete proved |
| Lemma 7.5 的原始单位权重、显式有限常数、任意 `z` 版本 | `threeBlockTerminalCoefficientOnPacket_concreteComparison` | concrete proved；无 mask certificate |

最终显式常数为

```text
threeBlockConcreteComparisonConstant z
  = threeBlockZeroComparisonConstant * threeBlockTranslationFactor z.
```

其中 `threeBlockZeroComparisonConstant` 使用有效 matching 的有限基数，
`threeBlockTranslationFactor` 是所有对角平移的显式三角变换因子。

## 第 9.3 节：Lemma 7.6 的周期块矩阵与 Floquet 行列式

Lean 用 `Fin (m+1)` 表示站点，因此假设 `0 < m` 对应至少两个周期
站点；这是与 TeX 站点数记号的重参数化。

| TeX 标签/步骤 | Lean 定义或定理 | 状态 |
|---|---|---|
| (9.56) `eq:local-floquet-recurrence` | `physicalCyclicMatrix` | definition |
| (9.59) `eq:local-floquet-augmented-system` | `explicitCyclicAugmented`, `rawCyclicAugmented` | definition |
| augmented top/bottom equations | `explicitCyclicAugmented_apply₁₁`, `_apply₁₂`, `_apply₂₁`, `_apply₂₂`, `rawCyclicAugmented_apply` | concrete proved |
| (9.62) `eq:local-floquet-first-elimination` | `explicitCyclicAugmented_det` | concrete proved |
| raw site order与 regrouped augmented matrix 一致 | `reindex_rawCyclicAugmented_eq_explicit`, `explicitCyclicAugmented_det_eq_raw` | concrete proved |
| (9.64) `eq:local-floquet-factor-L` | `rawCyclicAugmented_local_factorization`, `siteBlockDiagonal_det`, `rawCyclicAugmented_det` | concrete proved |
| (9.68) `eq:local-floquet-second-elimination` | `rotatedPeriodicTransfer_det_chronological`, `rawPeriodicTransfer_det` | concrete proved |
| ordering sign 属于 `{±1}` | `floquetSign_spec`, `floquetSign_sq` | concrete proved |
| (9.57) `eq:local-block-floquet` | `concrete_block_floquet_identity` | concrete proved；不接收 elimination certificate |
| (7.39) `eq:local-floquet-packet-split` | `concrete_block_floquet_packet_split`, `concrete_block_floquet_first_three_split` | concrete proved |
| Sylvester `det(I-AB)=det(I-BA)` | `det_one_sub_transfer_comm` | generic proved |
| 外幂乘法与 `det(I-A)` 展开 | `compound_mul`, `det_one_sub_eq_signedCompoundTrace` | generic proved |
| (9.69) `eq:local-floquet-cleared-one-step` | `clearedStepCompound`, `clearedStepCompound_eq_det_smul_compound_stepTransfer` | concrete proved；等式在 unit locus，左侧定义无分母 |
| (9.70) `eq:local-floquet-polynomial-extension` 的 unit-locus 形式 | `polynomialClearedSignedCompoundTrace_eq_detProduct_mul_floquet` | concrete proved；明确要求各 `det B` 为 unit |
| 奇异接口的全局延拓 | `polynomialClearedSignedCompoundTrace_companionStepList_eq_physical`, `polynomialClearedSignedCompoundTrace_listOfFn_eq_physical` | concrete proved；任意 `B` |

这里没有把 total inverse 在奇异点误当作多项式。奇异处使用由互补 minor
直接定义的 `clearedInverseCompound` 和 `clearedStepCompound`，其全局
trace 与实际物理周期行列式相等。

## 第 9.4 节：Proposition 9.3、Corollary 9.4

| TeX 标签/步骤 | Lean 定义或定理 | 状态 |
|---|---|---|
| (9.71) `eq:local-Theta-blocks`, (9.73) `eq:local-STheta` | `transferCoordinateMap`, `boundaryGraphS` | definition |
| (9.82) `eq:local-S-action` | `transferCoordinateMap_mul_frame`, `boundaryGraphS_eq_transferCoordinateMap` | concrete proved |
| (9.74) `eq:local-E` | `endpointFactor` | definition |
| (9.76) `eq:local-HTheta` | `concreteHTheta`, `threeBlockH_reindex_eq_concreteHTheta_shifted` | concrete proved |
| 字面五块 (9.78) `eq:local-KTheta` | `concreteKTheta`, `globalConcreteKPolynomial` | definition |
| unit interface 上的第一次消元 | `concreteKTheta_det_eq_boundaryCompatibility_of_units` | concrete proved |
| boundary exterior 定义及 Sylvester 方向 | `polynomialClearedBoundaryTrace`, `polynomialClearedBoundaryTrace_eq_detProduct_mul_compatibility_of_units` | concrete proved |
| (9.79) `eq:local-K-first-elimination`，包括奇异 `B_L,B_C,B_R` | `polynomialClearedBoundaryTrace_boundaryCompanionSteps_eq_concreteKTheta_det` | concrete proved；无接口可逆假设 |
| endpoint Schur complement 等于 `H_Theta` | `concrete_schurComplement_eq_HTheta` | concrete proved |
| `det G_Theta = det Theta_11` | `endpointPivot_det` | concrete proved，无需 `Theta_11` 可逆 |
| (9.77) `eq:local-double-elimination` 的数值形式 | `concreteKTheta_det_eq` | concrete proved |
| `D_Theta = det Theta_11 * p_Q` 的任意 shift 多项式形式 | `threeBlockConcreteKPolynomialShifted_det_eq` | concrete proved |
| 对应 coefficient vector/norm 缩放 | `threeBlockBoundaryKCoeffVectorShifted_eq_smul`, `threeBlockBoundaryKCoefficientNormShifted_eq` | concrete proved |
| 全局 exterior 表达式与字面 `K` 的逐点评价一致 | `eval_globalBoundaryDetPolynomial_eq_polynomialClearedBoundaryTrace` | concrete proved；接口可奇异 |
| (9.83) `eq:local-boundary-scaling`，只缩放 `3W` 个物理行 | `scaledGlobalConcreteKPolynomial_det`, `scaledGlobalBoundaryCoeffVector_eq_smul`, `globalBoundaryCoefficientNorm_eq_inv_mul_scaled` | concrete proved |
| 全局 determinant 仅有 squarefree monomial | `hasSquarefreeSupport_globalBoundaryDetPolynomial` | concrete proved；任意 boundary matrix |
| 全局完整系数重建 | `globalBoundaryDetPolynomial_eq_squarefreePolynomial` | concrete proved |

## 第 9.4.1 节：compound、Hodge–Jacobi 与去除 `E`

| TeX 标签/步骤 | Lean 定义或定理 | 状态 |
|---|---|---|
| (9.85) `eq:local-compound-minors` | `compound_apply`, `compoundEnergyReal_eq_sum_normSq` | generic proved |
| (9.84) `eq:local-compound-sum` | `det_one_add_gram_eq_sum_compoundEnergy_byDegree`, `gramEnergy_eq_sum_compoundEnergyReal` | generic proved；字面 finite degree sum |
| 外幂乘法的 HS 次乘性 | `compound_frobenius_norm_mul_le` | generic proved |
| 一般阶 Jacobi 互补 minor | `det_inv_topLeft_eq_det_bottomRight_div_det_of_isUnit`, `complementaryMinorCertificate_of_isUnit` | concrete proved；certificate 在内部构造 |
| `‖compound k E⁻¹‖ = ‖det E‖⁻¹ ‖compound (n-k) E‖` | `compound_inverse_norm_eq_of_isUnit` | concrete proved；调用者不传 certificate |
| (9.86) `eq:local-E-compounds` | `endpointFactor_conditioning_of_hodgeBounds` | concrete proved；由 `D,L` 内部推出逆 compound 界 |
| (9.87) `eq:local-ES-two-directions` | `compound_left_mul_le`, `compound_le_left_mul` | generic proved |
| (9.88) `eq:local-remove-E` | `gramVolume_remove_left` | generic proved，并由 `concrete_endpoint_boundary_volume_on_chart_of_hodgeBounds` 具体调用 |

完全无定量事件输入时，`endpointFactor_exactConditioning` 使用显式有限常数
`endpointExteriorConstant CL BR`。论文事件版本使用
`max 1 (max L (D * L))`。

## 第 9.5 节：Lemma 7.7 的确定性 coefficient–volume 核心

Lemma 7.7 的陈述为式 (7.46)；下表证明显式有限常数版本，不宣称已
得到原文全部参数统一性。末行另对应 Lemma 7.8 的式 (7.47)。

| TeX 标签/步骤 | Lean 定义或定理 | 状态 |
|---|---|---|
| (9.89) `eq:local-MN` | `boundaryFrameM`, `boundaryFrameN` | definition |
| `det M(Theta)=det Theta_11` | `boundaryFrameM_det` | concrete proved |
| `S(Theta)=N(Theta)M(Theta)⁻¹` | `boundaryGraphS_eq_mul_inv` | concrete proved |
| (9.90) `eq:local-graph-Gram` | `boundaryFrames_gram` | concrete proved |
| (9.91) `eq:local-graph-identity` | `explicit_boundary_gram_determinant`, `explicit_boundary_gram_determinant_normSq` | concrete proved |
| 平方根后的 `|det Theta_11|` 精确消去 | `boundaryGraph_gramVolume` | concrete proved |
| chart 上字面 coefficient norm 的精确缩放 | `globalBoundaryCoefficientNorm_eq_on_chart` | concrete proved |
| chart 上 coefficient–volume 比较 | `concrete_endpoint_boundary_volume_on_chart`, `concrete_endpoint_boundary_volume_on_chart_of_hodgeBounds` | concrete proved |
| (9.92) `eq:local-Theta-approx` | `exists_scalarPerturbationSequence`, `invertibleUpperLeftChart_sequentiallyDenseAt` | concrete proved |
| boundary polynomial 的逐系数连续性 | `coeffwiseContinuous_globalBoundaryDetPolynomial`, `continuous_globalBoundaryCoefficientNorm` | concrete proved |
| 任意可逆 `Theta` 的最终比较 | `globalBoundaryCoefficientNorm_bounds_fullyInstantiated` | concrete proved；无 terminal certificate，`Theta_11` 可奇异 |
| 给定 `D,L` 的定量确定性版本 | `globalBoundaryCoefficientNorm_bounds_of_hodgeBounds_fullyInstantiated` | concrete proved；事件及其概率不是本定理结论 |
| 最终 coefficient norm 严格正 | `globalBoundaryCoefficientNorm_pos_fullyInstantiated` | concrete proved |
| Lemma 7.8，(7.47) `eq:local-boundary-volume-vs-exterior` | `gramVolume_operatorCompound_two_sided_twoBlock_two_pow` | concrete proved，常数 `2^(card W)` |

## 最终 concrete theorem 的假设

不再存在需要模型层补齐的 elimination、mask 或 Jacobi certificate。最终
结论保留的假设为：

1. unit-locus Floquet 公式中各右接口块 `det B_j` 可逆；奇异接口使用
   denominator-cleared theorem，不带此假设；
2. boundary comparison 中端点块 `C_L,B_R` 可逆；
3. 定量版本另接收 `D`（逆行列式界）与 `L`（正向 compound 的
   Frobenius/HS 范数界）；事件给出这些输入的步骤不在本库；
4. 全局 boundary relation `Theta` 可逆；不要求 `Theta_11` 可逆。

工程不包含概率论、small-ball、随机事件概率或大规模极限论证。

## 与原文完整结论之间尚未形式化的步骤

- 将有限 matching、平移和 endpoint 常数统一控制为
  `e^{±C W log W}`，并证明 `C` 仅依赖原文允许的
  `K,K_z,c_*,C_*`。现有显式有限常数定理本身不证明这种统一性。
- 从原始单位权重的具体多项式搬运到全部逐项权重 `a_e`，包括对角
  平移与权重界的组合。统一物理行缩放已经证明，但不能据此宣称完整
  weighted-profile 系数范数比较已经实例化。
- TeX 也将 `det(I + Aᴴ A)^(1/2)` 写成奇异值乘积。Lean 使用证明中
  Gram determinant、compound energy 和 exterior operator 形式，并未
  另立奇异值乘积识别定理。

上述步骤不作为公理假设，也不计入已完成范围。它们与已消除的
elimination、mask、Jacobi certificate 是不同层次的问题。概率版
Proposition 7.3、Corollary 7.9，§9.2 / Theorem 7.10 的任意 frame
论证，以及 Cook/Nguyen/RRQR 的引入不属于本次发布。
