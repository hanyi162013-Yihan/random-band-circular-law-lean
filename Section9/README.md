# BernoulliLinearAlgebra — 第 9 节的确定性线性代数

本库对应 Yi Han 的
[*The circular law for non-Hermitian random band matrices: optimal bandwidth,
periodic profile and discrete law*](https://arxiv.org/abs/2609.01295v1)
**v1（2026-09-01）**：§9.1.3、§9.3–9.5 的确定性证明链，以及 Lemma 7.8
的 Gram volume / exterior operator 比较。不是整个第 9 节的完整形式化。

编号、源码注释和逐公式对照均以该版本为准。章节与公式定位见
[PAPER_REFERENCES.md](PAPER_REFERENCES.md)，详细定理与假设见
[FORMALIZATION_MAP.md](FORMALIZATION_MAP.md)。

## 入口与验证

本目录是仓库根 Lake 工程中的一个库，使用 Lean/mathlib `v4.33.0`。
从仓库根目录运行：

```sh
lake build BernoulliLinearAlgebra
lake env lean Section9/AxiomAudit.lean
```

`lake build` 同时构建仓库的 Section4 和 Section9 库。
入口为 [BernoulliLinearAlgebra.lean](BernoulliLinearAlgebra.lean)，保留
`import BernoulliLinearAlgebra` 和原有子模块名称，方便其他任务复用。
首次安装与缓存说明见[根 README](../README.md#build)；日常核查无需
`lake update`。

源文件不含 `sorry`、`admit` 或自定义 `axiom`。审计打印主要结论的
公理依赖；标准基础公理不等于论文的外部估计。Lean 检查通过也不能替代
对非形式化陈述与 Lean 定理之间对应关系的审查。

## 论文结果与覆盖范围

| 新版论文位置 | 已形式化内容 | 主要入口 |
|---|---|---|
| Lemma 7.5，证明 §9.1.3 | 原始单位权重三块 mask 的 matching 展开、全子式出现、Cauchy–Binet、任意谱参数的系数平移及显式有限常数比较 | `threeBlockTerminalCoefficientOnPacket_concreteComparison` |
| Lemma 7.6，证明 §9.3 | 实际周期块矩阵、两次消元、Floquet 符号、packet split，以及奇异接口的无分母多项式延拓 | `concrete_block_floquet_identity`、`polynomialClearedSignedCompoundTrace_listOfFn_eq_physical` |
| Proposition 9.3，§9.4 | 字面五块 `K_Theta` 的两种消元、`D_Theta = det(Theta_11) p_Q` | `concreteKTheta_det_eq`、`threeBlockConcreteKPolynomialShifted_det_eq` |
| Corollary 9.4，§9.4 | 三块物理行的统一缩放与完整系数向量缩放 | `scaledGlobalConcreteKPolynomial_det` |
| §9.4.1 | 一般阶 Jacobi/Hodge 互补子式、compound 范数界、移除端点矩阵 `E` | `compound_inverse_norm_eq_of_isUnit`、`endpointFactor_conditioning_of_hodgeBounds` |
| Lemma 7.7 的确定性核心，证明 §9.5 | boundary graph Gram 恒等式、chart 扰动与延拓、显式常数系数范数双向比较 | `globalBoundaryCoefficientNorm_bounds_fullyInstantiated` |
| Lemma 7.8，式 (7.47) | Gram volume 与最大 exterior operator norm 的双向界，常数恰为 `2^W` | `gramVolume_operatorCompound_two_sided_twoBlock_two_pow` |

还证明了全局字面行列式只有 squarefree monomial；定理
`globalBoundaryDetPolynomial_eq_squarefreePolynomial` 从完整系数向量
重建整个多项式，并非只抽取部分系数。

## 已消除的接口与保留的数学假设

最终 concrete 定理在库内构造实际 mask、Floquet 消元和 Jacobi
互补子式，不要求调用者提交 `MaskExpansionCertificate`、
`FloquetEliminationData` 或 `ComplementaryMinorCertificate`。
抽象版本仍作为可复用 API 保留。

仍显式保留以下条件：

- unit-locus Floquet 公式要求右接口块可逆；奇异接口由另一个
  denominator-cleared 定理覆盖，不把 total inverse 在奇异处当成多项式。
- boundary comparison 要求端点块 `C_L,B_R` 及完整 `Theta` 可逆，
  但不要求 `Theta_11` 可逆。后者只在局部 chart 证明中使用。
- 定量端点版本接收逆行列式界 `D` 和各阶正向 compound 范数界
  `L`；由已证明的 Jacobi/Hodge 恒等式推导逆 compound 界。
  此处 compound 使用 Frobenius/HS 范数，不能直接冒充 operator 范数界。

## 显式常数与尚未覆盖的部分

原始单位权重多项式的 terminal 常数是

```text
threeBlockConcreteComparisonConstant z
  = threeBlockZeroComparisonConstant * threeBlockTranslationFactor z.
```

前一个因子来自有效 matching 的有限基数，后一个来自对角平移的三角
系数变换。全局 boundary 常数为上述常数乘以
`endpointExteriorConstant CL BR`；给定 `D,L` 时可改用
`max 1 (max L (D * L))` 作为端点因子。

以下内容**尚未由本库作为论文完整结论证明**，不是新增公理：

- 将这些有限常数统一控制为论文的 `exp(C W log W)`，并核对 `C`
  对 `K,K_z,c_*,C_*` 的依赖；
- 将原始单位权重变量的系数范数比较实例化到全部逐项确定性权重
  `a_e` 的版本。已有统一物理行缩放恒等式，但不能把它视为完整
  weighted-profile 系数范数定理；
- 将 Gram determinant 精确识别为论文写出的奇异值乘积的单独定理；
- 端点事件的概率、Cook/Nguyen 估计、RRQR、small-ball、概率版
  Proposition 7.3 / Corollary 7.9，以及 §9.2 的任意 frame 论证。

因此，“concrete / fully instantiated”专指本库所陈述的确定性定理中
不再遗留 mask、terminal 或消元 certificate，**不表示上述范围外工作
已经完成**。本库没有把 Cook、Nguyen 或 RRQR 当作新公理导入。
