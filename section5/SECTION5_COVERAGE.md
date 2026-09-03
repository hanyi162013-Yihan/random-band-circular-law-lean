# Section 5：形式化覆盖与输入边界

本轮高斯输入迁移：固定原子 indicator 终点已改为内部构造 Ginibre 参考结论，
不再接收 BC12 参数；新增 taper 适配只保留目标 taper 的 LSV、计数、局部比较三项。
这批修改已在 `c4e8078` 的 Section 5 云端任务通过构建与 240 项公理审计，
见 [本章验证记录](SECTION3_INTEGRATION.md) 及 [全篇迁移状态](../GAUSSIAN_INPUT_MIGRATION.md)。

历史版本状态：总入口（4079 个构建任务）、65 个新增模块的严格重查、公理审计、15 个边界测试及全部 118 个 Section 5 模块的内核重放均已通过。

本文对应本地 combined manuscript 的 Section 5。Section 6 的 Gaussian-profile
论证不在本轮范围。Section 3、Section 4 的结果按用户要求作为预先输入。

GitHub 发布目录通过父项目复用已有 Section 4 和 replacement；只附上尚未在父项目
出现的五个小型 Section 3 支持模块。已有 Theorem 3.1 的独立 LSV 项目与仍保留的
其他 Section 3 输入，详见 [UPSTREAM_INPUTS.md](UPSTREAM_INPUTS.md)。

## 最终入口

- `indicator_original_real_full_of_section34`：indicator 权重、原始实 IID 数组。
- `indicator_complex_full_of_quantitative_section34`：indicator 权重、复平面有界密度。
- `tapered_original_real_full_of_section34`：实际采样、归一化的多项式 taper，原始实 IID 数组。
- `tapered_complex_full_of_quantitative_section34`：同一 taper，复平面有界密度。

`SourceRealFullEndpoints` 的两个 `*_of_source_assumptions` 入口直接接收已有 Section 3
`AtomMomentAssumption21` 记录和原始一维密度上界；二阶矩可积性和单位二阶矩由该记录
推出，不再作为重复输入。

输出 `Section5Conclusions` 包含：几乎处处谱参数下的实际对数势概率收敛、所有有界连续
实测试函数的 ESD 概率收敛、归一化 Hilbert–Schmidt 范数紧性，以及同一个满测度谱参数集
上每个矩阵尺寸的几乎处处行列式非零。不是仅有抽象压力或 supplied replacement 结论。

`section5_spectral_difference_under_coupling` 将任意两个这样的输出转成谱测试积分之差
趋于零；耦合的两个边缘分布须分别等于规范全序列样本空间的 `infinitePi` 分布，
不要求两个模型之间独立。`section5_spectral_difference_on_product` 给出直接可用的
独立乘积实现。这里没有声称已证明只约束逐尺寸边缘、允许任意时间相关性的更一般
ESD 耦合定理；对数势之差另有逐尺寸三角耦合版本。

### “谱分布之差趋零”的精确含义

记 `μ_N^X`、`μ_N^Y` 为两个实际矩阵的经验谱测度，`μ_disk` 为单位圆盘上的归一化
面积测度。在上述模型假设与样本空间条件下，对每个固定的有界连续实函数 `g`，已证明

\[
\int g\,d\mu_N^X \xrightarrow{\mathbb P} \int g\,d\mu_{\rm disk},\qquad
\int g\,d\mu_N^X-\int g\,d\mu_N^Y \xrightarrow{\mathbb P} 0.
\]

这里是有界连续测试函数意义下的概率收敛，不是总变差距离收敛。实际对数势
`N⁻¹ log ‖det(X_N - z I)‖` 的概率极限则在 Lebesgue 几乎处处的 `z` 上等于
`circularLogPotential z`；能量紧性与所需行列式非零事件均由本项目提供。

## 允许的上游输入究竟是什么

Section 3 使用 `Section3IndicatorAnchorsTri` 的两次短环锚定：

1. 目标尺寸的短分支；长分支填入确定目标值，因此没有预先假设全序列圆律。
2. 长分支上用于校准的 mesoscopic 辅助环；非活动分支同样填入目标值。

Section 4 使用两份 `QuantitativeSection4PressureInput`，分别作用于校准环和最终环。
每份只有四个有限尺寸条件：原始行列式/随机压力差的 `L¹` 可积性与显式界，以及各压力
的 `L²` 可积性与显式最大波动界。没有渐近压力极限、谱极限、replacement 假设、
逆范数恒等式或 taper 的统一常数假设。

实分支的 `OriginalRealSection34Inputs` 把这两份有限条件和两个短环锚点放在原始实
IID 数组上。其 `complexify` 定理证明输入搬运；最终结论又回到同一实样本空间。
实原子不被假设具有复平面密度。

校准环保留目标矩阵的同一组权重，但按辅助尺寸重新做循环列索引。它不是目标矩阵的
主子矩阵。实际实现选取 IID 数组中的相应行，证明限制后的 IID 分布，再构造该辅助
循环环；这正是短环结果和实际平均压力之间所用的模型识别。

模型自身仍具有显式的密度/矩条件、归一化权重、带宽增长、非混叠 band-fit 条件及
`0 < δ < γ < 1/8`。Section 5 使用所需的一、二阶可积性及二阶矩界；中心化、单位二阶矩
和三阶矩条件中属于 Section 3 锚点的内容没有被声称在这里重新证明。

对 taper，原 `TaperShortRingSource` 从 Section 3 的原始估计构造实际 taper 短环
结论，而不是把 taper 的极限本身作为该层的假设。具体的
`Section3TaperAnalyticInputs` 包含 Theorem 3.1 最小奇异值、Proposition 3.4 所有截断
尺度的计数、Lemma 3.5 局部比较，以及 Section 3 原来使用的 dense/BC12 比较结果。
源原子的中心化和行二阶矩由 `LiteralSourceMoments` 自动生成；最大方差、内带、指数
余量、可选参数和实际 cutoff 均在本项目证明。主终点仍用短环锚点包装接收这些结果，
该适配说明此包装如何从允许的原始 Section 3 结果得到。此历史适配已编译通过。
本轮的 `TaperVerifiedGinibre` 进一步从实际 Ginibre 分布与 BBV 构造上述四项高斯
结论；新入口 `tapered_short_ring_of_section3_estimates_withoutBC12` 的记录
`Section3TaperNonGaussianInputs` 只有目标矩阵的三项估计。尚未声称已证明这些 taper
估计，也没有把趋于零的权重下界改成统一正常数。该新适配已通过本轮云端验证。

## 原文逐项对应

以下声明均位于 `CircularLawSections56.Section5`，除特别注明的本地 Section 4 API。

| 原文步骤 | 对应声明或模块 | 本轮覆盖 |
|---|---|---|
| `eq:cell-decomposition`，实际 `B * Q` | `GenericPhysicalCell`、`GenericCenteredFreshCell` | fresh/outside 保测重组，保持中心 `E log ‖B‖` |
| `eq:det-versus-random-pressure` | `LiteralPhysicalDeterminantSeam`、`QuantitativeSection4Inputs` | 实际 determinant/FreshZ 识别，有限上游估计的接入口 |
| `eq:random-versus-mean-pressure` | `integral_abs_randomFiniteSignedMax_sub_mean_le_maxCenteredAbs` | 随机最大值到坐标期望最大值，不混淆两者 |
| `eq:mesoscopic-calibration` | `literal_uniform_mesoscopic_calibration` | 整个整数区间的有限上确界，非仅选定的一个长度 |
| `eq:cell-lower`、`eq:cell-upper` | `literalRandomOutsideExteriorCell_oneCellInputs_of_projective`、`GenericPhysicalCell` | 两侧界、可积性及随机 outside 中心化 |
| `eq:pressure-lift-r` | `literal_physical_telescope_uniform_atom` | 真实 chronological IID 矩阵乘积，所有外幂次数 |
| `eq:pressure-lift-max` | `literal_max_pressure_lift_uniform` | 取最大值后损失无 degree 或 cell-count 因子 |
| `eq:global-pressure-multiples` | `literal_global_pressure_uniform_in_cells` | 对全部正整数 cell-count 和全部 admissible cell 长度一致 |
| `eq:inverse-exterior-identity` | `norm_compound_inverse_eq_complement`、`literal_exterior_row_inverse_eq_complement_ae` | 精确 Euclidean operator norm 等式；零次与最高次外幂也包括在内 |
| `eq:one-row-log-cost` | `literal_row_forward_inverse_uniform`、`tapered_real_row_forward_inverse_uniform` | 两个实际正对数期望之和，统一 `C log(eW)` |
| `eq:pathwise-remainder` | `matrix_pathwise_remainder`、`LiteralAtomPressure` | 实际矩阵路径、AE 可逆与产品可积性 |
| `eq:balanced-cell-division` | `balanced_cell_division_spec`、`paperTransferReady_geometry`、`eventually_paperBandCellCount_ge_on_long` | 真正的整数除法、cell-length、剩余行数及长分支的 cell-count 发散 |
| `eq:mean-pressure-remainder` | `literal_row_increment_uniform_atom`、`GenericLiteralModel` | 实际 IID 平均压力逐行追加及终端端点识别 |
| `eq:target-mean-pressure` | `literalModel_completedSection4Data_of_atom_log`、`completedSection4_literalCertificate` | 所有比例与归一化余项自动消失 |
| `eq:final-seam`、`eq:final-pressure-fluctuation` | `QuantitativeSection4PressureInput`、`LogarithmicSection4Bounds` | 两份有限上游界，显式推出统一尺度界 |
| `eq:indicator-logdet-goal` | `literal_canonical_profile_endpoint_of_section34` | 原始未填充矩阵，几乎处处谱参数 |
| `eq:HS-tightness-indicator` | `literalIndicatorMatrix_expected_energy_one`、`literal_indicator_normalized_hilbertSchmidt_tight` | 单位二阶矩时精确能量期望等于一；紧性内部证明 |
| replacement 与圆律 | `CircularLawFromPotential`、`WeakCircularLaw`、最终入口 | 本地已证明 replacement；比较模型的能量和对数势不再外加 |
| 两模型 ESD 之差趋零 | `section5_spectral_difference_under_coupling` | 所有有界连续实测试函数；规范全序列边缘的任意耦合及独立乘积实现 |
| `eq:tapered-discrete-bounds` | `PolynomialTaperProfile.mass_linear_bounds`、`weight_lower_polynomial`、`weight_inner_linear` | 从实际 profile 条件推出离散常数，无 supplied normalizer bounds |
| taper 方差识别 | `taperedMatrix_expected_entry_eq_varianceMatrix` | 实际矩阵各项二阶矩等于定义的双随机方差数组 |
| 实际模型有效带宽 | `taperedMatrix_maxExpectedEntry_eq_maxWeight`、`taperedMatrix_effectiveBandwidth_comparable` | 先证明实际最大项二阶矩等于最大权重，再推出其倒数与 `W` 可比 |
| 内带 `W' = ⌊W/2⌋` | `varianceMatrix_inner_halfband_lower`、`effectiveBandwidth_comparable`、`eventually_taper_high_band_margin` | floor、内带常数、有效带宽及指数余量减半 |
| taper 短环的 Section 3 重用 | `tapered_short_ring_of_section3_estimates` | 从命名的 Section 3 原始估计重新推出实际 taper 的短环极限；矩条件与 cutoff 搬运内部完成 |
| taper isolated monomial 损失 | `PolynomialTaperProfile.selected_amplitude_exponential_lower` | 实际 `2W` 个幅度之积的 `exp(-Cκ W log(eW))` 下界 |
| taper 统一常数 | `RealQuantitativeSection4PressureInput.toCompleted`、复数对应版本 | 允许 `c₀ = c₀(W)`；没有把它当固定正数 |
| taper 完整推论 | 两个 `tapered_*_full_*` 入口 | 实、复两分支及四项最终结论 |
| 非空具体例子 | `triangleTaperProfile` | 三角 taper 的支撑、上下界与全局 BV 均证明 |

## 比较模型与逻辑审计

内部比较模型是 IID 均匀圆盘点组成的对角矩阵。其特征值、能量、对数势和谱积分极限
均已在本项目证明，并复用本地 Section 3 的圆盘势积分公式。这提供所需 replacement
参照，不需要把 Ginibre 的极限额外塞入最终 Section 5 定理。
另须区分：历史 taper 短环适配接收 Section 3 原有的 dense/BC12 比较输入；本轮新
适配将高斯侧改为内部构造。两者都不是给 Section 5 replacement 额外指定未证明的
比较模型；后者仍使用上面已经构造的均匀圆盘对角矩阵。

`AxiomAudit.lean` 保留逐个关键入口的依赖输出；`FullSection5AxiomAudit.lean` 自动遍历
整个公开 Section 5 命名空间，检查定义和定理的传递公理依赖，只允许 `propext`、
`Classical.choice`、`Quot.sound`。普通 theorem 前提不属于公理；此审计不能、也不声称
替代对上述 Section 3/4 输入边界的逐项阅读。

## 验证记录

本轮连续工作开始：2026-09-02 06:21:05 UTC。

- 总入口于 10:35:59 UTC 前完成编译，4079 个构建任务，退出码 0。
- 总构建日志：`/tmp/section5-verified-root-build.log`。
- 224 个不同关键声明的逐项公理审计通过。
- 穷尽审计通过：1561 个公开 Section 5 声明，其中 1215 个为定理，
  只使用 `propext`、`Classical.choice`、`Quot.sound`。
- 15 个边界回归证明以警告视为错误的模式通过，无错误或警告。
- 65 个新增模块的严格重查全部通过，警告视为错误，退出码 0；
  完成于 12:06:29 UTC 前，进度日志为 `/tmp/section5-strict-progress.log`。
- 额外内核重放于 13:35:56 UTC 前全部通过：117 个源模块及 Section 5 总入口，
  共 118 个模块；程序退出码 0，源文件、模块名称与数量均完整核对。
- 最终整轮公理审计和 15 个回归证明再次全部通过；随后总入口复查再次成功，
  4079 个构建任务。以上最终检查于 13:43:29 UTC 前已确认完成。
- 最终进度日志：`/tmp/section5-final-audit-progress.log`、
  `/tmp/section5-kernel-progress.log`；最终总构建日志：
  `/tmp/section5-final-root-build.log`。详细审计、严格检查与内核日志位于
  `/tmp/section5-validation.wfYBa5`。
- 原始项目缓存约 557 MiB，较本轮开始的 266 MiB 增加约 291 MiB；
  未下载或复制 mathlib、Lean 工具链或大体积依赖。数学核验已持续超过 7 小时。
- 原始本地清单记录 144 个 Lean/配置/验证文件的 SHA-256；本发布目录的
  `SOURCE_SHA256SUMS` 另行覆盖仓库相对路径配置及五个补充支持模块。
  发布适配不改变数学证明文本。

`verify_section5.sh` 提供顺序、本地缓存复用的验证流程，分为 `build`、`strict`、
`audit`、`kernel` 阶段。`Section5ValidationModules.txt` 列出本轮需要无警告严格重查的
新增模块。`kernel` 阶段用随 Lean 安装的 `leanchecker` 在单进程、单工作线程内重放
全部 Section 5 模块的声明，并核对源文件与总入口的完整覆盖；这是额外的 Lean 内核
检查，不是另一个独立逻辑系统的验证。它不使用 `--fresh`，不会重建或下载 mathlib。
所有验证日志写入指定临时目录。
