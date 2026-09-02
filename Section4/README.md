# CircularLawSection4

这是论文 [arXiv:2609.01295](https://arxiv.org/abs/2609.01295) 的 Section 4
**“Exterior transfer and local density tools”** 的 Lean 4 形式化模块。
本模块与后续章节共用[仓库根工程](../README.md)的 Lake 配置，
源码固定在 Lean/mathlib `v4.33.0`。

以下 **9/9** 指 Section 4 的九个具名结果均已有对应的无洞 Lean 证明主链。
精确的假设与结论以列出的 Lean 定理陈述为准，不代表整篇论文已形式化。
源文件定位为 `main.tex` 第 1240–1878 行；这些源代码行号不是 PDF 页码。

| 论文标签 | 主要 Lean 入口 |
|---|---|
| `lem:row-linearity` | `clearedRowCompanionCompound_eq_affine`, `orderedRowLinearity_with_l2_contraction` |
| `lem:periodic-det` | `paperXSubZI_det_eq_clearedSignedCompoundTrace`, `paperShiftedScalarTransfer_det_eq_leftEdge_div_rightEdge` |
| `lem:singleton-word` | `ResetWord.arbitrary_singleton_domain_word`, `orderedCoefficient_arbitrarySingletonCertificate` |
| `lem:isolated-monomial` | `exists_paperIndicatorFreshZ_isolatedFullMonomial`, `exists_paperIndicatorFreshZ_isolatedFullMonomial_logScale` |
| `lem:multiaffine` | `openSmallBall_topCoeff_le`, `iid_complex_positiveLogLoss_of_directionalDensity` |
| `prop:fresh-closure` | `complex_paperIndicatorFlatFreshZ_absLog_L1_withDensity`, `complex_paperIndicatorFlatFreshZ_absLog_L1_withDirectionalDensity`, `complex_paperIndicatorFlatFreshZ_joint_absLog_condExp_withDensity` |
| `lem:projective` | `exists_paperProjectiveFreshVector_complex_integral_log_ge_withDensity_andSecondMoment`, `exists_paperProjectiveFreshVector_real_integral_log_ge_of_intervalBound_andSecondMoment` |
| `lem:operator-affine` | `complex_paperIndicator_operatorAffine_memLp_two_and_integral_sq`, `paper_real_iid_operatorAffine_absLog_L2`, `complex_paperIndicator_operatorAffine_absLog_L2_directional` |
| `prop:pressure-concentration` | `integral_max_complex_paperIndicatorOpenPressure_le_auto`, `integral_max_real_paperIndicatorOpenPressure_le_auto`, `integral_max_directional_paperIndicatorFlatOpenPressure_le_auto` |

详细的假设、中间声明、证明修正和源文件行号对应见
[FORMALIZATION_MAP.md](FORMALIZATION_MAP.md)。

## 已形式化的证明主干

- `Exterior.lean`
  - 用 `k` 阶 minors 构造 compound matrix，也就是
    `exteriorPower.map k A` 的坐标矩阵；
  - 证明外幂函子性 `compound k (A * B) = compound k A * compound k B`；
  - 证明
    `det (I - A) = Σ_k (-1)^k tr (wedge^k A)`。
- `RowLinearity.lean`
  - 逐 minor 证明 companion transfer 只改变一行；
  - 证明清分母后的精确整矩阵恒等式
    `β wedge^k T = β K_star - Σ_j c_j K_j`；
  - 包含 `k = 0`，且只使用论文中定义 transfer 所需的 `β ≠ 0`。
- `Periodic.lean`
  - 证明清分母 exterior product 的时间序函子性；
  - 把 cyclic state system 到 `diag(I,I-P)` 的消元表成可核验矩阵证书；
  - 将 physical-to-state 的清分母消元保留为显式行列式接口，并从这两个输入
    推出论文 `lem:periodic-det` 的交错迹形式。
- `PeriodicMatrixCertificate.lean`
  - 用显式 row scaling、坐标重排、左右消元矩阵和 block reduction，把
    physical-to-state 接口加强为真正的矩阵级证书；
  - 从该证书推导旧的行列式等式及完整 periodic determinant identity；
  - 给出通用 unit-pivot Schur constructor，以及任意两步 transfer
    `T₀,T₁` 的端到端循环消元实例。
- `StateCopyElimination.lean`
  - 用 `cyclicStateCopyRelabel` 精确实现论文的周期重标
    `j = i + offset + k`，包括前 `m` 个 copy 与最后 anchor 的显式公式；
  - 显式构造差分/anchor 变换
    `wₙ,ₖ = vₙ,ₖ - vₙ,ₖ₊₁`，证明它与逆变换的行列式都为 `1`；
  - 证明所有 state-identification rows 右乘该逆变换后严格成为
    `[I,0]`，再用行消元得到 `diag(I, physical)`，并直接构造
    `PhysicalEliminationCertificate`。
  - 证明逆差分变换的每个 anchor column 等于同一物理位置所有 copy 上的
    `stateCopyAnchorLift`，从而给出该列的完全闭式。
- `CyclicCompanionRawRows.lean`
  - 把 ordered identification row 逐项展开为相邻 state-copy 基向量之差；
  - 在 raw cyclic 坐标中严格核验每个 early row 就是
    `s_{i+1,k} - s_{i,k+1} = 0`，包括 `k` 为最后早期 copy 时跨到
    anchor copy 的边界情形。
- `StateCopyPhysicalBlockFormula.lean`
  - 将 residual physical block 的每个条目化为末状态行与
    `stateCopyAnchorLift` 的有限点积，并展开为同一物理位置前 `m` 个 copy
    的系数之和再加 anchor 系数；
  - 对 concrete cyclic companion 系统显式求出 equation-row 与 state-column
    三个逆重标，并把 residual 条目精确改写为 supplied `lastRow` 在对应
    `m + 1` 个 raw state copies 上的系数和。
- `CyclicReindexDeterminant.lean`
  - 精确计算 independent equation-row/state-column reindex 对 determinant 的影响；
  - 证明该因子是一个确定性的 `±1`，并给出 ordered cyclic state matrix
    与raw cyclic state matrix 的精确 determinant 关系。
- `StateCopyRowScaling.lean`
  - 构造只作用于 anchor rows 的 block-diagonal `β` 缩放，并精确证明其
    行列式是 `∏ i, β i`；
  - 证明 identification rows 保持不变、physical block 第 `i` 行精确乘
    `β i`，并给出通用及 concrete cyclic companion 的
    `PhysicalEliminationCertificate`；
  - 因左右消元行列式均为 `1`，直接得到
    `det(physical_scaled) = (∏ i, β i) det(state)`，没有额外未追踪符号。
- `CyclicCompanionPhysicalBlock.lean`
  - 将 supplied raw `lastRow` 定义出的 concrete physical matrix 单独命名，
    并证明未缩放 residual block 与它逐项严格相等；
  - 证明 anchor-row 清分母后 residual block 精确等于
    `diagonal β * cyclicCompanionPhysicalMatrix`，从而把每一 physical row
    的 `β i` 因子与同-site `m+1` 个 raw copy 系数和同时显式化。
- `PaperCyclicLastRow.lean`
  - 把论文的 sparse last row 具体定义为 closure 项与
    `βᵢ⁻¹ aᵢₖ` 项的和，因而正确保留 `N = 1` 时两项落在同一
    state-copy 坐标上的退化情形；
  - 证明按 raw equation site 选取的 anchor-row `βᵢ` 缩放逐项消去
    所有逆元，所得 residual block 精确是 closure diagonal 加上
    `i + offset + k = j` 的所有 cyclic band coefficients。
- `PaperCyclicBandReindex.lean`
  - 在 `ZMod N` 上定义论文的 raw closure-plus-band matrix，并显式给出
    raw equation row 与 raw physical column 到 `Fin N` 的两个独立重标；
  - 证明重标后的矩阵逐项严格等于 `paperCyclicPhysicalMatrix`，并由
    `Matrix.det_reindex` 得到其 determinant 是 raw band determinant 乘一个
    显式的确定性 `±1`，同时给出该符号的 spec 与存在形式。
- `CyclicPhysicalDeterminantBridge.lean`
  - 合并 independent cyclic reindex 的确定性符号与 anchor-row 清分母因子，
    直接证明
    `det(physical_scaled) = σ (∏ i, β i) det(raw cyclic state)`；
  - 同时给出显式 `σ = cyclicStateReindexSign` 与存在某个 `σ = ±1` 的两个版本，
    因而这两段周期行列式 bookkeeping 之间不再有隐藏接口。
- `PaperPeriodicDeterminant.lean`
  - 将 raw band row/column 重排、raw cyclic state 重排与全部 anchor-row
    清分母因子合成一个端到端行列式等式；
  - 直接证明 `det(raw band) = σ (∏ p, β p) det(raw cyclic state)`，其中
    `σ` 是两个显式重排符号的乘积，并证明 `σ = ±1`；
  - 消去 raw-band 重排符号时没有使用除法，而是由其 `±1` spec 证明
    `σ_band² = 1`，因此符号 bookkeeping 全部留在可核验的矩阵层。
- `ArbitraryPeriodicElimination.lean`
  - 对任意有限 transfer list 递归构造 unit block-triangular open pivot、
    forward right-hand side、forward solution 与 closure row；
  - 内部证明三个消元恒等式并产出真正的
    `PeriodicEliminationCertificate`，从而得到任意长度的
    `det(system) = det(I - chronologicalProduct)`（空 list 也覆盖）。
- `PaperBandMatrixIdentification.lean`
  - 直接定义论文的循环标量带状矩阵以及字面意义上的 `X_N - z I_N`；
  - 严格核验 raw closure-plus-band matrix 就是该 shifted matrix，并覆盖
    小周期下多个名义 offset 落到同一列的情形；
  - 给出 `x_{i,k}=b_k ξ_{i,k}` 的论文系数版本；对称带宽取
    `m+1=2W`、`center=W`。
- `PaperCyclicMonodromyBridge.lean`
  - 将 raw cyclic state-copy 方程逐项识别为
    `s_{i+1}-T_i s_i=0` 的显式 companion transfer system；
  - 用 Schur complement 归纳证明任意 `N>0`（包括 `N=1`）的循环系统
    determinant 等于确定性重排符号乘 `det(I-P)`；
  - 完成 raw state、chronological monodromy 与既有 recursive system 的
    determinant-level 比较。
- `PaperPeriodicIdentityClosed.lean`
  - 合成 `X_N-zI_N` 识别、state-copy 消元、monodromy 与清分母外幂恒等式；
  - 最终定理 `paperXSubZI_det_eq_clearedSignedCompoundTrace` 的陈述中不再含
    raw-band/state-copy certificate，只保留定义 transfer 所必需的右端系数非零条件；
  - 因此论文周期行列式证明的必要确定性链条已经首尾闭合。
- `PaperCompanionInvertibility.lean`
  - 直接计算 companion transfer 的行列式；在论文的偶数状态维数下得到
    `det T_i = alpha_i / beta_i`；
  - 由左、右边系数非零推出 transfer、每一阶 exterior compound 以及
    清分母 compound 均可逆；
  - 将结论代入 literal 复/实 flat IID 随机矩阵，由有界密度得到几乎处处同时可逆。
- `ResetWord.lean`
  - 忠实的 Boolean particle 模型：`star`、contraction、shift、reset；
  - 构造长度恰为 `d` 的 singleton-domain word；
  - 在 Boolean 支撑模型中显式证明所有其他 particle-number sector 被杀死；
  - 将论文中的指标笔误编码为正确的 `d - r + k` 并证明它小于 `d`。
- `Isolation.lean`
  - 定义抽象交错 exterior trace 中“每个 fresh row 取一个变量”的表达式；
  - 从 arbitrary-frame singleton operator certificate 条件式证明其他 exterior
    degree 精确消失；
  - 从该证书及显式 entry/weight 下界得到
    `bmin^d * entryLower`。
- `ResetMatrixBridge.lean`
  - 将 Boolean occupation states 与 `Set.powersetCard` 外幂坐标连接；
  - 证明 reset/shift 保持长度与 particle number，并把 partial dynamics
    表成具体有限矩阵；
  - 对 diagonal `I = J` 从 `ResetWord.singleton_domain_word` 实际构造
    `SingletonWordCertificate`，不再把矩阵消失关系作为该情形的假设。
- `ArbitraryResetWord.lean`
  - 实现论文的 reset prefix `j_t-t+1` 与无洞 suffix scheduler，并逐步证明
    任意等粒子数 Boolean states `J → I` 的长度 `d` singleton-domain word；
  - 将该 word 提升到 `powersetCard` 坐标矩阵，实际构造任意 `I,J` 的
    `booleanSupport_arbitrarySingletonCertificate`，同时精确杀掉所有其他 exterior
    degrees，不再局限于 diagonal 情形；
  - 将证书继续接到 full-monomial trace extraction，直接得到任意矩阵元
    `B r J I` 的精确模及 `bmin^d * entryLower` 下界。
- `OrderedExteriorPhase.lean`
  - 定义由真实 companion shift 的 `rowFreeCompound` 与
    `rowMinorCoefficient` 组成的 ordered-exterior coefficient family，reset 负号也包含在内；
  - 证明 shift 及 last-row coordinate update 全幺模，从而每个真实单步矩阵的
    任意非零 entry 都具有模 `1`；
  - 给出由 word-operator entry 模相等运输 `SingletonWordCertificate` 的通用定理，
    将相位问题归约为真实 ordered minors 与 Boolean dynamics 的一步零支撑等价；
    该等价已在后续 `OrderedBooleanBridge.lean` 中完全解决。
- `OrderedBooleanBridge.lean`
  - 完整证明 star 步的真实 ordered minor 非零当且仅当 Boolean
    shift 成功，反向证明中还显式识别 surviving minor 为 `1`；
  - 对 reset 步给出 occupation-set 的精确充要刻画，并证明任一非零的
    真实 reset minor 当且仅当 Boolean reset 成功；反向证明把 minor
    精确识别为一个 permutation matrix，因而其行列式为 `±1`；
  - 合并 star/reset 后得到全部真实 ordered coefficients 与 Boolean 一步支撑的
    精确等价，并对任意同次数端点 `I,J` 实际构造
    `orderedCoefficient_arbitrarySingletonCertificate`。
- `OrderedCoefficientL2Contraction.lean`
  - 证明任意每行、每列至多一个非零元且 entry 模不超过 `1` 的复矩阵满足
    Euclidean `l2_opNorm ≤ 1`；
  - 利用 successful Boolean step 的存活域 injectivity 和 ordered 非零支撑桥，
    得到所有 star/reset `orderedCoefficient` 的 `orderedCoefficient_l2_opNorm_le_one`。
- `OrderedRowLinearity.lean`
  - 把清分母 companion compound 的精确仿射展开直接改写成
    `β • orderedCoefficient none + ∑_j c_j • orderedCoefficient (some j)`；
  - 在同一公开定理中同时给出每个真实系数算子的 Euclidean
    `l2_opNorm ≤ 1`，直接形式化论文式 (4.1) 的公式与收缩结论。
- `DeterministicWeightedProduct.lean`
  - 证明若每个单步矩阵的支撑是确定性 partial map 的 graph，且存活权重
    均为单位模，则长 word 乘积中不会发生相消；
  - 从一步 support/unit-phase 数据直接推出 word-operator 模与 Boolean 模型相同，
    并给出生成真实 `SingletonWordCertificate` 的通用 constructor。
- `IsolatedMaxEntry.lean`
  - 在所有 exterior degrees 与坐标对组成的有限依赖和类型上实际取到最大矩阵元；
  - 自动把该最大元送入任意端点 reset word，得到相对于
    `exteriorFamilyMaxEntryNorm` 的端到端 `bmin^d` 隔离下界。
- `OperatorNormMaxEntry.lean`
  - 证明复矩阵的 Euclidean `l2_opNorm` 由显式有限维常数乘最大矩阵元控制；
  - 在所有 exterior degrees 中选择大坐标元，并把它直接接到 Boolean reset word，
    得到相对于最大 `l2_opNorm` 的端到端隔离系数下界。
- `OrderedIsolatedMaxEntry.lean`
  - 使用真实 ordered arbitrary-endpoint singleton certificate，将 exact modulus、
    任意 entry 与最大 entry 隔离下界从 Boolean support 提升到 `orderedCoefficient`；
  - 同时得到相对于 exterior-family 最大 Euclidean `l2_opNorm` 的真实 ordered
    端到端隔离下界，保留显式 family-entry cardinality 因子。
- `PaperIsolatedFreshMonomial.lean`
  - 构造论文实际交错 fresh-block trace `paperIndicatorFreshZ` 的多仿射表示，并
    证明其求值严格等于真实 chronological exterior product；
  - 将 ordered singleton word 直接识别为该多项式的满次数系数，给出相对于
    exterior-family 最大 `l2_opNorm` 的显式隔离下界，并证明谱平移不改变该系数；
  - 同一结论已落实到 literal flat random-matrix sample，同时证明改变未选原子
    不会改变冻结多项式。
- `ProjectiveCoordinates.lean`
  - 对有限复 Euclidean space 内部选择大坐标，并证明两个单位向量存在坐标乘积
    至少为显式 `card⁻²`；
  - 另给出完全基于有限矩阵元与输入坐标的 `card⁻³` 版本，避免条件化应用中
    对随机奇异向量作未说明的可测选择；
  - 从显式 norming scalar sum 自动选择 singleton 系数
    `a i * v j`，给出相对于算子尺度的 `card⁻²` 下界；
  - 对任意非零连续算子内部构造 Hahn--Banach 近 norming pair，并直接产出上述
    大 singleton coefficient。
- `PaperProjectiveObservability.lean`、`PaperProjectiveConditional.lean`
  - 用有限坐标测试矩阵把 scalar multiaffine polynomial 的求值严格识别为真实
    fresh exterior 表达式 `B Q v` 的一个坐标，并内部选择具有显式下界的满系数；
  - 对复、实和异质 directional fiber 证明零点集零测、可积对数缺损与实际
    `log ‖B Q v‖` 的条件积分下界；选择器保持在 `∀ past, ∃` 内，避免虚构可测
    奇异向量；
  - 证明 comp-product fiber 积分与 canonical `condExp` 的几乎处处恒等式及
    下界运输，完成 projective 分支真正的过去可测条件期望接口。
- `PaperConditionalCompletion.lean`
  - 用论文的归一化二阶矩自动证明 projective 向量的正对数可积性，
    复、实最终期望下界不再把 `hexcess` 作为外部假设；
  - 对过去可测的冻结 family `B`，将 literal `Z_B` 的统一 fiber `L¹`
    界提升为联合可积性，并识别 canonical conditional expectation 与 fresh
    fiber 积分，同时给出几乎处处条件界。
- `Multiaffine.lean`
  - 递归定义 multiaffine polynomial、求值和满单项式系数；
  - 证明冻结前缀后最后一个坐标的精确线性差分公式；
  - 对正 `rho` 和非零满单项式系数，在显式的 open-small-ball 边缘等式与
    正尺度 integrated one-coordinate small-ball 输入下，无洞证明
    `lem:multiaffine` 的 small-ball `k * delta` 归纳，以及 `k * C * rho`、
    `k * C * rho^2` 两个版本。
- `MultiaffineTranslation.lean`
  - 递归构造多仿射多项式的加法、缩放与逐坐标确定性平移；
  - 证明平移后的求值恒等于原多项式在 `x+t` 的求值，并证明满单项式系数完全
    不变，形式化论文中 diagonal `-z` 只贡献低次项的代数理由。
- `ProductSmallBall.lean`
  - 用 `Measure.prod` 与 `Measure.map` 构造 `Fin n → ℝ/ℂ` 上的递归 IID laws；
  - 证明 multiaffine evaluation 的连续性、small-ball events 的可测性和实际
    prefix marginal identity；
  - 从 `volume.withDensity f`、`f ≤ L` a.e. 与概率归一化，经 product/Fubini
    无洞推出实支 `2 L k rho` 和复支 `pi L k rho^2`。
- `MultiaffineLog.lean`
  - 用 layer-cake 从 `A rho^m` 小球界推出速率 `m/d` 的显式截断负对数期望界；
  - 直接接实/复 IID with-density 模型，分别得到 `A = 2Lk, q = 1/k` 与
    `A = pi L k, q = 2/k`；结论对每个有限 cutoff 一致。
- `MultiaffineUntruncated.lean`
  - 由 power small-ball 证明多项式零点集为零测，并证明 cutoff 损失单调且
    依单调收敛趋于未经截断的正对数损失；
  - 给出实/复 IID 有界密度的最终未截断入口，几乎处处精确等于
    `(log (|topCoeff| / |P|))₊`，并保留同一显式期望界。
- `MultiaffineDirectional.lean`
  - 提供较早的 constant/IID-kernel 解析接口：以显式 Markov kernel 表示正交
    分量 `V` 给定后标量方向分量 `U` 的条件律，并要求每个 fiber 是满足统一
    区间小球界的递归 IID product；
  - 通过 comp-product/Tonelli 证明联合 `(V,U)` 律下的方向 small-ball、零点集零测
    与未经截断的正对数期望界；后续 directional 模块给出论文所需的正确异质
    条件乘积特化。
- `HeterogeneousProductSmallBall.lean`、`DirectionalKernelConstruction.lean`
  - 将独立但不必同分布的有限实坐标乘积接入 multiaffine small-ball 与未截断
    对数损失定理；
  - 从论文的单原子方向条件密度假设构造 canonical regular conditional law，
    仅在边缘零测集上修补后得到处处满足统一区间界的 Markov kernel；
  - 递归构造随完整正交向量变化的异质条件乘积核，并证明其 fiber、联合
    small-ball 与正对数损失界。
- `LIntegralFiniteProduct.lean`、`DirectionalVectorLaw.lean`
  - 证明有限乘积测度下非负可测坐标函数乘积的精确 `lintegral` 分解；
  - 利用该分解证明实际 IID 复原子向量旋转后的 `(V,U)` 联合律，严格等于
    正交边缘乘积与异质条件核的 comp-product；
  - 证明该核与联合律的 canonical `condDistrib` 在正交边缘下几乎处处一致。
- `DirectionalOperatorAffine.lean`
  - 把冻结正交坐标后的复随机原子逐项重构为真实复数，并证明所得算子表达式
    精确化为 real-input complex operator-affine 形式；
  - 从原始方向条件密度假设推出异质 fiber small-ball、零点集零测及
    `L²` 对数缺损界，直接覆盖实际重构的复随机行。
- `DirectionalFreshClosure.lean`
  - 把异质 directional conditional-product 下的负对数界严格运回实际
    IID 复原子联合律，并接到 literal flat 随机矩阵的真实 `Z_B`；
  - 正对数半边只使用非条件二阶矩，最终得到 directional 假设下完整
    双侧 `L¹` fresh closure。
- `DirectionalOperatorAffineFull.lean`
  - 将 directional small-ball 负半边与实际 IID 原子的非条件二阶矩正半边合成；
  - 对论文实际 operator-affine 表达式给出零点集零测和完整双侧
    `L²` 对数偏差界。
- `FreshClosure.lean`
  - 证明绝对对数偏差精确分解为 deficit 与 excess，并把两侧 `L¹` 界合成为
    one-fresh-block closure；
  - 若隔离系数仅有 `bmin^d * scale` 下界，自动给出精确的
    `-d * log bmin` 换尺度损失。
- `FreshAtomProductSplit.lean`、`PiRestrictMarginal.lean`、
  `PaperFreshCoordinateMarginal.lean`、`ProductIntegralUniformBound.lean`
  - 对任意 reset word，把每行选中的原子与全部未选原子构造成可测等价，
    并证明 IID 原子乘积测度被严格送到两组坐标的乘积测度；
  - 证明从任意更大的有限 IID 坐标空间沿注入抽取 fresh block 后，边缘律仍是
    目标坐标上的 IID 乘积，从而可把抽象 fresh-product 结论严格搬回 flat sample；
  - 给出带统一 section 积分上界的有限乘积 Fubini 闭合引理，供实际 fresh
    polynomial 的负半部使用。
- `PaperFreshClosurePositive.lean`、`PaperFreshClosureFull.lean`
  - 从真实 exterior trace 的矩阵范数、时间序乘积与逐行原子和，证明 actual
    `paperIndicatorFreshZ` 的正对数可积性和显式期望上界，并分别接到复、实
    literal flat IID 样本；
  - 把隔离满单项式、selected/unselected product split 与 Fubini 合成为复、实
    full fresh-product 的零点集零测和负对数界，再经 injective flat marginal
    严格搬回实际随机矩阵样本；
  - 最终 `complex_paperIndicatorFlatFreshZ_absLog_L1_withDensity` 与
    `real_paperIndicatorFlatFreshZ_absLog_L1_withDensity` 内部导出 a.e. 正性和
    两侧可积性，不保留 `hZpos` 或 `hexcess` 作为调用者假设。
- `ExponentialTailSecondMoment.lean`
  - 用 layer-cake 与 Gamma 积分证明 `P(Z>t) ≤ A exp(-qt)` 推出 `Z ∈ L²`；
  - 给出显式二阶矩界
    `E Z² ≤ 4 ((log(max 1 A)+1)/q)²`，并证明 `A=1` 时的精确 `2/q²` 版本。
- `LogDeviationSecondMoment.lean`
  - 把同一尺度下的 deficit/excess 两条指数尾分别转成 `L²`，再合成为完整
    `|log radius - log scale|` 的显式二阶矩界。
- `PositiveLogMoment.lean`
  - 形式化 operator-affine 正半边的缩放估计：由 `S/scale` 的二阶矩控制
    `log₊²(S+|z|)`，常数完全显式；
  - 用有限和 Cauchy--Schwarz 证明逐坐标二阶矩 `≤ 1` 自动推出归一化随机和
    的二阶矩 `≤ 1`。
- `OperatorAffineLog.lean`
  - 定义论文的 operator-affine scale，并证明总能选到一个达到固定比例的
    加权系数算子；
  - 用近范数向量与 Hahn--Banach 泛函把该算子标量化为大斜率的一坐标仿射式；
  - 证明冻结其余坐标后的实/复 operator-norm 小球界，以及正对数所需的
    `‖G‖ ≤ μ (Σ ‖ξᵢ‖ + ‖z‖)` 确定性界。
- `PaperOperatorAffineL2.lean`、`PaperOperatorAffineRealL2.lean`
  - 把论文的平方根 indicator weights、完整 IID 行和自然
    `W⁻¹ᐟ²` 尺度代入 operator-affine 引理；
  - 分别对复平面有界密度与实有界密度输入给出显式双侧 `L²` 对数界。
- `PaperPressureObservable.lean`、`PaperPressureLeaveOneOut.lean`
  - 在“一个独立坐标就是一整行”的字面随机矩阵样本空间上定义
    `Y_q(n)=log ‖A_[1,n]^(q)‖`；
  - 证明替换第 `i` 行前后共享同一左右历史、冻结算子族及尺度，并精确等于
    同一个 operator-affine 表达式的两次求值。
- `PaperPressureComplexL2.lean`、`PaperPressureRealL2.lean`
  - 将实/复 operator-affine `L²` 定理搬运到完整的实际 open pressure 行纤维；
  - 同时处理冻结尺度为零的退化情形：此时所有更新后乘积范数逐点为零。
- `PaperPressureDirectionalL2.lean`
  - 把完整 directional operator-affine `L²` 定理代入实际 leave-one-row pressure
    fiber，并同样闭合正尺度与零尺度两个分支。
- `IIDFiberL2Resampling.lean`、`IIDFiberMemLpResampling.lean`
  - 对任意有限坐标证明 `Fin.insertNth` 形式的 IID Fubini 公式；
  - 从逐冻结历史的 `MemLp 2` 共同中心界自动得到双样本可积性和单行
    raw replacement energy `≤ 4V`。
- `IIDFiberOuterIntegrable.lean`
  - 从同一逐冻结行纤维 `MemLp 2` 界自动推出 raw replacement square 的
    outer Bochner 可积性；
  - `iidRawResamplingEnergy_le_four_mul_of_fiber_memLp_auto` 因而无需调用者另行
    提供 outer-integrability 前提，即可得到单坐标能量 `≤ 4V`。
- `PaperPressureComplexConcentration.lean`、`PaperPressureRealConcentration.lean`
  - 对实际复/实行样本证明单行能量界、逐 exterior degree 方差界
    `Var ≤ 2nV`，以及所有 degree 的期望最大中心偏差界；
  - 这些 conditional 底层 API 仍把全局 `MemLp 2` 与 outer Bochner 可积性
    保留为显式前提，便于在其他模型中单独复用。
- `PaperPressureDirectionalConcentration.lean`
  - 将 directional row-fiber `L²` 界代入真实行替换、连续 IID
    Efron--Stein、逐 exterior degree 方差与有限次数最大偏差链；
  - 保留显式常数 `directionalPaperPressureFiberL2Bound`，使方向密度、
    二阶矩和谱参数的依赖可直接审查。
- `PaperPressureDirectionalAssumptionFree.lean`
  - 从 all-scales directional row-fiber `L²` 定理内部推出 outer 可积性、
    raw replacement energy 与全局 `MemLp 2`；
  - 最终 `_le_auto` 定理给出逐次数方差和全次数最大偏差，并通过
    保测度行分组搬回 literal flat 随机矩阵空间；调用者不再需要提供
    全局 `MemLp 2` 或 outer Bochner 可积性。
- `PaperPressureAssumptionFree.lean`
  - 将行纤维 `L²` 定理代入上述通用桥，自动证明论文实/复 pressure 的
    `rawOuter_integrable`、raw energy 与全局 `MemLp 2`；
  - 给出后缀为 `_le_auto` 的逐次数方差及全次数最大偏差定理，并继续搬运到
    literal flat 随机矩阵空间；这些最终 wrappers 不再要求调用者提供全局
    `MemLp 2` 或 outer Bochner 可积性。
- `FlatIIDRows.lean`、`PaperIndicatorFlatConcentration.lean`
  - 证明扁平的 `N(m+2)` 个 IID 标量与 `N` 个 IID 完整行之间存在真正的
    measure-preserving measurable equivalence；
  - 逐坐标核验该等价与既有 `paperIndicatorXi` / `paperIndicatorXiOfReal`
    flattening 完全一致；
  - 将实/复逐次数方差和全次数最大偏差定理严格搬回定义
    `paperIndicatorX` 的 `paperIndicatorSampleMeasure` / real flat 样本空间；
  - 本模块保留可复用的 conditional transport，而
    `PaperPressureAssumptionFree.lean` 中相应 `_le_auto` 定理已自动消除其两个
    技术前提。
- `Pressure.lean`
  - 证明 pressure concentration 最后一步的纯有限维最大值不等式；
  - 对 `0,...,2W` 阶给出精确的 `sqrt(2W+1)` 损失。
- `PressureProbability.lean`
  - 在任意概率空间上证明逐次数方差之和控制期望最大中心偏差；
  - 特别地，若每个次数的方差至多为 `V`，则得到论文形状的
    `E max_r |Y_r - E Y_r| <= sqrt((2W+1) V)`。
- `PressureEfronStein.lean`
  - 在有限非空类型的 `n` 重均匀乘积上，从全方差分解递归证明 sharp
    Efron--Stein：`Var f <= (1/2) sum_i E(f(X)-f(X^i))^2`；
  - 定义实际坐标替换 `uniformCubeReplace`，并证明递归 resampling energy
    精确等于对旧样本和独立新坐标的双重平均；
  - 从逐点平方变化
    `(f(x)-f(replace x i a'))^2 <= D` 推出 `Var <= nD/2`，再直接接到
    `pressure_maximal_concentration_of_variance`，得到完整有限均匀模型的
    `sqrt((2W+1)nD/2)` 最大偏差界。
- `GeneralPMFEfronStein.lean`
  - 将上述递归证明推广到任意有限 PMF 的 IID product，允许非均匀权重和
    零质量原子；
  - 给出实际 PMF product measure 下的 replacement 双重积分公式，并直接接到
    pressure 最大偏差结论。
- `ContinuousEfronStein.lean`
  - 对递归连续 IID product law 证明有界可测函数的乘积全方差分解、单坐标
    independent-copy 恒等式和逐层 fresh-coordinate resampling 恒等式；
  - 递归构造 Doob 型重采样预算，证明全维方差界，并把该预算直接接到 pressure
    最大偏差闭合。
- `RawContinuousEfronStein.lean`
  - 定义标准连续坐标替换能量
    `∫ x, ∫ a', (f x - f (Function.update x i a'))²`，并证明末坐标与前缀坐标的
    `joinLast`/Fubini 展开；
  - 用条件均值的 Jensen 收缩证明递归 Doob 预算受控于全部 raw-coordinate
    energies 之和，从而得到 sharp `1/2` 的标准全维 Efron--Stein 与 pressure closure。
- `UnboundedRawContinuousEfronStein.lean`
  - 构造 1-Lipschitz 对称截断 `symmetricClip`，证明它不增大任一
    raw-coordinate replacement energy；
  - 用支配收敛证明截断方差回到原 `MemLp 2` 观测量的方差，
    因而将连续 IID Efron--Stein 从全局有界函数推广到真正的 `L²` 变量；
  - 直接推出 `MemLp 2` 版 pressure 最大偏差界，不再对对数观测量假设
    pointwise boundedness。
- `UnboundedRawContinuousMemLp.lean`
  - 用对称截断、两独立样本差的统一二阶矩界与 Fatou 论证，从 raw coordinate
    replacement square 的 inner/outer 可积性反推出原观测量的全局
    `MemLp 2`；
  - 通用入口 `memLp_two_of_iid_raw_replacement_integrable` 使 paper-specific
    最终定理不必再把全局 `MemLp 2` 当作外部输入。
- `UnboundedContinuousPressureL2Bridge.lean`
  - 在所需的 inner/outer Bochner 可积性都显式列出的条件下，把共同冻结中心的
    两个 `L² ≤ V` 界转化为 raw replacement energy `≤ 4V`；
  - 将该估计接到 `MemLp 2` Efron--Stein 与 pressure 最大偏差，从而完全移除
    旧 common-center bridge 中的 pointwise boundedness 限制。
- `ContinuousPressureL2Bridge.lean`
  - 证明连续 IID law 下，原观测与同一坐标替换观测围绕共同冻结中心各有
    平方积分 `≤ V` 时，标准 raw replacement energy `≤ 4V`；
  - 将该界对所有坐标和 exterior degrees 求和，直接接到连续 Efron--Stein 与
    pressure 最大偏差，形式化正文共同中心 `log μ_i` 的平方差步骤。
- `PressureL2Bridge.lean`
  - 形式化 operator-affine 引理之后所需的替换代数：若原观测量与单坐标
    替换后的观测量，围绕同一个冻结中心各有平均平方误差 `<= V`，则
    replacement energy `<= 4V`；
  - 将这个 `L²` 型输入直接接到 Efron--Stein 和最大压力偏差，不再要求逐点
    bounded-difference。
- `PressureTailBridge.lean`
  - 将旧行观测量与独立替换行的两个显式 `A exp(-qt)` 尾界，自动转成共同中心
    `L²` 控制、replacement energy、Efron--Stein 方差；
  - 直接推出最大压力偏差，完整消去中间二阶矩/能量参数，留下的唯一输入是
    paper-specific 的两条 operator-affine 指数尾。

所有本地定理均没有 `sorry`、`admit` 或自定义 `axiom`。`AxiomAudit.lean`
列出关键公开定理的 Lean 公理依赖。

## 明确的形式化边界

这份交付已覆盖论文 Section 4 中 9 个具名 lemma/proposition 的证明主链；
精确的数学覆盖范围以各 Lean 定理的假设与结论为准。
这里的“完成”指主结论已代入论文的 transfer、fresh block、projective
向量与实际随机矩阵样本；它不表示已形式化 Section 5、Section 6 或整篇论文。

1. 周期行列式链已经从字面 `X_N-zI_N` 闭合到 cyclic state system、
   chronological monodromy、`det(I-P)` 与清分母交错外幂迹。最终定理
   `paperXSubZI_det_eq_clearedSignedCompoundTrace` 不再含 paper-specific
   certificate 或未解释的重排接口；对称带状模型只需代入
   `m+1=2W`、`center=W`。`det T_i = alpha_i / beta_i`、transfer 及其全部
   exterior powers 的可逆性也已接到 literal 随机样本的 a.e. 结论。
2. reset-word/ordered-exterior 隔离链已接到真实
   `paperIndicatorFreshZ`：多仿射求值、满次数系数、谱平移不变性、
   `bmin^d` 损失以及 literal flat sample 均已形式化。复、实有界密度 IID
   flat sample 的 one-fresh-block 两侧对数 `L¹` closure 由真实 trace 上界、
   selected/unselected 坐标独立分解、Fubini 与零点集零测内部合成；最终入口
   不把 `Z_B ≠ 0` 或正半可积性当作外部假设。对过去可测 `B`，
   `PaperConditionalCompletion.lean` 进一步证明联合 `L¹`、canonical `condExp`
   与 fresh fiber 积分的 a.e. 恒等式及统一条件界。
3. projective 分支已把 scalar polynomial 严格识别为真实 `B Q v` 的坐标，
   用有限坐标选择避免可测奇异向量问题，并完成复、实、raw-directional fiber
   的对数下界。正对数可积性已由论文归一化二阶矩自动推出，
   复/实最终期望定理不再需要外部 `hexcess`；comp-product fiber integral 与
   canonical conditional expectation 的几乎处处恒等式和下界运输也已证明。
4. directional-density 分支从论文的单原子 a.e. 条件密度假设出发，构造只在
   零测集上修补的 regular conditional kernel，以及正确的异质有限乘积核。
   实际 IID 旋转原子向量的联合律已证明等于该 comp-product，且该 kernel 与
   canonical `condDistrib` 几乎处处一致；重构复随机行的 operator-affine
   small-ball、完整双侧 `L²` 对数界、literal `Z_B` 双侧 `L¹` fresh closure
   和 pressure concentration 均已闭合。一般情况下条件坐标独立但不同分布，
   只有条件律不随正交坐标变化时才能退化为 IID kernel。
5. pressure 分支覆盖真实 indicator 随机矩阵的 leave-one-row operator-affine
   估计、连续 IID raw-coordinate Efron--Stein、全局 `MemLp 2`、逐次数方差与
   全次数最大偏差，并通过扁平样本与整行样本的保测度等价搬回 literal
   `paperIndicatorX` 空间。复、实与 directional 三个分支的最终 `_le_auto`
   入口均不再要求调用者提供全局 `MemLp 2` 或 outer Bochner 可积性。

仍保留为显式假设的是论文本身的概率输入，例如原子归一化、独立性、有界密度
或方向条件密度、二阶矩、权重正性与必要的非退化条件。这些都是 theorem
parameters/structure fields，而不是隐藏的本地公理。因此最准确的描述是：这是
一个 **Section 4 的 9/9 具名结果主链、可编译、无洞的形式化**，
不是整篇论文的完全形式化。

## 构建与审计

以下所有命令均从仓库根目录运行，而不是从 `Section4/` 目录运行。
首次环境准备和统一依赖说明见[仓库根 README](../README.md)。

```bash
lake build
lake env lean Section4/AxiomAudit.lean
lake env lean Section4/FourGapsAxiomAudit.lean
lake env lean Section4/Section4CompleteAxiomAudit.lean
rg -n '^[[:space:]]*(axiom|opaque)\b|\b(sorry|admit)\b' --glob '*.lean' Section4
```

各章节共用仓库根的 Lake/mathlib 工程和 `.lake` 缓存；日常验证无需运行
`lake update`，也无需为本模块或文档审计另建一份 mathlib 缓存。

从仓库根看，入口文件是 `Section4/CircularLawSection4.lean`。
论文标签与 Lean 声明的逐项对应见
[FORMALIZATION_MAP.md](FORMALIZATION_MAP.md)。
