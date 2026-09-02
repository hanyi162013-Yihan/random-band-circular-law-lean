# arXiv v1 章节、公式与覆盖范围

目标文献：Yi Han,
[*The circular law for non-Hermitian random band matrices: optimal bandwidth,
periodic profile and discrete law*](https://arxiv.org/abs/2609.01295v1)，
2026-09-01，v1，89 页。

本库位于 `Section9/`，命名空间与导入入口为
`BernoulliLinearAlgebra`。仓库的 `Section4/` 是另一独立章节库。

## 章节与命名结果

| 内容 | arXiv v1 位置 | v1 PDF 页码 |
|---|---|---|
| all-minor coefficient estimate | Lemma 7.5，式 (7.24)；证明 §9.1.3 | 陈述 39；证明 60–61 |
| Block Floquet | Lemma 7.6，式 (7.39)；证明 §9.3 | 陈述 41；证明 62–64 |
| 双消元 | Proposition 9.3，§9.4，式 (9.77)、(9.79) | 64–66 |
| 三块物理行缩放 | Corollary 9.4，式 (9.83) | 66 |
| compound、Hodge/Jacobi、移除端点矩阵 | §9.4.1，式 (9.84)–(9.88) | 66–67 |
| boundary coefficient–volume | Lemma 7.7，式 (7.46)；证明 §9.5 | 陈述 42；证明 67 |
| Gram volume / exterior operator 比较 | Lemma 7.8，式 (7.47) | 42 |

## TeX 标签与公式号

以下标签从官方 arXiv v1 源码的 `part2_block.tex` 读取，并以 TeX
生成的交叉引用和正式 PDF 中的显示编号核对。标签用于定位，不是
额外 Lean 假设。

| 稳定 TeX 标签 | arXiv v1 |
|---|---|
| `eq:local-mask`、`eq:local-mask-support` | (7.11)、(7.12) |
| `eq:local-terminal-matrix`、`eq:local-terminal-coefficients` | (7.16)、(7.18) |
| `eq:local-all-minor` | (7.24) |
| `eq:local-floquet-clearing-factors`、`eq:local-floquet-packet-split` | (7.38)、(7.39) |
| `eq:local-DTheta`、`eq:local-DTheta-det` | (7.42)、(7.44) |
| `eq:local-E-control`、`eq:local-coefficient-main` | (7.45)、(7.46) |
| `eq:local-boundary-volume-vs-exterior` | (7.47) |
| `eq:local-monomial-minor` | (9.44) |
| `eq:local-coefficients-to-minors` | (9.45) |
| `eq:local-all-minor-CB` | (9.46) |
| `eq:local-floquet-recurrence` | (9.56) |
| `eq:local-block-floquet` | (9.57) |
| `eq:local-floquet-augmented-system` | (9.59) |
| `eq:local-floquet-first-elimination` | (9.62) |
| `eq:local-floquet-factor-L` | (9.64) |
| `eq:local-floquet-second-elimination` | (9.68) |
| `eq:local-floquet-cleared-one-step` | (9.69) |
| `eq:local-floquet-polynomial-extension` | (9.70) |
| `eq:local-Theta-blocks` | (9.71) |
| `eq:local-STheta` | (9.73) |
| `eq:local-E` | (9.74) |
| `eq:local-HTheta` | (9.76) |
| `eq:local-double-elimination` | (9.77) |
| `eq:local-KTheta` | (9.78) |
| `eq:local-K-first-elimination` | (9.79) |
| `eq:local-S-action` | (9.82) |
| `eq:local-boundary-scaling` | (9.83) |
| `eq:local-compound-sum` | (9.84) |
| `eq:local-compound-minors` | (9.85) |
| `eq:local-E-compounds` | (9.86) |
| `eq:local-ES-two-directions` | (9.87) |
| `eq:local-remove-E` | (9.88) |
| `eq:local-MN` | (9.89) |
| `eq:local-graph-Gram` | (9.90) |
| `eq:local-graph-identity` | (9.91) |
| `eq:local-Theta-approx` | (9.92) |

## 数学内容和覆盖审计

[覆盖表](FORMALIZATION_MAP.md)逐项列明 Lean 定理，而不将所有相关
论文陈述都计为完整证明。尤其应区分：

- 已证明的原始单位权重、显式有限常数比较和实际矩阵消元；
- 尚未完成的全部逐项权重实例化、统一 `exp(C W log W)` 常数控制
  与奇异值乘积识别定理；
- 本库范围外的事件概率、small-ball 和任意 frame 论证。

具体假设与结论以 Lean 定理为准。Cook、Nguyen、RRQR 不作为本库的
新公理或本次发布的已证明结果。

## 源文献指纹

核对所用官方源码：[arXiv v1 source](https://arxiv.org/src/2609.01295v1)。
以下为 SHA-256；本仓库不复制论文 PDF、TeX 或本地构建产物。

| 文件 | SHA-256 |
|---|---|
| v1 source archive | `597d5b03337dd90a550d918179948f80d28ca692eeac648754e61d7b26c2ca5a` |
| `main.tex` | `eb737f3e1541e7949cf71354fa7cd18a49f2d779d2c71108dda262339e8d98fe` |
| `part2_block.tex` | `9ad6009606b66d6a02afbe7df56872276f98e9196ecf66522032f91de86c1fbc` |
| v1 PDF | `c09843c706aebf8a33358d870a7c9d11d7c52926b0132605fa2ffd7eed4f512d` |
