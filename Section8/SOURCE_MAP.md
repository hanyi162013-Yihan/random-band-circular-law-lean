# Section 8 source map: discrete cyclic full-block branch

## Fixed source and scope

This is a source-level audit, not a declaration that the Section 8 Lean
implementation is complete. The implementation ledger belongs in
`FORMALIZATION_MAP.md`; entries below identify the exact obligations against
which that ledger must be checked.

The fixed source is Yi Han, *The circular law for non-Hermitian random band
matrices: optimal bandwidth, periodic profile and discrete law*,
[arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1).
`part2_block.tex` has SHA-256
`9ad6009606b66d6a02afbe7df56872276f98e9196ecf66522032f91de86c1fbc`;
the 89-page PDF has SHA-256
`c09843c706aebf8a33358d870a7c9d11d7c52926b0132605fa2ffd7eed4f512d`.
Both fingerprints were checked. Section 8 is at `part2_block.tex`
987-1957, PDF pp. 43-53. The model and discrete main theorem appear at
lines 74-181. The PDF numbering was independently checked by extracting the
relevant PDF pages, rather than counting every raw TeX label: the TeX also
contains commented-out statements.

The printed result being closed is **Theorem 2.8**, label `thm:main`.
The model has `N = m W`, `m >= 4`, `W` tending to infinity, and
`W / log N` tending to infinity. All entries in the three displayed block
diagonals are independent copies of a fixed **real**, centered,
variance-one, subgaussian atom. Every block is divided by `sqrt(3 W)`.
There is no density assumption. The Rademacher law assigning mass `1/2`
to each of `-1` and `1` is an explicit instance.

The conclusion is convergence in probability of the empirical eigenvalue
measure to the uniform probability measure on the unit disk, together with
normalized logarithmic determinant convergence to
`U(z) = (|z|^2 - 1) / 2` for `|z| <= 1` and `U(z) = log |z|` otherwise,
on a deterministic full-planar-measure set. Proposition 8.2 and equation
(8.67) assert the stronger intermediate conclusion **for every fixed**
`z : Complex`. No simultaneous convergence over all `z` is asserted.

## Normalization and probability conventions

- Row block `j` has `C_j` at its left cyclic neighbor, `A_j` at its own
  site, and `B_j` at its right cyclic neighbor. There are exactly `3 W`
  independent entries of variance `1 / (3 W)` in every scalar row, hence
  `3 N W` displayed variance-one atoms in the whole matrix.
- Chronological transfer multiplication has later sites on the left.
  At the cut immediately preceding sites `a,a+1,a+2`, the packet sends
  `v_in = (psi_a, psi_(a-1))` to `v_out = (psi_(a+3),psi_(a+2))`.
  The outside sends `v_out` back to `v_in`. Thus the actual local boundary
  parameter is `Theta = R_out`, after conditioning on the outside.
- Transfer inverses exist only on interface-good events. The cleared
  exterior operator must be defined polynomially on *all* samples. At a
  singular `B`, Lean's totalized matrix inverse inserted into
  `(det B) * wedge^r T` does not define this polynomial continuation.
- `log 0 = -infinity` in the paper. Lean's `Real.log 0 = 0` is a different
  convention and needs a proved event comparison before use in a
  convergence statement. The paper's clipping sends `-infinity` to the
  lower endpoint and its capped value loss sends a zero denominator to
  the cap.
- Probability concentration is under the original IID law, never under
  the law conditioned on all interfaces being good.
- The only failures union-bounded over the entire ring are exponentially
  small interface failures. The terminal/reset small-ball error `p_W`
  is averaged in a capped loss and then handled by Markov; it must not be
  multiplied by the number of cells.

## Imported inputs and exact trust boundary

### L1: one-site interface regularity

The source imports Lemma 7.1, `lem:local-interface-control`, with the
subgaussian norm tail for the diagonal block. The resulting event `G_j`
has complement probability at most `exp(-c W)`, bounds all three normalized
block norms by a fixed constant, bounds the absolute determinants of `B_j`
and `C_j` between `exp(-C W)` and `exp(C W)`, and bounds their inverse
norms by `exp(C W)`. Constants depend on the fixed atom/subgaussian bound;
growth constants below may also depend on the fixed `z`.

Section 9's proof uses Nguyen fixed-index and overcrowding estimates,
subgaussian matrix norm tails, a product of singular-value floors, and
the smallest singular-value floor. Repository entry points include
`BernoulliSection9.nguyenInterfaceCanonicalDetInverseControl`,
`interfacePairProbabilityAndPaperEndpointGood`, and
`section9CanonicalLargeWThreshold`; check their current signatures before
applying them.

`NguyenBottomSingularInput` in `BernoulliSection9/ExternalInputs.lean`
remains an **explicit unproved literature input**. It fixes a subgaussian
parameter range and the constants `theta`, `gamma0`, `nguyenc`, `nguyenC`,
and `k0`; its `fixedIndex` and `overcrowding` fields quantify over concrete
IID real subgaussian squares in that range. No value of this structure is
constructed by the Section 9 wrapper merely because its axiom report is
clean. The user subsequently explicitly authorized this literature input
for Section 8. It must remain visible in the assumption/signature ledger;
this authorization does not turn its fields into internally proved
probability estimates.

### L2: terminal packet, coefficients, and arbitrary complex frames

The source imports Proposition 7.3 `prop:local-terminal`, Lemma 7.7
`lem:local-boundary-volume`, Lemma 7.8 (equation
`eq:local-boundary-volume-vs-exterior`), Corollary 7.9 `corollary885`,
and Theorem 7.10 `thm:local-complex-frame`.

The packet consists of three sites. Its endpoint matrices are the left
`C` and right `B`; the other **seven** independent matrix blocks remain
fresh. The concrete main model has unit raw-entry weights. The physical
normalization `1 / sqrt(3 W)` must be reconciled by an equality, not by
inserting a generalized weighted-packet estimate.

The capped coefficient-relative log loss is at most
`C W log W + p_W T` for every `T > 0`, with
`p_W <= C sqrt(log W / W) + exp(-c W)`. The statement is uniform in
deterministic complex outside deformations and complex Grassmann frames.
Application to random outside data requires the stated outside
measurability and fresh/outside independence. Reverse evaluation bounds
hold on the fresh maximum-entry event and fail with probability at most
`exp(-c W)`; they are not deterministic for general unbounded subgaussian
atoms.

Theorem 7.10 in the PDF has only its coefficient bounds (7.54) and capped
estimate (7.55). Raw labels `eq:local-frame-zero` and
`eq:local-frame-reverse` occur inside a TeX `comment` environment and are
**not** separately printed conclusions of Theorem 7.10. Zero probability
is obtainable from the capped estimate by letting the cap tend to
infinity; the terminal reverse estimate is available from the terminal
and boundary statements.

Repository public routes include `section9TerminalSmallBall`,
`section9TerminalSmallBallConditional`, the literal-frame theorems in
`Section9Results.lean`, and the conditional lifting modules
`RandomQConditional.lean` and `RandomFrameConditional.lean`. Deterministic
coefficient/minor and transfer algebra comes from `BernoulliLinearAlgebra`.
The local probability routes still take
`CookDeformedSquareInput`, and interface-combined routes also take
`NguyenBottomSingularInput`.

`CookDeformedSquareInput` fixes a subgaussian bound, a positive profile
interval containing `1`, and functions `beta L`, `cookC L`, `cookc L`.
Its unconditional field quantifies over a deterministic complex
deformation with norm at most `n^L`; its conditional field additionally
requires fresh-square measurability, independent outside sigma-field,
outside deformation measurability, and an almost-everywhere deformation
norm bound. Both are genuine singular-value estimates, not algebraic
certificates. Section 9 applies them to two disjoint complete IID squares.
An input for Bernoulli atoms alone can suffice for a Bernoulli final
theorem; construction of the fully universal structure is stronger than
that minimal obligation.

The established RRQR polynomial exponent is `16`, while printed Lemma
9.1 uses `4`. A fixed polynomial loss remains sufficient for Section 8:
it changes fixed constants in `O(W log W)` and width thresholds, and does
not alter any limiting error. This is a sufficient quantitative variant,
not a new asymptotic obstruction. Packaging for the actual Section 8
parameters is now written in `RademacherTerminalRates.lean` and
`CookRates.lean`: the base loss is bounded by a fixed multiple of
`W log(eW)`, and the exact Cook failure multiplied by `log(eW)` tends to
zero. Its normal-build verification remains pending; see
`FORMALIZATION_MAP.md` for the declaration and status ledger.

### L3: the permitted high-band anchor

**Proposition 3.8**, `prop:subgaussian-block-high-band`, has its statement
at `main.tex` 1146-1161 and proof at 1163-1245, not in the Section 8
portion of `part2_block.tex`.
It applies to the actual cyclic full-block model under a fixed real
centered variance-one subgaussian law, `N,W -> infinity`, and
`W >= N^(8/9 + omega)` for fixed `0 < omega < 1/9`. Its conclusion (3.19),
`eq:gb-high-band-logdet`, is the normalized log-determinant limit for each
fixed complex `z`.

Its proof uses the repaired full-block LSV **Proposition 3.2**
`prop:jjlo-block-lsv` when `m >= m_*`. For the finitely many
`4 <= m < m_*`, it separately uses Cook's broadly-connected-profile
Theorem 1.12 and a subgaussian norm event. The remaining dependencies are
the mesoscopic counting Proposition 3.3, finite-third-moment bulk
comparison Lemma 3.4, Hilbert--Schmidt upper-tail truncation, and the
Ginibre logarithmic-potential/negative-moment input. The single use of
Proposition 3.2 does not cover the finite-`m` branch by itself.

The current authorized external mathematical inputs are the exact
**Section 3 propositions, Cook, and Nguyen**. The user explicitly clarified
that Section 4 is not an external input to this branch. Previously proved
generic source code may be reused regardless of its directory, but no
Section 4 paper-proposition parameter is needed or intended here.
Proposition 3.8 cannot supply L1 or L2; their Cook/Nguyen estimates are
listed separately. Reset, seam, pressure, reference, and replacement
conclusions are not authorized external assumptions and must be derived.

## Complete numbered result inventory

Only four numbered theorem environments occur in Section 8.

| PDF item / source | Printed assumptions and conclusion | Required proof dependencies |
| --- | --- | --- |
| Lemma 8.1, p. 47, `lem:gb-cell-concentration`, lines 1336-1359 | For `K_c >= 1` disjoint complete cells and `u > 0`, a simultaneous deviation bound over all `0 <= r <= 2W` for the sum of the clipped core logs, with size `C ell_W log W sqrt(K_c (log W + u))` and failure `2 exp(-u)` | IID disjoint cores; bounded measurable clipped logs; Hoeffding; finite degree union bound. No interface conditioning. |
| Proposition 8.2, p. 47, `prop:gb-roadmap`, lines 1367-1433 | Under Theorem 2.8's standing model assumptions, for each fixed `z`, `N^(-1) log |det(X_N-zI)| -> U(z)` in probability | Pressure sandwich, independent-anchor seam, Proposition 3.8, deterministic pressure calibration, long target seam/remainder, direct high-band branch, and interface probability ledger. Its displayed proof is an outline completed by later subsections. |
| Lemma 8.3, pp. 50-51, unnamed lemma at lines 1716-1727; use equation label `eq:gb-terminal-pressure` | For the independent anchor with `m_M = K_W c_W + 3` sites, its log determinant differs from the maximum degree log norm of the `K_W` complete-cell product by `o_P(M_W)` | Polynomial Floquet identity on the good event; conditional fresh terminal packet; coefficient norm versus boundary volume and maximal wedge growth; reverse event; simultaneous interface failure `o(1)`. |
| Corollary 8.4, p. 51, unnamed corollary at lines 1825-1833; use equation label `eq:gb-pressure-calibration` | The deterministic quantity `ell_W^(-1) max_r Phi_(W,r)(z)` tends to `U(z)` | Lemma 8.3, pressure concentration/stitching at `K_c = K_W`, Proposition 3.8 for the same anchor law, uniqueness of an in-probability limit for deterministic sequences, and terminal rounding. |

## Complete equation ledger

The ledger includes every effective Section 8 equation label. A source
label identifies an obligation even when several identities belong in one
Lean module. Equations described as definitions still require measurable
and algebraic compatibility when used probabilistically.

### Boundary orientation and local inputs (8.1)-(8.10)

| PDF | TeX label; line | Statement / dependency |
| --- | --- | --- |
| 8.1 | `eq:gb-packet-transfer-definition`; 1024 | `R_partial = T_(a+2) T_(a+1) T_a`, with `v_out = R_partial v_in`; interface-invertible recurrence. |
| 8.2 | `eq:gb-outside-transfer-definition`; 1031 | The complementary chronological transfer gives `v_in = R_out v_out`. |
| 8.3 | `eq:gb-cut-closure`; 1036 | Cyclic closure is `det(I - R_out R_partial) = 0`; finite-dimensional nontrivial kernel equivalence. |
| 8.4 | `eq:gb-abstract-boundary`; 1043 | Local theorem uses `v_in = Theta v_out`, `Theta` invertible. |
| 8.5 | `eq:gb-actual-theta-substitution`; 1050 | Substitute `Theta = R_out` only after exposing/conditioning on the complementary arc. |
| 8.6 | `eq:gb-one-site-failure`; 1071 | `P(G_j^c) <= exp(-c_K W)`; L1 plus diagonal-block norm tail. |
| 8.7 | `eq:gb-interface-det-control`; 1079 | Three block norms are bounded; `B,C` determinants have exponential upper/lower bounds. |
| 8.8 | `eq:gb-interface-inverse-control`; 1085 | `B,C` inverse norms have exponential bounds; only on `G_j`. |
| 8.9 | `eq:gb-pW`; 1096 | `p_W <= C_K sqrt(log W / W) + exp(-c_K W)`; L2 constants must be uniform over conditioned data and degrees. |
| 8.10 | `eq:gb-fresh-max`; 1107 | Fresh maximum-entry event `max |xi| <= C_0 sqrt W` and exponential failure; subgaussian scalar tails and `7 W^2` union bound. |

### Cleared transfer algebra and deterministic good-event growth (8.11)-(8.22)

| PDF | TeX label; line | Statement / dependency |
| --- | --- | --- |
| 8.11 | `eq:gb-transfer`; 1141 | Companion matrix `[-B^(-1)(A-zI), -B^(-1)C; I,0]`; recurrence on invertible `B`. |
| 8.12 | `eq:gb-cleared-transfer`; 1147 | Cleared degree operator `A_j^(r) = det(B_j) wedge^r T_j`; interpreted as its polynomial continuation off invertibility. |
| 8.13 | `eq:gb-wedge-product`; 1154 | Product of cleared operators equals the product of `det B` times the wedge of the chronological transfer product. |
| 8.14 | `eq:gb-cyclic-monodromy`; 1160 | `M_cyc = T_m ... T_1`. |
| 8.15 | `eq:gb-full-fock`; 1176 | Actual cyclic determinant equals a deterministic unit-modulus sign times `prod det B * det(I-M_cyc)`, and equals the alternating sum of traces of cleared degree products. The polynomial equality extends to singular interfaces. |
| 8.16 | `eq:gb-exterior-identities`; 1185 | `det(I-M) = sum_r (-1)^r trace(wedge^r M)` and wedge functoriality. |
| 8.17 | `eq:gb-cut-exterior-sum`; 1203 | Packet cut writes the determinant as `sign * c_out * sum_r (-1)^r trace(Q^(r) wedge^r R_out)`. Coefficient comparison handles cancellation. |
| 8.18 | `eq:gb-one-step-upper`; 1222 | Uniform degree operator norm bound `exp(C_(K,z) W log W)` on `G_j`, from polynomial companion-minor expansion. |
| 8.19 | `eq:gb-transfer-det`; 1227 | `det T_j = +/- det C_j / det B_j`. |
| 8.20 | `eq:gb-hodge`; 1234 | `norm(wedge^r T^(-1)) = |det T|^(-1) norm(wedge^(2W-r) T)`; Euclidean operator norm and Hodge duality. |
| 8.21 | `eq:gb-one-step-inverse`; 1243 | `norm((A_j^(r))^(-1)) <= norm(A_j^(2W-r)) / |det B_j det C_j| <= exp(C W log W)`. The first comparison can be an equality under the stated norms. |
| 8.22 | `eq:gb-product-control`; 1253 | For `s` consecutive sites of scalar size `L=sW`, the absolute log norm of the degree product is bounded by `C L log W`, using norm and inverse bounds. |

### Mesoscopic definitions and concentration (8.23)-(8.35)

| PDF | TeX label; line | Statement / dependency |
| --- | --- | --- |
| 8.23 | `eq:gb-cell-scales`; 1268 | `s_W=ceil(W^(1/200))`, `c_W=s_W+3`, `ell_W=c_W W`. |
| 8.24 | `eq:gb-anchor-scales`; 1274 | `K_W=ceil(W^(1/200))`, `M_W=W(K_W c_W+3)`; in particular `M_W=W^(101/100+o(1))`. |
| 8.25 | `eq:gb-cell-reset`; 1288 | Three-site cleared reset product in chronological order. |
| 8.26 | `eq:gb-cell-core`; 1292 | `s_W`-site cleared core product after the reset. |
| 8.27 | `eq:gb-cell-product`; 1295 | Whole cell is `core * reset`. |
| 8.28 | `eq:gb-core-transfer-and-scalar`; 1304 | Core transfer and its scalar product of right-interface determinants, on interface invertibility. |
| 8.29 | `eq:gb-core-cleared-form`; 1310 | Cleared core equals `c_core * wedge^r R_core`. |
| 8.30 | `eq:gb-clip-definition`; 1317 | Clip to a compact real interval, including `clip(-infinity)=a`. |
| 8.31 | `eq:gb-core-log`; 1322 | `Y_(k,r) = log norm(cleared core)`, possibly `-infinity`. |
| 8.32 | `eq:gb-clipped-log`; 1325 | Clip `Y` to `[-C ell_W log W,C ell_W log W]`; inactive on core-good event. |
| 8.33 | `eq:gb-pressure`; 1327 | `Phi_(W,r)(z)` is the expectation under the unconditioned IID law of the clipped core log. |
| 8.34 | `eq:gb-deterministic-degree`; 1329 | Least maximizing degree `r_*` is deterministic; fixed before sampling either target or anchor. |
| 8.35 | `eq:gb-hoeffding`; 1349 | Lemma 8.1 simultaneous independent-cell concentration; degree union bound of size `2W+1`. |

### Reset, capped losses, and stitching (8.36)-(8.52)

| PDF | TeX label; line | Statement / dependency |
| --- | --- | --- |
| 8.36 | `eq:gb-recursive-wedge`; 1446 | Normalize the preceding unit decomposable wedge after each complete cell, with a fixed fallback wedge when the image is zero. Measurable before the next fresh reset. |
| 8.37 | `eq:gb-top-singular-pair`; 1478 | Choose top singular wedges for the cleared core and adjoint, including the phase of `c_core`. |
| 8.38 | `eq:gb-adjoint-test`; 1484 | Absolute pairing with the top output wedge after the core equals core norm times pairing with the top input wedge. |
| 8.39 | `eq:gb-reset-pairing`; 1505 | `Z_(k,r)=<w_hat,reset v_hat>` and its coefficient norm `Gamma_(k,r)` in the seven fresh blocks. |
| 8.40 | `eq:gb-endpoint-regularity`; 1517 | Norm/determinant/inverse event for only the two exposed reset endpoints `C_(a_k),B_(a_k+2)`, with failure at most `2 exp(-c W)`. |
| 8.41 | `eq:gb-reset-coefficients`; 1525 | `exp(-C W log W) <= Gamma <= exp(C W log W)` from the fixed-degree theorem. |
| 8.42 | `eq:gb-reset-test`; 1534 | `norm(core * reset * v_hat) >= norm(core) * |Z|`, by testing on the top output wedge. |
| 8.43 | `eq:gb-actual-loss`; 1548 | Capped *actual norm loss*, with cap `T_W=C_2 ell_W log W`, not the scalar pairing loss. A zero norm triggers the cap. |
| 8.44 | `eq:gb-Hk`; 1557 | `H_k = core-good intersect endpoint-good`, measurable before the seven fresh reset blocks. |
| 8.45 | `eq:gb-conditional-loss`; 1573 | `1_(H_k) E[L_(k,r) | F_(k-1)] <= 1_(H_k)(C W log W+p_W T_W)`; conditional L2 plus coefficient lower bound and norm test. |
| 8.46 | `eq:gb-unconditional-loss`; 1580 | `E L_(k,r) <= C W log W+(p_W+exp(-cW)) T_W`; average over `H_k` and use cap on its complement. |
| 8.47 | `eq:gb-total-reset-loss`; 1594 | For one deterministic degree, normalized sum of actual losses is `O_P(W log W/ell_W+p_W log W+exp(-cW)log W)=o_P(1)`, by tower/Markov. |
| 8.48 | `productcellus1`; 1606 | Chronological complete-cell product through `K_c` cells. |
| 8.49 | `eq:gb-splice-lower`; 1618 | On all-good event, log norm at deterministic maximizing degree is at least sum of clipped core logs minus the actual loss sum, via vector-norm telescoping. |
| 8.50 | `eq:gb-splice-upper`; 1628 | Simultaneously for all degrees, log product norm is at most sum of clipped core logs plus `C K_c W log W`, by submultiplicativity and three reset sites. |
| 8.51 | `eq:gb-pressure-sandwich`; 1645 | Normalized maximal product growth differs from deterministic maximal pressure by `O_P(W log W/ell_W+p_W log W+log^(3/2)W/sqrt(K_c))`. Must include the all-good failure control when stating unconditioned convergence. |
| 8.52 | `eq:gb-remainder-cost`; 1654 | An incomplete interval with fewer than `c_W` sites changes unnormalized log pressure by at most `C ell_W log W`; both norm and inverse norm are needed. |

### Independent anchor and deterministic calibration (8.53)-(8.62)

| PDF | TeX label; line | Statement / dependency |
| --- | --- | --- |
| 8.53 | `eq:gb-anchor-sites`; 1670 | Independent ring with `m_M=K_W c_W+3`, exactly `K_W` complete cells and three terminal sites. |
| 8.54 | `eq:gb-anchor-two-transfers`; 1679 | Last three sites define `R_partial^anc`; preceding complete cells define `R_out^anc`, with the correct orientation. |
| 8.55 | `eq:gb-anchor-cleared-outside`; 1693 | `c_out^anc * wedge^r R_out^anc` is literally the complete-cell product. |
| 8.56 | `eq:gb-terminal-pressure`; 1725 | Lemma 8.3: anchor log determinant equals maximal complete-cell log norm plus `o_P(M_W)`. |
| 8.57 | `eq:gb-anchor-two-identities`; 1746 | `det(X_M-zI)=sign*c*D_Theta` and cleared outside product `=c*wedge^r Theta`. |
| 8.58 | `eq:gb-anchor-value-to-coeff`; 1776 | Terminal value log equals coefficient norm log plus `o_P(M_W)`; conditional cap `T=epsilon M_W`, reverse fresh-entry event, and endpoint/outside failure. |
| 8.59 | `eq:gb-anchor-pressure`; 1810 | `M_W^(-1) log |det(X_M-zI)| = K_W/M_W * max_r Phi_(W,r)+o_P(1)`. |
| 8.60 | `eq:gb-anchor-errors`; 1819 | Explicit errors `O_P(W^(-1/200)log W+W^(-1/2)log^(3/2)W+W^(-1/400)log^(3/2)W)+o_P(1)`. |
| 8.61 | `eq:gb-pressure-calibration`; 1831 | Corollary 8.4: deterministic pressure divided by `ell_W` tends to disk potential, comparing Proposition 3.8 and (8.59). |
| 8.62 | `eq:gb-anchor-rounding`; 1843 | Clipping bounds the normalization discrepancy by `C W log W/M_W=o(1)` because `K_W ell_W=M_W-3W`. |

### Target, direct branch, energy, and replacement (8.63)-(8.69)

| PDF | TeX label; line | Statement / dependency |
| --- | --- | --- |
| 8.63 | `eq:gb-target-cell-count`; 1852 | For `N>=M_W`, reserve three final sites and set `K_N=floor((m-3)/c_W)`. |
| 8.64 | `eq:gb-target-rounding`; 1859 | `K_N>=K_W-1 -> infinity` and `K_N ell_W/N=1+O(ell_W/N)`; the exact integer model actually permits the stronger `K_N>=K_W`. |
| 8.65 | `eq:gb-target-actual-substitution`; 1877 | Condition on actual target outside sites and the terminal `C_(m-2),B_m` endpoints; use `Theta=R_out^tar`. |
| 8.66 | `eq:gb-target-terminal-pressure`; 1894 | Target log determinant equals maximal cleared outside log norm plus `o_P(N)`, including all incomplete outside sites. |
| 8.67 | `eq:gb-global-logdet`; 1904 | Each fixed `z`: normalized target log determinant tends to `U(z)`. Long branch uses (8.51),(8.52),(8.61),(8.66); short branch uses Proposition 3.8 directly. |
| 8.68 | `eq:gb-HS`; 1933 | Normalized Hilbert--Schmidt energy equals `(3WN)^(-1) sum_(3NW atoms) xi^2` and tends to `1` in probability. For Rademacher this energy is identically `1` on the support. |
| 8.69 | `eq:gb-replacement-logdet`; 1944 | Difference from a same-dimension Ginibre normalized log determinant tends to zero for almost every `z`; apply the in-probability Tao--Vu replacement principle and the reference ESD limit. |

The direct branch after (8.67) has no separate equation label:
`N<M_W` implies `W/N^0.99 -> infinity`; choose, for example,
`omega=1/20`, so `8/9+omega<0.99`. The two dimension subsequences may
alternate. Either a filter-level two-region argument or a proved
subsequence recombination is required; one cannot assume an eventually
fixed branch.

## Final assembly crosswalk: source written, checks pending

The following map identifies the concrete declarations now written for
(8.52)-(8.69). **Status: `written-pending-check` for this final assembly
chain.** Declaration names have been checked against the source files;
this is not a claim that these files have passed Lean, that the complete
dependency build succeeds, or that the final axiom/signature audit has
finished. Successful independent checks of the supporting
`MesoscopicScales`, `CellConcentration`, and `CellCoordinates` modules do
not promote their downstream assembly to checked status. File names below
are relative to `Section8/BernoulliSection8`, and declaration names are in
namespace `BernoulliSection8` unless indicated otherwise.

| PDF obligation | Written declarations and exact role | Status |
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

The written caller-facing scope is the **symmetric Rademacher
specialization** of Theorem 2.8, with independent entries; it does not
claim a symmetric matrix, nor every subgaussian atom. The public
signatures contain the explicit Cook, Nguyen (with subgaussian bound at
least one), and Section 3 inputs, positive widths, positive `s` with
`m=s+3`, `W -> infinity`, and `W/log N -> infinity`. Full compilation and
inspection of the expanded final signatures remain required before
changing any assembly status above to checked.

## Probability ledger required to close the argument

The source roadmap refers to a “final probability ledger” but does not
print a separate ledger at the end of Section 8. The following bounds are
the actual obligations implicit in its proof.

| Error or exceptional event | Bound needed | Why it vanishes |
| --- | --- | --- |
| All target interfaces | `C (N/W) exp(-cW)` | `W/log N -> infinity`; this is precisely where the logarithmic bandwidth hypothesis is used. |
| All anchor interfaces | `C (M_W/W) exp(-cW)` | `M_W` is a fixed power of `W` up to rounding. |
| Core and two endpoints of one cell | `(s_W+2) exp(-cW)` initially | Polynomial factor absorbed by a smaller positive exponential rate, for sufficiently large `W`. |
| Fresh terminal entry maximum | `C W^2 exp(-cW)` initially | Same exponential absorption; for Rademacher and a sufficiently large threshold the event holds everywhere on the support. |
| Independent-cell fluctuation | `2 exp(-u)` at size `C ell_W log W sqrt(K_c(log W+u))` | Take fixed `u` for `O_P`, or a chosen diverging `u` for a concrete probability bound. |
| Total reset loss | `E sum L/(K_c ell_W) <= C(W log W/ell_W+p_W log W+exp(-cW)log W)` | `ell_W/W >= W^(1/200)` and `p_W log W=O(W^(-1/2)log^(3/2)W)+o(1)`. |
| Terminal lower comparison at scale `D` | `p_W+C W log W/(epsilon D)` plus endpoint/outside failure | `D=M_W` for anchor; `D=N>=M_W` for long target. Zero determinant belongs to this bad event. |
| Terminal reverse comparison | deterministic `C W log W` on fresh maximum event | Divide by `D>=M_W`; add exponential maximum-event failure. |
| Cell remainder | `C ell_W log W/N` | Long target has `N>=M_W` and `M_W/ell_W` of order `W^(1/200)`. |
| Normalization rounding | at most a constant times `ell_W log W/N` for target, `W log W/M_W` for anchor | Clipped pressure is bounded by `C ell_W log W`; the same scale relations apply. |

The pressure sandwich alone is not an unconditional statement for
arbitrarily many cells: the exceptional probability must include the
number of interfaces. Similarly, **`K_c -> infinity` alone does not imply
its concentration error vanishes**, since it contains
`log^(3/2) W / sqrt(K_c)`. The actual applications have
`K_c=K_W` or `K_c=K_N>=K_W-1`, which is sufficient. This is a qualification
of the informal roadmap, not a failure of its chosen scales.

## Zero determinants, total functions, and conditional frames

1. **Singular Bernoulli interfaces have positive probability.** The proof
   does not claim almost-sure invertibility. It first defines all
   polynomial cleared operators and clipped core logs on all samples,
   then uses interface inverses on the simultaneous good event. A final
   limit can use any measurable finite default value on an exceptional
   event only after proving that event has probability tending to zero.

2. **The global determinant can vanish even on good interfaces.** The
   terminal polynomial may vanish by cancellation. Since its coefficient
   norm is positive on endpoint regularity, the capped estimate with all
   caps yields `P(D_Theta=0 | outside) <= p_W`. More directly, a zero
   determinant belongs to every lower-tail event used for (8.58) and
   (8.66). This controls the real-versus-extended-log convention.

3. **Actual reset loss is not the scalar pairing loss.** The pairing `Z`
   can vanish while `core*reset*v_hat` is nonzero; (8.42) then supplies a
   trivial lower bound, but the capped scalar loss still dominates the
   capped actual loss. On the all-interface-good event, inverse product
   bounds keep the actual log norms finite and make the cap inactive.
   No claim that `Z` is nonzero on that event is justified.

4. **Define the off-good loss explicitly.** Formula (8.43) contains a
   possible `(-infinity)-(-infinity)`. The surrounding sentence supplies
   the intended convention: if either logged norm vanishes, assign the
   cap. This produces a bounded measurable real function, agrees with
   the displayed difference on the good event, and suffices for its
   conditional estimate because that estimate is multiplied by `1_H`.

5. **Measurable frame choices cannot be silently assumed.** The
   recursive incoming wedge has a measurable normalization/fallback
   construction. A top singular frame of the random core either needs a
   measurable selection proof or may be chosen pointwise after fixing
   outside data, provided the resulting actual-loss integral is first
   shown measurable and the uniform fixed-data estimate is lifted by a
   proved conditional Fubini/distribution argument. The repository's
   `RandomQConditional` technique is a relevant precedent. The proof
   does not need a globally measurable internal RRQR selector.

6. **A.e. spectral exclusions for Bernoulli are available but weaker.**
   For each finite size a Bernoulli matrix has finitely many possible
   samples; the union of their spectra over all integer widths/site
   counts is countable. Off this deterministic planar-null set every
   sampled determinant is nonzero. This can serve the final a.e.-`z`
   circular-law statement, but it does not prove Proposition 8.2's
   assertion for every fixed `z`, nor substitute for its quantitative
   terminal argument.

7. **Small widths are asymptotically irrelevant, but must be handled
   honestly.** Bounds written as `C W log W` cannot generally hold at
   `W=1`, and the degree-union Hoeffding bound needs a positive logarithmic
   baseline. Stating the estimates for sufficiently large `W`, or using
   `log(eW)`/`log(W+1)` with proved comparisons, is a sufficient faithful
   variant. It is not a gap in the limiting theorem.

## Existing generic reuse versus density-dependent results

These are verified source-level reuse candidates; importing a file with
“Density” in its name is not itself a density assumption. Inspect the
actual theorem parameter list.

| Existing module / declaration | Applicable reuse and qualification |
| --- | --- |
| `CyclicPhysicalModel.lean`: `densityCyclicMatrix`, `densityShiftedCyclicMatrix_eq_sub_scalar`, `densityCyclicLogDet_eq_polynomial_trace` | Actual deterministic three-neighbor cyclic matrix and polynomial Fock identity. Its `Real.log` convention still requires the discrete zero-event argument. Coordinate parameter is `m=s+3`; use `s>=1` for the printed `m>=4` model. |
| `PhysicalIIDEmbedding.lean`: `physicalRowsFromSequence_measurePreserving` and `physicalRowsFromSquare_measurePreserving` | Concrete IID law transport and independent coordinate embeddings; no density needed. |
| `PhysicalProfile.lean`: `physicalProfile_row`, `physicalProfile_column`, and `blockNormalization_sq` | Doubly stochastic scalar variance profile and normalization identities. |
| `DensityEnergyLimit.lean`: `intervalMeanAtomSquare_tendsto_of_second_moment`, `density_ring_energy_limit_of_second_moment` | Energy convergence under only the appropriate second-moment/probability assumptions; directly applicable to Bernoulli after constructing the law. The separate `density_ring_energy_limit` wrapper does use bounded density. |
| `DimensionReplacement.lean`: `taoVuReplacementPrinciple_sequence` | Already-proved arbitrary dimension-sequence form of Tao--Vu; no new replacement-principle input should be requested. |
| `DiskReferenceLaw.lean`: `circularMeasure_log_potential`; `DiagonalDiskReference.lean`: `diagonalDiskReference_logPotential_limit_sequence`, `diagonalDiskReference_esd_limit_sequence` | A diagonal IID disk reference has the same potential and ESD limit as the target disk, with proved bounded energy. Using this reference instead of Ginibre is a sufficient proved reformulation of the final replacement step. |
| `CircularLawFromPotential.lean`: `physical_circularLaw_of_logPotential` | Generic second-moment physical model to disk-reference replacement bridge; check the current signature's moment and log-potential premises. |
| `WeakCircularLaw.lean`: `circularLaw_boundedContinuousMap_of_compactSupport` | Generic upgrade from compact-support test functions to bounded continuous tests. |
| Density-based affine logarithm, packet probability, integrated Hodge, and seam theorems in Section 10 | Their bounded-density hypotheses cannot be instantiated by Rademacher. Their deterministic algebra or generic probability lemmas may be reused separately. |

`FORMALIZATION_MAP.md` now maps every numbered result and every equation
to the written implementation, including the concrete packet/cell laws,
conditional integration, uniform rates, and final assembly. Its explicit
variants include matrix-prefix losses in place of a recursive random
wedge, a retained ambient interface error, and a Parseval terminal upper
tail. The intentionally external Cook, Nguyen, and Section 3 inputs are
separate from the still-pending normal compilation and final signature
audit. A clean `#print axioms` report alone does not show that a theorem
has no additional parameters; both checks remain required.
