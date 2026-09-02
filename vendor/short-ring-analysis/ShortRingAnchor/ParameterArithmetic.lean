import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Parameter arithmetic for Proposition 3.6

This file formalizes the deterministic exponent bookkeeping in formulas
(3.9)--(3.10) of Proposition 3.6 of `Circular_Law_Combined_Manuscript.pdf`.
It contains no random-matrix or probability input.

In the source proof, `beta = 8/9 + omega`, with `0 < omega < 1/9`, and
positive parameters `chi`, `kappa`, and `tau` are chosen so that

`1/2 + chi < beta`, `kappa < chi/4`, `tau < beta/8`, and
`tau + 3*kappa < 9*beta/8 - 1`.  These are formula (3.9).

Formula (3.10) then contains the two deterministic rates

`M^(1+tau+3*kappa) W^(-9/8)` and `M^tau W^(-1/8) log M`.

We use real powers (`Real.rpow`) throughout, since the exponents are real.
-/

open Filter

noncomputable section

namespace ShortRingAnchor

/-- Formula (3.9), including the strict positivity implicit in the words
"choose `chi`, `kappa`, `tau > 0` so small that". -/
def HardEdgeAdmissible (beta chi kappa tau : Real) : Prop :=
  0 < chi /\
  0 < kappa /\
  0 < tau /\
  1 / 2 + chi < beta /\
  kappa < chi / 4 /\
  tau < beta / 8 /\
  tau + 3 * kappa < 9 * beta / 8 - 1

/-- Formula (3.9) is feasible whenever `beta > 8/9`.

This is a constructive proof: we take

* `chi = (beta - 1/2)/2`,
* `kappa = min (chi/8) ((9*beta/8-1)/12)`, and
* `tau = min (beta/16) ((9*beta/8-1)/4)`.

Thus no density argument or choice axiom is hidden in the parameter
selection. -/
theorem exists_hardEdgeAdmissible {beta : Real}
    (hbeta : (8 / 9 : Real) < beta) :
    exists chi kappa tau, HardEdgeAdmissible beta chi kappa tau := by
  let chi : Real := (beta - 1 / 2) / 2
  let gap : Real := 9 * beta / 8 - 1
  let kappa : Real := min (chi / 8) (gap / 12)
  let tau : Real := min (beta / 16) (gap / 4)
  have hbeta_pos : 0 < beta :=
    (by norm_num : (0 : Real) < 8 / 9).trans hbeta
  have hgap : 0 < gap := by
    change 0 < 9 * beta / 8 - 1
    have hscaled := mul_pos (by norm_num : (0 : Real) < 9 / 8)
      (sub_pos.mpr hbeta)
    calc
      0 < (9 / 8 : Real) * (beta - 8 / 9) := hscaled
      _ = 9 * beta / 8 - 1 := by ring
  have hchi : 0 < chi := by
    dsimp only [chi]
    exact div_pos
      (sub_pos.mpr ((by norm_num : (1 / 2 : Real) < 8 / 9).trans hbeta))
      (by norm_num)
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    exact lt_min (by positivity) (by positivity)
  have htau : 0 < tau := by
    dsimp [tau]
    exact lt_min (by positivity) (by positivity)
  refine ⟨chi, kappa, tau, ?_⟩
  refine ⟨hchi, hkappa, htau, ?_, ?_, ?_, ?_⟩
  · dsimp [chi]
    linarith
  · have hkappa_le : kappa <= chi / 8 := min_le_left _ _
    linarith
  · have htau_le : tau <= beta / 16 := min_le_left _ _
    linarith
  · have htau_le : tau <= gap / 4 := min_le_right _ _
    have hkappa_le : kappa <= gap / 12 := min_le_right _ _
    change tau + 3 * kappa < gap
    linarith

/-- Source specialization of (3.9): for `beta = 8/9 + omega`, every
`omega > 0` gives admissible hard-edge parameters.  The source additionally
assumes `omega < 1/9`; that upper bound is irrelevant to this feasibility
step. -/
theorem exists_hardEdgeAdmissible_of_omega {omega : Real}
    (homega : 0 < omega) :
    exists chi kappa tau,
      HardEdgeAdmissible ((8 / 9 : Real) + omega) chi kappa tau := by
  apply exists_hardEdgeAdmissible
  linarith

/-- The exponent controlling the first term of (3.10) after substituting
`W >= M^beta`. -/
def hardEdgeFirstExponent (beta tau kappa : Real) : Real :=
  1 + tau + 3 * kappa - 9 * beta / 8

/-- The exponent controlling the second term of (3.10) after substituting
`W >= M^beta`. -/
def hardEdgeSecondExponent (beta tau : Real) : Real :=
  tau - beta / 8

/-- The last inequality in (3.9) says precisely that the first exponent
appearing after the bandwidth substitution is negative. -/
theorem hardEdgeFirstExponent_neg {beta chi kappa tau : Real}
    (h : HardEdgeAdmissible beta chi kappa tau) :
    hardEdgeFirstExponent beta tau kappa < 0 := by
  rcases h with ⟨_, _, _, _, _, _, hlast⟩
  dsimp [hardEdgeFirstExponent]
  linarith

/-- The inequality `tau < beta/8` in (3.9) says precisely that the second
exponent appearing after the bandwidth substitution is negative. -/
theorem hardEdgeSecondExponent_neg {beta chi kappa tau : Real}
    (h : HardEdgeAdmissible beta chi kappa tau) :
    hardEdgeSecondExponent beta tau < 0 := by
  rcases h with ⟨_, _, _, _, _, htau, _⟩
  simpa [hardEdgeSecondExponent] using sub_neg.mpr htau

/-- The first deterministic rate in formula (3.10). -/
def hardEdgeFirstRate (M W tau kappa : Real) : Real :=
  M ^ (1 + tau + 3 * kappa) * W ^ (-(9 / 8 : Real))

/-- The second deterministic rate in formula (3.10). -/
def hardEdgeSecondRate (M W tau : Real) : Real :=
  M ^ tau * W ^ (-(1 / 8 : Real)) * Real.log M

/-- Under `W >= M^beta`, the first rate in (3.10) is bounded by the pure
power with exponent `1 + tau + 3*kappa - 9*beta/8`.

This is the exact deterministic substitution made in the displayed
estimate following (3.9). -/
theorem hardEdgeFirstRate_le_rpow
    {M W beta tau kappa : Real}
    (hM : 1 <= M) (hW : M ^ beta <= W) :
    hardEdgeFirstRate M W tau kappa <=
      M ^ hardEdgeFirstExponent beta tau kappa := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hMbeta : 0 < M ^ beta := Real.rpow_pos_of_pos hMpos beta
  have hneg : (-(9 / 8 : Real)) <= 0 := by norm_num
  have hband := Real.rpow_le_rpow_of_nonpos hMbeta hW hneg
  calc
    hardEdgeFirstRate M W tau kappa
        <= M ^ (1 + tau + 3 * kappa) *
            (M ^ beta) ^ (-(9 / 8 : Real)) := by
          exact mul_le_mul_of_nonneg_left hband (Real.rpow_nonneg hMpos.le _)
    _ = M ^ hardEdgeFirstExponent beta tau kappa := by
          rw [<- Real.rpow_mul hMpos.le]
          rw [<- Real.rpow_add hMpos]
          congr 1
          simp only [hardEdgeFirstExponent]
          ring

/-- Under `W >= M^beta`, the second rate in (3.10) is bounded by
`M^(tau-beta/8) log M`. -/
theorem hardEdgeSecondRate_le_rpow_mul_log
    {M W beta tau : Real}
    (hM : 1 <= M) (hW : M ^ beta <= W) :
    hardEdgeSecondRate M W tau <=
      M ^ hardEdgeSecondExponent beta tau * Real.log M := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hMbeta : 0 < M ^ beta := Real.rpow_pos_of_pos hMpos beta
  have hneg : (-(1 / 8 : Real)) <= 0 := by norm_num
  have hband := Real.rpow_le_rpow_of_nonpos hMbeta hW hneg
  have hlog : 0 <= Real.log M := Real.log_nonneg hM
  calc
    hardEdgeSecondRate M W tau
        <= (M ^ tau * (M ^ beta) ^ (-(1 / 8 : Real))) * Real.log M := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hband (Real.rpow_nonneg hMpos.le tau)) hlog
    _ = M ^ hardEdgeSecondExponent beta tau * Real.log M := by
          congr 1
          rw [<- Real.rpow_mul hMpos.le]
          rw [<- Real.rpow_add hMpos]
          congr 1
          simp only [hardEdgeSecondExponent]
          ring

/-- A negative real power tends to zero at infinity, in the exponent form
used after (3.10). -/
theorem tendsto_rpow_atTop_zero_of_neg {d : Real} (hd : d < 0) :
    Tendsto (fun x : Real => x ^ d) atTop (nhds 0) := by
  simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hd)

/-- A negative real power still tends to zero after multiplication by one
logarithm.  This is the analytic fact used for the second term in (3.10). -/
theorem tendsto_rpow_mul_log_atTop_zero_of_neg {d : Real} (hd : d < 0) :
    Tendsto (fun x : Real => x ^ d * Real.log x) atTop (nhds 0) := by
  have h :=
    (isLittleO_log_rpow_atTop (neg_pos.mpr hd)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
  have hrpow : x ^ d = (x ^ (-d))⁻¹ := by
    simpa only [neg_neg] using Real.rpow_neg hx.le (-d)
  rw [hrpow]
  simp only [div_eq_mul_inv, mul_comm]

/-- Full deterministic conclusion for the first term in (3.10).

`M_n -> infinity` and the eventual high-band inequality
`W_n >= M_n^beta` force the first rate to tend to zero.  No separate
assumption `W_n -> infinity` is needed for this implication. -/
theorem hardEdgeFirstRate_tendsto_zero
    {M W : Nat -> Real} {beta chi kappa tau : Real}
    (hparam : HardEdgeAdmissible beta chi kappa tau)
    (hM : Tendsto M atTop atTop)
    (hW : ∀ᶠ n in atTop, M n ^ beta <= W n) :
    Tendsto (fun n => hardEdgeFirstRate (M n) (W n) tau kappa)
      atTop (nhds 0) := by
  have hMone : ∀ᶠ n in atTop, 1 <= M n := hM.eventually_ge_atTop 1
  apply squeeze_zero'
  · filter_upwards [hMone, hW] with n hnM hnW
    have hMn : 0 < M n := zero_lt_one.trans_le hnM
    have hWn : 0 < W n := (Real.rpow_pos_of_pos hMn beta).trans_le hnW
    exact mul_nonneg (Real.rpow_nonneg hMn.le _) (Real.rpow_nonneg hWn.le _)
  · filter_upwards [hMone, hW] with n hnM hnW
    exact hardEdgeFirstRate_le_rpow hnM hnW
  · exact (tendsto_rpow_atTop_zero_of_neg
      (hardEdgeFirstExponent_neg hparam)).comp hM

/-- Full deterministic conclusion for the second term in (3.10).

The logarithm costs less than every positive power, so the strict inequality
`tau < beta/8` makes this term tend to zero under the same bandwidth
condition. -/
theorem hardEdgeSecondRate_tendsto_zero
    {M W : Nat -> Real} {beta chi kappa tau : Real}
    (hparam : HardEdgeAdmissible beta chi kappa tau)
    (hM : Tendsto M atTop atTop)
    (hW : ∀ᶠ n in atTop, M n ^ beta <= W n) :
    Tendsto (fun n => hardEdgeSecondRate (M n) (W n) tau)
      atTop (nhds 0) := by
  have hMone : ∀ᶠ n in atTop, 1 <= M n := hM.eventually_ge_atTop 1
  apply squeeze_zero'
  · filter_upwards [hMone, hW] with n hnM hnW
    have hMn : 0 < M n := zero_lt_one.trans_le hnM
    have hWn : 0 < W n := (Real.rpow_pos_of_pos hMn beta).trans_le hnW
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hMn.le _) (Real.rpow_nonneg hWn.le _))
      (Real.log_nonneg hnM)
  · filter_upwards [hMone, hW] with n hnM hnW
    exact hardEdgeSecondRate_le_rpow_mul_log hnM hnW
  · exact (tendsto_rpow_mul_log_atTop_zero_of_neg
      (hardEdgeSecondExponent_neg hparam)).comp hM

end ShortRingAnchor
