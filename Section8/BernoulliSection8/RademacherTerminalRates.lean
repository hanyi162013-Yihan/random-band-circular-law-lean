import BernoulliSection8.RademacherBoundarySmallBall
import BernoulliSection8.CookRates
import BernoulliSection9.TerminalComparisonNumerics

/-! # Numerical rates of the actual Rademacher terminal estimate

All constants below are determined by the approved Cook input. The fresh
packet is the variance-one Rademacher family, so the coordinate exposure
threshold is at most `7W`. The resulting terminal loss is bounded by a
fixed multiple of `W log(eW)`, and its exact failure probability times
`log(eW)` tends to zero.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection9.TerminalAssembly
open BernoulliSection10 BernoulliLinearAlgebra

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem rademacherExposureThreshold_le (W : ℕ) (hW : 0 < W) :
    terminalConcreteExposureThreshold (rademacherPacketFamily W) W ≤ 7 * (W : ℝ) := by
  let N := Fintype.card (ThreeBlockVariable (Fin W))
  letI : Nonempty (Fin W) := Fin.pos_iff_nonempty.mp hW
  letI : Nonempty (ThreeBlockVariable (Fin W)) := threeBlockVariable_nonempty
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (show 1 ≤ W by omega)
  have hNpos : 0 < N := Fintype.card_pos
  have hN : (N : ℝ) ≤ 9 * (W : ℝ) ^ 2 := by
    have h := card_threeBlockVariable_le_index_sq (w := Fin W)
    have heq : Fintype.card (ThreeBlockIndex (Fin W)) *
        Fintype.card (ThreeBlockIndex (Fin W)) = 9 * W ^ 2 := by
      simp [ThreeBlockIndex, ThreeBlockOuter]
      ring
    rw [heq] at h
    exact_mod_cast h
  have hlog : Real.log (2 * (N : ℝ)) ≤ 18 * (W : ℝ) ^ 2 := by
    have hp : 0 < 2 * (N : ℝ) := by positivity
    exact (Real.log_le_sub_one_of_pos hp).trans (by nlinarith)
  unfold terminalConcreteExposureThreshold packetCoordinateMaxThreshold
  apply max_le
  · linarith
  · unfold familyCoordinateMaxThreshold
    simp only [rademacherPacketFamily_subgaussianParameter, NNReal.coe_one, mul_one]
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · change 2 * ((W : ℝ) + Real.log (2 * (N : ℝ))) ≤ (7 * (W : ℝ)) ^ 2
      nlinarith

theorem tendsto_rademacherBoundaryBadProbability_mul_logScale
    (cook : CookDeformedSquareInput) :
    Tendsto (fun W : ℕ => rademacherBoundaryBadProbability cook W * densityLogScale W)
      atTop (𝓝 0) := by
  have h0 := tendsto_exp_neg_width_mul_logScale (c := 1) (by norm_num)
  have h1 := tendsto_uniformCookFailureBound_mul_logScale
    (cook.cookC (terminalCanonicalFirstCookExponent 1))
    (cook.c_pos (terminalCanonicalFirstCookExponent 1))
  have h2 := tendsto_uniformCookFailureBound_mul_logScale
    (cook.cookC (terminalCanonicalSecondCookExponent cook 1))
    (cook.c_pos (terminalCanonicalSecondCookExponent cook 1))
  convert h0.add (h1.add h2) using 1 <;>
    simp [rademacherBoundaryBadProbability, terminalUniformBadProbability, add_mul]

theorem tendsto_rademacherBoundaryBadProbability (cook : CookDeformedSquareInput) :
    Tendsto (rademacherBoundaryBadProbability cook) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (rademacherBoundaryBadProbability_nonneg cook)) _
    (tendsto_rademacherBoundaryBadProbability_mul_logScale cook)
  filter_upwards [eventually_gt_atTop 0] with W hW
  have hL : 1 ≤ densityLogScale W := by
    rw [densityLogScale_eq hW]
    have hlog := Real.log_nonneg (by exact_mod_cast hW : (1 : ℝ) ≤ W)
    linarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hL
    (rademacherBoundaryBadProbability_nonneg cook W)

/-- A coarse fixed constant, independent of width, shift, endpoints,
outside boundary relation and exterior degree. -/
def rademacherTerminalLossConstant (cook : CookDeformedSquareInput) : ℝ :=
  160 + 6 * cook.beta (terminalCanonicalFirstCookExponent 1) +
    6 * cook.beta (terminalCanonicalSecondCookExponent cook 1)

theorem rademacherTerminalLossConstant_pos (cook : CookDeformedSquareInput) :
    0 < rademacherTerminalLossConstant cook := by
  have h1 := cook.beta_pos (terminalCanonicalFirstCookExponent 1)
  have h2 := cook.beta_pos (terminalCanonicalSecondCookExponent cook 1)
  unfold rademacherTerminalLossConstant
  positivity

private theorem comparisonPolynomialBase_le
    (W : ℕ) (hW : 160 ≤ W) (z : ℂ) (hz : ‖z‖ ≤ (W : ℝ)) :
    terminalComparisonPolynomialBase (Fin W) z ≤ (W : ℝ) ^ 4 := by
  have hW160 : (160 : ℝ) ≤ W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by linarith
  unfold terminalComparisonPolynomialBase
  apply max_le (one_le_pow₀ hW1)
  simp only [BernoulliSection10.card_threeBlockIndex, Fintype.card_fin, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  calc
    ((3 * (W : ℝ)) * (3 * W) + 1) * (1 + ‖z‖) ≤
        (10 * (W : ℝ) ^ 2) * (2 * W) := by gcongr <;> nlinarith
    _ ≤ (W : ℝ) ^ 4 := by
      nlinarith [mul_nonneg (show 0 ≤ (W : ℝ) - 20 by linarith)
        (pow_nonneg (Nat.cast_nonneg W : (0 : ℝ) ≤ W) 3)]

private theorem reversePolynomialBase_le
    (W : ℕ) (hW : 160 ≤ W) (z : ℂ) (hz : ‖z‖ ≤ (W : ℝ)) :
    terminalReversePolynomialBase (Fin W) z
      (terminalConcreteExposureThreshold (rademacherPacketFamily W) W) ≤ (W : ℝ) ^ 5 := by
  have hW160 : (160 : ℝ) ≤ W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hM := rademacherExposureThreshold_le W (by omega)
  have hM0 : 0 ≤ terminalConcreteExposureThreshold (rademacherPacketFamily W) W :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (packetCoordinateMaxThreshold_one_le _ _)
  unfold terminalReversePolynomialBase
  apply max_le (one_le_pow₀ hW1)
  simp only [BernoulliSection10.card_threeBlockIndex, Fintype.card_fin, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  calc
    ((3 * (W : ℝ)) * (3 * W) + 1) * (1 + ‖z‖) *
        (terminalConcreteExposureThreshold (rademacherPacketFamily W) W + ‖z‖) ≤
        (10 * (W : ℝ) ^ 2) * (2 * W) * (8 * W) := by
          gcongr <;> nlinarith
    _ ≤ (W : ℝ) ^ 5 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hW160) (pow_nonneg (Nat.cast_nonneg W : (0 : ℝ) ≤ W) 4)]

private theorem terminalUniformValueLoss_le
    (cook : CookDeformedSquareInput) (W : ℕ) (hW : 160 ≤ W) :
    terminalUniformValueLoss cook W 1 ≤
      (126 + 6 * cook.beta (terminalCanonicalFirstCookExponent 1) +
        6 * cook.beta (terminalCanonicalSecondCookExponent cook 1)) *
        (W : ℝ) * Real.log W := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hW3 : (3 : ℝ) ≤ W := by exact_mod_cast (show 3 ≤ W by omega)
  have hl0 : 0 ≤ Real.log (W : ℝ) := Real.log_nonneg (by linarith)
  have hl2 : Real.log 2 ≤ Real.log (W : ℝ) := Real.log_le_log (by norm_num) (by linarith)
  have hl3 : Real.log 3 ≤ Real.log (W : ℝ) := Real.log_le_log (by norm_num) hW3
  have hl2W : Real.log (2 * (W : ℝ)) ≤ 2 * Real.log W := by
    rw [Real.log_mul (by norm_num) hW0.ne']
    linarith
  have hl3W : Real.log (3 * (W : ℝ)) ≤ 2 * Real.log W := by
    rw [Real.log_mul (by norm_num) hW0.ne']
    linarith
  have hb1 := (cook.beta_pos (terminalCanonicalFirstCookExponent 1)).le
  have hb2 := (cook.beta_pos (terminalCanonicalSecondCookExponent cook 1)).le
  have hlog :
      -Real.log (terminalUniformDeterminantFactor cook W 1) +
        Real.log (terminalUniformGramThresholdFactor W 1) =
      4 * W * Real.log 2 + 32 * W * Real.log (2 * (W : ℝ)) +
        3 * W * cook.beta (terminalCanonicalFirstCookExponent 1) * Real.log (3 * (W : ℝ)) +
        3 * W * cook.beta (terminalCanonicalSecondCookExponent cook 1) * Real.log (3 * (W : ℝ)) +
        58 * W * Real.log (W : ℝ) := by
    simp only [terminalUniformDeterminantFactor, terminalUniformGramThresholdFactor,
      terminalCanonicalThreshold, terminalCanonicalThresholdExponent, strongRRQRExponent,
      Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow, Real.log_inv]
    rw [Real.log_rpow (by positivity), Real.log_rpow (by positivity),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 29 hW0.ne'),
      Real.log_pow]
    norm_num
    ring
  unfold terminalUniformValueLoss
  apply max_le
  · positivity
  · rw [hlog]
    calc
      _ ≤ 4 * W * Real.log (W : ℝ) + 32 * W * (2 * Real.log (W : ℝ)) +
          3 * W * cook.beta (terminalCanonicalFirstCookExponent 1) * (2 * Real.log (W : ℝ)) +
          3 * W * cook.beta (terminalCanonicalSecondCookExponent cook 1) * (2 * Real.log (W : ℝ)) +
          58 * W * Real.log (W : ℝ) := by gcongr
      _ = _ := by ring

/-- Explicit `O(W log(eW))` bound for the loss occurring in the actual
normalized boundary and fixed-frame capped estimates. -/
theorem rademacherBoundaryBaseLoss_le
    (cook : CookDeformedSquareInput) (W : ℕ) (z : ℂ)
    (hW : 160 ≤ W) (hz : 3 * ‖z‖ ^ 2 ≤ (W : ℝ)) :
    rademacherBoundaryBaseLoss cook W z ≤
      rademacherTerminalLossConstant cook * (W : ℝ) * densityLogScale W := by
  have hW0 : 0 < W := by omega
  have hw0 : (0 : ℝ) ≤ W := by positivity
  have hshift : ‖packetRowScale W * z‖ ≤ (W : ℝ) := by
    simpa using packetRowScale_shift_bound W z hW0 hz
  have hc := log_threeBlockConcreteComparisonConstant_le_card_mul_log_base
    (Fin W) (packetRowScale W * z)
  have hcp := Real.log_le_log
    (lt_of_lt_of_le zero_lt_one (terminalComparisonPolynomialBase_one_le _ _))
    (comparisonPolynomialBase_le W hW _ hshift)
  rw [Real.log_pow] at hcp
  have hM : 0 ≤ terminalConcreteExposureThreshold (rademacherPacketFamily W) W :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (packetCoordinateMaxThreshold_one_le _ _)
  have hr := terminalReverseLoss_le_card_mul_log_polynomialBase
    (Fin W) (packetRowScale W * z)
    (terminalConcreteExposureThreshold (rademacherPacketFamily W) W) (by positivity)
  have hrp := Real.log_le_log
    (lt_of_lt_of_le zero_lt_one (terminalReversePolynomialBase_one_le _ _ _))
    (reversePolynomialBase_le W hW _ hshift)
  rw [Real.log_pow] at hrp
  have hv := terminalUniformValueLoss_le cook W hW
  simp only [BernoulliSection10.card_threeBlockIndex, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_ofNat] at hc hr
  have hcl : Real.log (threeBlockConcreteComparisonConstant (W := Fin W) (packetRowScale W * z)) ≤
      12 * W * Real.log (W : ℝ) := by
    calc
      _ ≤ 3 * (W : ℝ) * Real.log (terminalComparisonPolynomialBase (Fin W) (packetRowScale W * z)) := hc
      _ ≤ 3 * (W : ℝ) * (4 * Real.log (W : ℝ)) := by gcongr
      _ = _ := by ring
  have hrl : terminalReverseLoss (Fin W) (packetRowScale W * z)
      (terminalConcreteExposureThreshold (rademacherPacketFamily W) W) ≤
      15 * W * Real.log (W : ℝ) := by
    calc
      _ ≤ 3 * (W : ℝ) * Real.log (terminalReversePolynomialBase (Fin W)
          (packetRowScale W * z) (terminalConcreteExposureThreshold (rademacherPacketFamily W) W)) := hr
      _ ≤ 3 * (W : ℝ) * (5 * Real.log (W : ℝ)) := by gcongr
      _ = _ := by ring
  have hl0 : 0 ≤ Real.log (W : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ W by omega))
  have hcombined : rademacherBoundaryBaseLoss cook W z ≤
      rademacherTerminalLossConstant cook * (W : ℝ) * Real.log W := by
    unfold rademacherBoundaryBaseLoss terminalUniformBaseLoss rademacherTerminalLossConstant
    nlinarith [mul_nonneg hw0 hl0]
  have hl : Real.log (W : ℝ) ≤ densityLogScale W := by
    rw [densityLogScale_eq hW0]
    linarith
  exact hcombined.trans (mul_le_mul_of_nonneg_left hl
    (mul_nonneg (rademacherTerminalLossConstant_pos cook).le hw0))

theorem rademacherBoundaryBaseLoss_le_of_threshold
    (cook : CookDeformedSquareInput) (W : ℕ) (z : ℂ)
    (hW : rademacherBoundaryWidthThreshold cook z ≤ W) :
    rademacherBoundaryBaseLoss cook W z ≤
      rademacherTerminalLossConstant cook * (W : ℝ) * densityLogScale W := by
  have hlarge : 160 ≤ terminalCanonicalLargeWThreshold cook 1
      (cook.subgaussianBound : ℝ) :=
    (by norm_num [terminalCanonicalPivotConstant] : 160 ≤ 2 * terminalCanonicalPivotConstant).trans
      (le_max_left _ _)
  have h160 : 160 ≤ W := hlarge.trans ((le_max_left _ _).trans hW)
  have hz : 3 * ‖z‖ ^ 2 ≤ (W : ℝ) :=
    (Nat.le_ceil _).trans (by
      exact_mod_cast ((le_max_right _ _).trans ((le_max_right _ _).trans hW) :
        Nat.ceil (3 * ‖z‖ ^ 2) ≤ W))
  exact rademacherBoundaryBaseLoss_le cook W z h160 hz

theorem rademacherBoundaryBaseLoss_eventually_le
    (cook : CookDeformedSquareInput) (z : ℂ) :
    ∀ᶠ W : ℕ in atTop, rademacherBoundaryBaseLoss cook W z ≤
      rademacherTerminalLossConstant cook * (W : ℝ) * densityLogScale W := by
  filter_upwards [eventually_ge_atTop (rademacherBoundaryWidthThreshold cook z)] with W hW
  exact rademacherBoundaryBaseLoss_le_of_threshold cook W z hW

end BernoulliSection8
