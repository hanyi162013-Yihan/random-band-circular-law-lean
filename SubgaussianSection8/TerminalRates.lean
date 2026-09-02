import SubgaussianSection8.BoundarySmallBall
import BernoulliSection8.CookRates
import BernoulliSection9.TerminalComparisonNumerics

/-! # Numerical rates of the actual subgaussian terminal estimate

All constants below are determined by the approved Cook input. The fixed atom parameter is absorbed into the width
threshold, after which coordinate exposure is at most `W²`. The resulting terminal loss is bounded by a
fixed multiple of `W log(eW)`, and its exact failure probability times
`log(eW)` tends to zero.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace SubgaussianSection8
open BernoulliSection8

open BernoulliSection9 BernoulliSection9.TerminalAssembly
open BernoulliSection10 BernoulliLinearAlgebra

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private theorem exposureThreshold_le_sq
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (Ksg : Real) (hW : 64 <= W)
    (hsg : (X.subgaussianParameter : Real) <= Ksg)
    (hKsg : 0 <= Ksg) (hKsgW : Ksg <= (W : Real)) :
    terminalConcreteExposureThreshold X (W : Real) <= (W : Real) ^ 2 := by
  let w : Real := W
  let N : Nat := Fintype.card (ThreeBlockVariable (Fin W))
  have hWposNat : 0 < W := by omega
  letI : Nonempty (Fin W) := Fin.pos_iff_nonempty.mp hWposNat
  letI : Nonempty (ThreeBlockVariable (Fin W)) := threeBlockVariable_nonempty
  have hw : 64 <= w := by dsimp [w]; exact_mod_cast hW
  have hw0 : 0 <= w := by positivity
  have hw1 : 1 <= w := by linarith
  have hNposNat : 0 < N := Fintype.card_pos
  have hcard : N <= 9 * W ^ 2 := by
    calc
      N <= Fintype.card (ThreeBlockIndex (Fin W)) *
          Fintype.card (ThreeBlockIndex (Fin W)) :=
        card_threeBlockVariable_le_index_sq
      _ = 9 * W ^ 2 := by
        simp [ThreeBlockIndex]
        ring
  have hNreal : (N : Real) <= 9 * w ^ 2 := by
    dsimp [N, w]
    exact_mod_cast hcard
  have htwoNpos : 0 < (2 * (N : Real)) := by positivity
  have hlog : Real.log (2 * (N : Real)) <= 18 * w ^ 2 := by
    calc
      Real.log (2 * (N : Real)) <= 2 * (N : Real) - 1 :=
        Real.log_le_sub_one_of_pos htwoNpos
      _ <= 18 * w ^ 2 := by nlinarith
  have hinside :
      2 * (X.subgaussianParameter : Real) *
          ((w : Real) + Real.log (2 * (N : Real))) <= w ^ 4 := by
    have hsg0 : 0 <= (X.subgaussianParameter : Real) := by positivity
    have hsum0 : 0 <= w + Real.log (2 * (N : Real)) := by
      have : 1 <= 2 * (N : Real) := by exact_mod_cast (show 1 <= 2 * N by omega)
      exact add_nonneg hw0 (Real.log_nonneg this)
    calc
      2 * (X.subgaussianParameter : Real) *
          (w + Real.log (2 * (N : Real))) <=
          2 * Ksg * (w + Real.log (2 * (N : Real))) := by
            gcongr
      _ <= 2 * w * (w + 18 * w ^ 2) := by
            gcongr
      _ <= w ^ 4 := by nlinarith [sq_nonneg (w - 38)]
  unfold terminalConcreteExposureThreshold packetCoordinateMaxThreshold
  apply max_le
  · nlinarith [sq_nonneg w]
  · unfold familyCoordinateMaxThreshold
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · convert hinside using 1 <;> simp [w, N] <;> ring


theorem subgaussianExposureThreshold_le (Ξ : Atom) (W : ℕ)
    (hW : 64 ≤ W) (hparameter : (Ξ.parameter : ℝ) ≤ W) :
    terminalConcreteExposureThreshold (packetFamily Ξ W) W ≤ (W : ℝ) ^ 2 := by
  apply exposureThreshold_le_sq (packetFamily Ξ W) (Ξ.parameter : ℝ) hW
  · simp
  · positivity
  · exact hparameter

theorem tendsto_subgaussianBoundaryBadProbability_mul_logScale (Ξ : Atom)
    (cook : CookInput Ξ) :
    Tendsto (fun W : ℕ => (subgaussianBoundaryBadProbability Ξ) cook W * densityLogScale W)
      atTop (𝓝 0) := by
  have h0 := tendsto_exp_neg_width_mul_logScale (c := 1) (by norm_num)
  have h1 := tendsto_uniformCookFailureBound_mul_logScale
    (cook.cookC (terminalCanonicalFirstCookExponent 1))
    (cook.c_pos (terminalCanonicalFirstCookExponent 1))
  have h2 := tendsto_uniformCookFailureBound_mul_logScale
    (cook.cookC (terminalCanonicalSecondCookExponent cook 1))
    (cook.c_pos (terminalCanonicalSecondCookExponent cook 1))
  convert h0.add (h1.add h2) using 1 <;>
    simp [(subgaussianBoundaryBadProbability Ξ), terminalUniformBadProbability, add_mul]

theorem tendsto_subgaussianBoundaryBadProbability (Ξ : Atom) (cook : CookInput Ξ) :
    Tendsto ((subgaussianBoundaryBadProbability Ξ) cook) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall ((subgaussianBoundaryBadProbability_nonneg Ξ) cook)) _
    ((tendsto_subgaussianBoundaryBadProbability_mul_logScale Ξ) cook)
  filter_upwards [eventually_gt_atTop 0] with W hW
  have hL : 1 ≤ densityLogScale W := by
    rw [densityLogScale_eq hW]
    have hlog := Real.log_nonneg (by exact_mod_cast hW : (1 : ℝ) ≤ W)
    linarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hL
    ((subgaussianBoundaryBadProbability_nonneg Ξ) cook W)

/-- A coarse fixed constant, independent of width, shift, endpoints,
outside boundary relation and exterior degree. -/
def subgaussianTerminalLossConstant (Ξ : Atom) (cook : CookInput Ξ) : ℝ :=
  170 + 6 * cook.beta (terminalCanonicalFirstCookExponent 1) +
    6 * cook.beta (terminalCanonicalSecondCookExponent cook 1)

theorem subgaussianTerminalLossConstant_pos (Ξ : Atom) (cook : CookInput Ξ) :
    0 < (subgaussianTerminalLossConstant Ξ) cook := by
  have h1 := cook.beta_pos (terminalCanonicalFirstCookExponent 1)
  have h2 := cook.beta_pos (terminalCanonicalSecondCookExponent cook 1)
  unfold subgaussianTerminalLossConstant
  positivity

private theorem comparisonPolynomialBase_le (Ξ : Atom)
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

private theorem reversePolynomialBase_le (Ξ : Atom)
    (W : ℕ) (hW : 160 ≤ W) (hparameter : (Ξ.parameter : ℝ) ≤ W) (z : ℂ) (hz : ‖z‖ ≤ (W : ℝ)) :
    terminalReversePolynomialBase (Fin W) z
      (terminalConcreteExposureThreshold ((packetFamily Ξ) W) W) ≤ (W : ℝ) ^ 6 := by
  have hW160 : (160 : ℝ) ≤ W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hM := (subgaussianExposureThreshold_le Ξ) W (by omega) hparameter
  have hM0 : 0 ≤ terminalConcreteExposureThreshold ((packetFamily Ξ) W) W :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (packetCoordinateMaxThreshold_one_le _ _)
  unfold terminalReversePolynomialBase
  apply max_le (one_le_pow₀ hW1)
  simp only [BernoulliSection10.card_threeBlockIndex, Fintype.card_fin, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  calc
    ((3 * (W : ℝ)) * (3 * W) + 1) * (1 + ‖z‖) *
        (terminalConcreteExposureThreshold ((packetFamily Ξ) W) W + ‖z‖) ≤
        (10 * (W : ℝ) ^ 2) * (2 * W) * (2 * (W : ℝ) ^ 2) := by
          gcongr <;> nlinarith
    _ ≤ (W : ℝ) ^ 6 := by
      nlinarith [mul_nonneg (show 0 ≤ (W : ℝ) - 40 by linarith) (pow_nonneg (Nat.cast_nonneg W : (0 : ℝ) ≤ W) 5)]

private theorem terminalUniformValueLoss_le (Ξ : Atom)
    (cook : CookInput Ξ) (W : ℕ) (hW : 160 ≤ W) :
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
theorem subgaussianBoundaryBaseLoss_le (Ξ : Atom)
    (cook : CookInput Ξ) (W : ℕ) (z : ℂ)
    (hW : 160 ≤ W) (hparameter : (Ξ.parameter : ℝ) ≤ W) (hz : 3 * ‖z‖ ^ 2 ≤ (W : ℝ)) :
    (subgaussianBoundaryBaseLoss Ξ) cook W z ≤
      (subgaussianTerminalLossConstant Ξ) cook * (W : ℝ) * densityLogScale W := by
  have hW0 : 0 < W := by omega
  have hw0 : (0 : ℝ) ≤ W := by positivity
  have hshift : ‖packetRowScale W * z‖ ≤ (W : ℝ) := by
    simpa using (packetRowScale_shift_bound Ξ) W z hW0 hz
  have hc := log_threeBlockConcreteComparisonConstant_le_card_mul_log_base
    (Fin W) (packetRowScale W * z)
  have hcp := Real.log_le_log
    (lt_of_lt_of_le zero_lt_one (terminalComparisonPolynomialBase_one_le _ _))
    ((comparisonPolynomialBase_le Ξ) W hW _ hshift)
  rw [Real.log_pow] at hcp
  have hM : 0 ≤ terminalConcreteExposureThreshold ((packetFamily Ξ) W) W :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (packetCoordinateMaxThreshold_one_le _ _)
  have hr := terminalReverseLoss_le_card_mul_log_polynomialBase
    (Fin W) (packetRowScale W * z)
    (terminalConcreteExposureThreshold ((packetFamily Ξ) W) W) (by positivity)
  have hrp := Real.log_le_log
    (lt_of_lt_of_le zero_lt_one (terminalReversePolynomialBase_one_le _ _ _))
    ((reversePolynomialBase_le Ξ) W hW hparameter _ hshift)
  rw [Real.log_pow] at hrp
  have hv := (terminalUniformValueLoss_le Ξ) cook W hW
  simp only [BernoulliSection10.card_threeBlockIndex, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_ofNat] at hc hr
  have hcl : Real.log (threeBlockConcreteComparisonConstant (W := Fin W) (packetRowScale W * z)) ≤
      12 * W * Real.log (W : ℝ) := by
    calc
      _ ≤ 3 * (W : ℝ) * Real.log (terminalComparisonPolynomialBase (Fin W) (packetRowScale W * z)) := hc
      _ ≤ 3 * (W : ℝ) * (4 * Real.log (W : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hw0)
        simpa only [Nat.cast_ofNat] using hcp
      _ = _ := by ring
  have hrl : terminalReverseLoss (Fin W) (packetRowScale W * z)
      (terminalConcreteExposureThreshold ((packetFamily Ξ) W) W) ≤
      18 * W * Real.log (W : ℝ) := by
    calc
      _ ≤ 3 * (W : ℝ) * Real.log (terminalReversePolynomialBase (Fin W)
          (packetRowScale W * z) (terminalConcreteExposureThreshold ((packetFamily Ξ) W) W)) := hr
      _ ≤ 3 * (W : ℝ) * (6 * Real.log (W : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hw0)
        simpa only [Nat.cast_ofNat] using hrp
      _ = _ := by ring
  have hl0 : 0 ≤ Real.log (W : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ W by omega))
  have hcombined : (subgaussianBoundaryBaseLoss Ξ) cook W z ≤
      (subgaussianTerminalLossConstant Ξ) cook * (W : ℝ) * Real.log W := by
    unfold subgaussianBoundaryBaseLoss terminalUniformBaseLoss subgaussianTerminalLossConstant
    nlinarith [mul_nonneg hw0 hl0]
  have hl : Real.log (W : ℝ) ≤ densityLogScale W := by
    rw [densityLogScale_eq hW0]
    linarith
  exact hcombined.trans (mul_le_mul_of_nonneg_left hl
    (mul_nonneg ((subgaussianTerminalLossConstant_pos Ξ) cook).le hw0))

theorem subgaussianBoundaryBaseLoss_le_of_threshold (Ξ : Atom)
    (cook : CookInput Ξ) (W : ℕ) (z : ℂ)
    (hW : (subgaussianBoundaryWidthThreshold Ξ) cook z ≤ W) :
    (subgaussianBoundaryBaseLoss Ξ) cook W z ≤
      (subgaussianTerminalLossConstant Ξ) cook * (W : ℝ) * densityLogScale W := by
  have hlarge : 160 ≤ terminalCanonicalLargeWThreshold cook 1
      (cook.subgaussianBound : ℝ) :=
    (by norm_num [terminalCanonicalPivotConstant] : 160 ≤ 2 * terminalCanonicalPivotConstant).trans
      (le_max_left _ _)
  have h160 : 160 ≤ W := hlarge.trans ((le_max_left _ _).trans hW)
  have hz : 3 * ‖z‖ ^ 2 ≤ (W : ℝ) :=
    (Nat.le_ceil _).trans (by
      exact_mod_cast ((le_max_right _ _).trans ((le_max_right _ _).trans hW) :
        Nat.ceil (3 * ‖z‖ ^ 2) ≤ W))
  have hceil : Nat.ceil (cook.subgaussianBound : ℝ) ≤ W := by
    exact (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans
        ((le_max_left _ _).trans hW)))
  have hparameter : (Ξ.parameter : ℝ) ≤ W :=
    (show (Ξ.parameter : ℝ) ≤ (cook.subgaussianBound : ℝ) by
      exact_mod_cast cook.parameter_le).trans
        ((Nat.le_ceil _).trans (by exact_mod_cast hceil))
  exact (subgaussianBoundaryBaseLoss_le Ξ) cook W z h160 hparameter hz

theorem subgaussianBoundaryBaseLoss_eventually_le (Ξ : Atom)
    (cook : CookInput Ξ) (z : ℂ) :
    ∀ᶠ W : ℕ in atTop, (subgaussianBoundaryBaseLoss Ξ) cook W z ≤
      (subgaussianTerminalLossConstant Ξ) cook * (W : ℝ) * densityLogScale W := by
  filter_upwards [eventually_ge_atTop ((subgaussianBoundaryWidthThreshold Ξ) cook z)] with W hW
  exact (subgaussianBoundaryBaseLoss_le_of_threshold Ξ) cook W z hW

end SubgaussianSection8
