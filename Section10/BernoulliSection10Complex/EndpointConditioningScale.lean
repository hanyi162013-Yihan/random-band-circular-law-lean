import BernoulliSection10Complex.EndpointConditioningGrowth

open scoped BigOperators Matrix ENNReal NNReal
open MeasureTheory

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open BernoulliLinearAlgebra

local instance endpointConditioningScaleSumLinearOrder (W : ℕ) :
    LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W ↦ (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h ↦ toLex.injective h)

theorem endpointOneBlockRowCost_eq_W_log_eW
    (L : ℝ) (W : ℕ) (hW : 0 < W) :
    multiAffineLogCost L (List.replicate W W) =
      ENNReal.ofReal (Real.sqrt (lemma10_2Constant L)) *
        oneSiteWLogScale W := by
  have hW0 : (0 : ℝ) ≤ W := by positivity
  have hlog0 : 0 ≤ Real.log (Real.exp 1 * W) := by
    rw [← one_add_posLog_nat_eq_log_e_mul W hW]
    exact add_nonneg (by norm_num) Real.posLog_nonneg
  rw [multiAffineLogCost_replicate]
  unfold oneSiteWLogScale
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_mul hW0]
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  congr 1
  ring

theorem endpointTwoBlockRowCost_eq_W_log_eW
    (L : ℝ) (W : ℕ) (hW : 0 < W) :
    multiAffineLogCost L (List.replicate (W + W) W) =
      2 * ENNReal.ofReal (Real.sqrt (lemma10_2Constant L)) *
        oneSiteWLogScale W := by
  calc
    multiAffineLogCost L (List.replicate (W + W) W) =
        ((W + W : ℕ) : ℝ≥0∞) * ENNReal.ofReal
          (Real.sqrt (lemma10_2Constant L) *
            Real.log (Real.exp 1 * (W : ℝ))) :=
      multiAffineLogCost_replicate L (W + W) W
    _ = 2 * ((W : ℝ≥0∞) * ENNReal.ofReal
          (Real.sqrt (lemma10_2Constant L) *
            Real.log (Real.exp 1 * (W : ℝ)))) := by
      push_cast
      ring
    _ = 2 * multiAffineLogCost L (List.replicate W W) := by
      rw [multiAffineLogCost_replicate]
    _ = 2 * ENNReal.ofReal (Real.sqrt (lemma10_2Constant L)) *
        oneSiteWLogScale W := by
      rw [endpointOneBlockRowCost_eq_W_log_eW L W hW]
      ring

def endpointCountLogConstant : ℝ := 1 + Real.posLog 7

theorem endpointCountLogConstant_nonneg : 0 ≤ endpointCountLogConstant := by
  unfold endpointCountLogConstant
  exact add_nonneg (by norm_num) Real.posLog_nonneg

theorem posLog_endpointCount_le_W_log_eW
    (W : ℕ) (hW : 0 < W) :
    Real.posLog (4 * W + 3 : ℝ) ≤
      endpointCountLogConstant * W * Real.log (Real.exp 1 * W) := by
  have hW1Nat : 1 ≤ W := by omega
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1Nat
  have hW0 : (0 : ℝ) ≤ W := by positivity
  let t := Real.posLog (W : ℝ)
  have ht : 0 ≤ t := Real.posLog_nonneg
  have hcount : (4 * W + 3 : ℝ) ≤ 7 * W := by
    push_cast
    nlinarith
  have hlog : Real.posLog (4 * W + 3 : ℝ) ≤ Real.posLog 7 + t := by
    calc
      Real.posLog (4 * W + 3 : ℝ) ≤ Real.posLog (7 * W : ℝ) :=
        Real.posLog_le_posLog (by positivity) hcount
      _ ≤ Real.posLog 7 + t := by
        simpa only [t] using Real.posLog_mul (x := (7 : ℝ)) (y := (W : ℝ))
  calc
    Real.posLog (4 * W + 3 : ℝ) ≤ Real.posLog 7 + t := hlog
    _ ≤ endpointCountLogConstant * W * (1 + t) := by
      unfold endpointCountLogConstant
      have hc : 0 ≤ Real.posLog (7 : ℝ) := Real.posLog_nonneg
      have hinner : Real.posLog 7 + t ≤
          (1 + Real.posLog 7) * (1 + t) := by
        nlinarith [mul_nonneg hc ht]
      calc
        Real.posLog 7 + t ≤ (1 + Real.posLog 7) * (1 + t) := hinner
        _ = 1 * ((1 + Real.posLog 7) * (1 + t)) := by ring
        _ ≤ W * ((1 + Real.posLog 7) * (1 + t)) := by
          exact mul_le_mul_of_nonneg_right hW1
            (mul_nonneg (add_nonneg (by norm_num) hc)
              (add_nonneg (by norm_num) ht))
        _ = (1 + Real.posLog 7) * W * (1 + t) := by ring
    _ = endpointCountLogConstant * W * Real.log (Real.exp 1 * W) := by
      rw [← one_add_posLog_nat_eq_log_e_mul W hW]

theorem posLog_endpointDetTensorGrowth_le_W_log_eW
    (W : ℕ) (hW : 0 < W) :
    Real.posLog ((2 : ℝ) ^ W * |blockNormalization W|⁻¹ ^ W) ≤
      oneSiteDetLogConstant * W * Real.log (Real.exp 1 * W) := by
  let a : ℝ := |(blockNormalization W)⁻¹|
  have ha0 : 0 ≤ a := abs_nonneg _
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (show 1 ≤ W by omega)
  have hbase : 2 * a ≤ 1 + (3 * W : ℝ) * a := by
    have ha : 2 * a ≤ 3 * W * a := by
      exact mul_le_mul_of_nonneg_right (by nlinarith) ha0
    linarith
  have hpow : (2 * a) ^ W ≤
      (1 + (3 * W : ℝ) * a) ^ W :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) ha0) hbase W
  calc
    Real.posLog ((2 : ℝ) ^ W * |blockNormalization W|⁻¹ ^ W) =
        Real.posLog ((2 * a) ^ W) := by
      congr 1
      rw [mul_pow]
      simp only [a, abs_inv]
    _ ≤ Real.posLog ((1 + (3 * W : ℝ) * a) ^ W) :=
      Real.posLog_le_posLog (pow_nonneg (mul_nonneg (by norm_num) ha0) W) hpow
    _ = Real.posLog (oneSiteDetTensorGrowth W) := by
      rfl
    _ ≤ oneSiteDetLogConstant * W * Real.log (Real.exp 1 * W) :=
      posLog_oneSiteDetTensorGrowth_le_W_log_eW W hW

def endpointForwardWLogConstant (L : ℝ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal (Real.sqrt (lemma10_2Constant L)) +
    ENNReal.ofReal endpointTensorLogConstant

theorem endpointForwardWLogIntegralBound_le_W_log_eW
    (L : ℝ) (W : ℕ) (hW : 0 < W) :
    endpointForwardWLogIntegralBound L W ≤
      endpointForwardWLogConstant L * oneSiteWLogScale W := by
  have htensor : ENNReal.ofReal
      (endpointTensorLogConstant * W * Real.log (Real.exp 1 * W)) =
      ENNReal.ofReal endpointTensorLogConstant * oneSiteWLogScale W := by
    rw [show endpointTensorLogConstant * (W : ℝ) *
        Real.log (Real.exp 1 * W) = endpointTensorLogConstant *
          ((W : ℝ) * Real.log (Real.exp 1 * W)) by ring,
      ENNReal.ofReal_mul endpointTensorLogConstant_nonneg]
    rfl
  unfold endpointForwardWLogIntegralBound endpointForwardWLogConstant
  rw [endpointTwoBlockRowCost_eq_W_log_eW L W hW, htensor]
  rw [add_mul]

def endpointExteriorWLogConstant (L : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal endpointCountLogConstant +
    4 * ENNReal.ofReal (Real.sqrt (lemma10_2Constant L)) +
    ENNReal.ofReal endpointTensorLogConstant +
    2 * ENNReal.ofReal oneSiteDetLogConstant

theorem endpointExteriorLogIntegralBound_le_W_log_eW
    (L : ℝ) (W : ℕ) (hW : 0 < W) :
    endpointExteriorLogIntegralBound L W ≤
      endpointExteriorWLogConstant L * oneSiteWLogScale W := by
  have hcount : ENNReal.ofReal (Real.posLog (4 * W + 3 : ℝ)) ≤
      ENNReal.ofReal endpointCountLogConstant * oneSiteWLogScale W := by
    have h := ENNReal.ofReal_le_ofReal
      (posLog_endpointCount_le_W_log_eW W hW)
    rw [show endpointCountLogConstant * (W : ℝ) *
        Real.log (Real.exp 1 * W) = endpointCountLogConstant *
          ((W : ℝ) * Real.log (Real.exp 1 * W)) by ring,
      ENNReal.ofReal_mul endpointCountLogConstant_nonneg] at h
    exact h
  have hforward := endpointForwardWLogIntegralBound_le_W_log_eW L W hW
  have hrow : multiAffineLogCost L (List.replicate W W) =
      ENNReal.ofReal (Real.sqrt (lemma10_2Constant L)) *
        oneSiteWLogScale W :=
    endpointOneBlockRowCost_eq_W_log_eW L W hW
  have hdet : ENNReal.ofReal
      (Real.posLog ((2 : ℝ) ^ W * |blockNormalization W|⁻¹ ^ W)) ≤
      ENNReal.ofReal oneSiteDetLogConstant * oneSiteWLogScale W := by
    have h := ENNReal.ofReal_le_ofReal
      (posLog_endpointDetTensorGrowth_le_W_log_eW W hW)
    rw [show oneSiteDetLogConstant * (W : ℝ) *
        Real.log (Real.exp 1 * W) = oneSiteDetLogConstant *
          ((W : ℝ) * Real.log (Real.exp 1 * W)) by ring,
      ENNReal.ofReal_mul oneSiteDetLogConstant_nonneg] at h
    exact h
  unfold endpointExteriorLogIntegralBound endpointExteriorWLogConstant
  calc
    ENNReal.ofReal (Real.posLog (4 * W + 3 : ℝ)) +
        endpointForwardWLogIntegralBound L W +
        2 * (multiAffineLogCost L (List.replicate W W) +
          ENNReal.ofReal
            (Real.posLog ((2 : ℝ) ^ W * |blockNormalization W|⁻¹ ^ W))) ≤
      ENNReal.ofReal endpointCountLogConstant * oneSiteWLogScale W +
        endpointForwardWLogConstant L * oneSiteWLogScale W +
        2 * (ENNReal.ofReal (Real.sqrt (lemma10_2Constant L)) *
          oneSiteWLogScale W +
          ENNReal.ofReal oneSiteDetLogConstant * oneSiteWLogScale W) := by
      exact add_le_add (add_le_add hcount hforward)
        (mul_le_mul' le_rfl (add_le_add hrow.le hdet))
    _ = (ENNReal.ofReal endpointCountLogConstant +
          4 * ENNReal.ofReal (Real.sqrt (lemma10_2Constant L)) +
          ENNReal.ofReal endpointTensorLogConstant +
          2 * ENNReal.ofReal oneSiteDetLogConstant) *
        oneSiteWLogScale W := by
      unfold endpointForwardWLogConstant
      ring

theorem endpointExteriorConstant_log_lintegral_le_W_log_eW
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) :
    (∫⁻ x, ENNReal.ofReal
        (Real.log (exactExteriorConditioningConstant
          (normalizedEndpointFactor W x)))
        ∂endpointBlockPairLaw W μ) ≤
      endpointExteriorWLogConstant L * oneSiteWLogScale W :=
  (endpointExteriorConstant_log_lintegral_le hμ W hW).trans
    (endpointExteriorLogIntegralBound_le_W_log_eW L W hW)

end BernoulliSection10Complex
