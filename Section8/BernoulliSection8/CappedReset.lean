import BernoulliSection8.CappedProbability
import BernoulliSection10.FinitePressure

/-!
# Clipped reset losses and the deterministic pressure sandwich

The reset loss uses the norm of the actual product. A zero product is
charged the entire cap. The scalar-test estimate compares this loss with
the Section 9 coefficient-relative capped loss. In particular, no union
bound over the slow Cook failure is used.

The final lemma is the finite deterministic implication of (8.46)--(8.47).
It uses only the one optimizing degree for its lower bound. Probabilistic
and physical hypotheses are discharged in separate modules.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10

def cappedSpliceLoss (T a b d : ℝ) : ℝ :=
  if d = 0 then T else min T (max 0 (Real.log a + Real.log b - Real.log d))

@[simp] theorem cappedSpliceLoss_zero (T a b : ℝ) : cappedSpliceLoss T a b 0 = T := by
  simp [cappedSpliceLoss]

theorem cappedSpliceLoss_nonneg {T : ℝ} (hT : 0 ≤ T) (a b d : ℝ) :
    0 ≤ cappedSpliceLoss T a b d := by
  unfold cappedSpliceLoss
  split_ifs
  · exact hT
  · exact le_min hT (le_max_left _ _)

theorem cappedSpliceLoss_le_cap (T a b d : ℝ) : cappedSpliceLoss T a b d ≤ T := by
  unfold cappedSpliceLoss
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem measurable_cappedSpliceLoss {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ) {a b d : Ω → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hd : Measurable d) : Measurable (fun ω => cappedSpliceLoss T (a ω) (b ω) (d ω)) := by
  unfold cappedSpliceLoss
  exact Measurable.ite (hd (measurableSet_singleton 0)) measurable_const
    (measurable_const.min (measurable_const.max
      (((Real.measurable_log.comp ha).add (Real.measurable_log.comp hb)).sub
        (Real.measurable_log.comp hd))))

theorem integrable_cappedSpliceLoss {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {T : ℝ} (hT : 0 ≤ T)
    {a b d : Ω → ℝ} (ha : Measurable a) (hb : Measurable b) (hd : Measurable d) :
    Integrable (fun ω => cappedSpliceLoss T (a ω) (b ω) (d ω)) μ := by
  apply (integrable_const T).mono'
    (measurable_cappedSpliceLoss T ha hb hd).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_of_nonneg (cappedSpliceLoss_nonneg hT _ _ _)]
    exact cappedSpliceLoss_le_cap _ _ _ _

/-- Unclipping requires only a bound for the true increment, which can be
obtained from the core and reset inverse norms independently of past length. -/
theorem log_product_ge_sub_cappedSpliceLoss {T a b d : ℝ} (hd : d ≠ 0)
    (hdefect : Real.log a + Real.log b - Real.log d ≤ T) :
    Real.log a + Real.log b - cappedSpliceLoss T a b d ≤ Real.log d := by
  have h : Real.log a + Real.log b - Real.log d ≤
      cappedSpliceLoss T a b d := by
    rw [cappedSpliceLoss, if_neg hd]
    exact le_min hdefect (le_max_right _ _)
  linarith

theorem min_max_le_add_min {T D e y : ℝ} (hD : 0 ≤ D) (hy : 0 ≤ y)
    (he : e ≤ D + y) : min T (max 0 e) ≤ D + min T y := by
  by_cases hTy : T ≤ y
  · rw [min_eq_left hTy]
    exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hTy))]
    exact (min_le_right _ _).trans (max_le (by linarith) he)

/-- The singular scalar test causes no exception: its coefficient loss is
exactly the cap when the test value vanishes. -/
theorem cappedSpliceLoss_le_coefficient_loss {T a b d c D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hD : 0 ≤ D)
    (hcLower : -Real.log c ≤ D) (w : ℂ)
    (htest : a * b * ‖w‖ ≤ d) :
    cappedSpliceLoss T a b d ≤ D + cappedLogLoss T c w := by
  by_cases hw : w = 0
  · rw [hw, cappedLogLoss_zero]
    exact (cappedSpliceLoss_le_cap _ _ _ _).trans (by linarith)
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have habw : 0 < a * b * ‖w‖ := mul_pos (mul_pos ha hb) hn
    have hd : 0 < d := habw.trans_le htest
    have hlog := Real.log_le_log habw htest
    rw [Real.log_mul (mul_ne_zero ha.ne' hb.ne') hn.ne',
      Real.log_mul ha.ne' hb.ne'] at hlog
    have hratio : Real.log (c / ‖w‖) = Real.log c - Real.log ‖w‖ :=
      Real.log_div hc.ne' hn.ne'
    have hpos : Real.log (c / ‖w‖) ≤ Real.posLog (c / ‖w‖) := le_max_right _ _
    have hdefect : Real.log a + Real.log b - Real.log d ≤
        D + Real.posLog (c / ‖w‖) := by rw [hratio] at hpos; linarith
    rw [cappedSpliceLoss, if_neg hd.ne', cappedLogLoss_of_ne_zero hw]
    exact min_max_le_add_min hD Real.posLog_nonneg hdefect

/-- Integrating a fixed-fiber scalar test only adds the coefficient-norm
loss to the capped Section 9 bound. -/
theorem integral_cappedSpliceLoss_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T a b c D A p : ℝ} (hT : 0 ≤ T) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hD : 0 ≤ D) (hcLower : -Real.log c ≤ D)
    {d : Ω → ℝ} {w : Ω → ℂ} (hd : Measurable d) (hw : Measurable w)
    (htest : ∀ ω, a * b * ‖w ω‖ ≤ d ω)
    (hcap : (∫ ω, cappedLogLoss T c (w ω) ∂μ) ≤ A + p * T) :
    (∫ ω, cappedSpliceLoss T a b (d ω) ∂μ) ≤ D + A + p * T := by
  have hleft := integrable_cappedSpliceLoss μ hT
    (measurable_const (a := a)) (measurable_const (a := b)) hd
  have hright := (integrable_const D).add (integrable_cappedLoss μ hT c hw)
  have h := integral_mono hleft hright (fun ω =>
    cappedSpliceLoss_le_coefficient_loss ha hb hc hD hcLower (w ω) (htest ω))
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const D) (integrable_cappedLoss μ hT c hw)] at h
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at h
  linarith

/-- The pressure sandwich uses the deterministic maximizing degree only
on the lower side and all degrees on the upper side. -/
theorem finite_pressure_sandwich {d : ℕ}
    (pressure core product : Fin (d + 1) → ℝ) {K noise loss resetCost : ℝ}
    (hK : 0 ≤ K)
    (hcore : ∀ r, |core r - K * pressure r| ≤ noise)
    (hlower : core (pressureOptimizingDegree pressure) - loss ≤
      product (pressureOptimizingDegree pressure))
    (hupper : ∀ r, product r ≤ core r + resetCost) :
    K * finitePressureMax pressure - noise - loss ≤ finitePressureMax product ∧
      finitePressureMax product ≤ K * finitePressureMax pressure + noise + resetCost := by
  constructor
  · have hn := (abs_le.mp (hcore (pressureOptimizingDegree pressure))).1
    rw [pressureOptimizingDegree_maximizes pressure] at hn
    have hp := le_finitePressureMax product (pressureOptimizingDegree pressure)
    linarith
  · apply finitePressureMax_le
    intro r
    have hn := (abs_le.mp (hcore r)).2
    have hp := mul_le_mul_of_nonneg_left (le_finitePressureMax pressure r) hK
    have hu := hupper r
    linarith

end BernoulliSection8
