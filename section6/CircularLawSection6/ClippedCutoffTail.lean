import ShortRingAnchor.LogDecomposition
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Removing the upper cutoff using only the second moment

The bounded test is the existing clipped logarithm of squared singular
values. Its difference from the one-sided logarithmic cutoff is exactly
the existing upper correction. The resulting expectation error is at
most the second moment divided by the upper cutoff. Zero singular values
are included throughout; no least-singular-value estimate is needed.
-/

open MeasureTheory Filter Topology Set ShortRingAnchor
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem continuous_clippedLog {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    Continuous (clippedLog a R) := by
  have hcont : Continuous (realClamp (a ^ 2) (R ^ 2)) :=
    continuous_const.min (continuous_const.max continuous_id)
  apply Continuous.const_mul
  apply hcont.log
  intro x
  exact (lt_of_lt_of_le (sq_pos_of_pos ha)
    (realClamp_lower (x := x) (by nlinarith))).ne'

theorem clippedLog_abs_le {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) (x : ℝ) :
    |clippedLog a R x| ≤ max |Real.log a| |Real.log R| := by
  have hlo := realClamp_lower (x := x) (by nlinarith : a ^ 2 ≤ R ^ 2)
  have hhi := realClamp_upper (lo := a ^ 2) (hi := R ^ 2) (x := x)
  have hp := lt_of_lt_of_le (sq_pos_of_pos ha) hlo
  have hl := Real.log_le_log (sq_pos_of_pos ha) hlo
  have hu := Real.log_le_log hp hhi
  rw [Real.log_pow] at hl hu
  norm_num only [Nat.cast_ofNat] at hl hu
  have hla := le_max_left |Real.log a| |Real.log R|
  have hRa := le_max_right |Real.log a| |Real.log R|
  have h1 := neg_abs_le (Real.log a)
  have h2 := le_abs_self (Real.log R)
  unfold clippedLog
  apply abs_le.2
  constructor <;> linarith

theorem cutoffLog_eq_clippedLog_add_upper {a R s : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hs : 0 ≤ s) :
    Real.log (max s a) = clippedLog a R (s ^ 2) + upperLogCorrection R s := by
  by_cases hsa : s < a
  · have hs2 : s ^ 2 ≤ a ^ 2 := by nlinarith
    have ha2R : a ^ 2 ≤ R ^ 2 := by nlinarith
    have hRs : ¬ R < s := not_lt_of_ge (hsa.le.trans haR)
    simp [clippedLog, realClamp, upperLogCorrection, hRs,
      max_eq_right hsa.le, max_eq_left hs2, min_eq_right ha2R, Real.log_pow]
  · have has : a ≤ s := le_of_not_gt hsa
    have h := log_eq_clippedLog_sub_lower_add_upper ha haR (ha.trans_le has)
    simpa only [max_eq_left has, lowerLogCorrection, if_neg hsa, sub_zero] using h

theorem cutoffLog_clipped_error_nonneg {a R s : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hs : 0 ≤ s) :
    0 ≤ Real.log (max s a) - clippedLog a R (s ^ 2) := by
  rw [cutoffLog_eq_clippedLog_add_upper ha haR hs, add_sub_cancel_left]
  by_cases h : R < s
  · rw [upperLogCorrection, if_pos h]
    exact sub_nonneg.mpr (Real.log_le_log (ha.trans_le haR) h.le)
  · simp [upperLogCorrection, h]

theorem cutoffLog_clipped_error_le_sq_div {a R s : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hR : 1 ≤ R) (hs : 0 ≤ s) :
    Real.log (max s a) - clippedLog a R (s ^ 2) ≤ s ^ 2 / R := by
  rw [cutoffLog_eq_clippedLog_add_upper ha haR hs, add_sub_cancel_left]
  rcases hs.eq_or_lt with h | h
  · subst s
    simp [upperLogCorrection, not_lt.mpr (zero_le_one.trans hR)]
  · exact upperLogCorrection_le_sq_div hR h

theorem cutoffLog_clipped_abs_error_le_sq_div {a R s : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hR : 1 ≤ R) (hs : 0 ≤ s) :
    |Real.log (max s a) - clippedLog a R (s ^ 2)| ≤ s ^ 2 / R := by
  rw [abs_of_nonneg (cutoffLog_clipped_error_nonneg ha haR hs)]
  exact cutoffLog_clipped_error_le_sq_div ha haR hR hs

theorem integrable_clippedLog_comp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Ω → ℝ) (hs : Measurable s)
    {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    Integrable (fun ω => clippedLog a R (s ω ^ 2)) μ := by
  apply (integrable_const (max |Real.log a| |Real.log R|)).mono'
  · exact ((continuous_clippedLog ha haR).measurable.comp (hs.pow_const 2)).aestronglyMeasurable
  · exact ae_of_all μ fun ω => by
      simpa only [Real.norm_eq_abs] using clippedLog_abs_le ha haR (s ω ^ 2)

theorem expected_cutoffLog_clipped_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Ω → ℝ) (hs : Measurable s)
    (hspos : ∀ᵐ ω ∂μ, 0 ≤ s ω) (hsecond : Integrable (fun ω => s ω ^ 2) μ)
    {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) (hR : 1 ≤ R) :
    Integrable (fun ω => Real.log (max (s ω) a)) μ ∧
      |(∫ ω, Real.log (max (s ω) a) ∂μ) -
        ∫ ω, clippedLog a R (s ω ^ 2) ∂μ| ≤ (∫ ω, s ω ^ 2 ∂μ) / R := by
  have hclip := integrable_clippedLog_comp μ s hs ha haR
  have hlog : Measurable (fun ω => Real.log (max (s ω) a)) :=
    Real.measurable_log.comp (hs.max measurable_const)
  have hm := hlog.sub ((continuous_clippedLog ha haR).measurable.comp (hs.pow_const 2))
  have herr : Integrable (fun ω => Real.log (max (s ω) a) - clippedLog a R (s ω ^ 2)) μ := by
    apply (hsecond.div_const R).mono' hm.aestronglyMeasurable
    filter_upwards [hspos] with ω hω
    simpa only [Real.norm_eq_abs, Pi.sub_apply, Function.comp_apply] using
      cutoffLog_clipped_abs_error_le_sq_div ha haR hR hω
  have hint : Integrable (fun ω => Real.log (max (s ω) a)) μ := by
    apply (herr.add hclip).congr
    filter_upwards with ω
    exact sub_add_cancel _ _
  refine ⟨hint, ?_⟩
  rw [← integral_sub hint hclip]
  calc
    _ ≤ ∫ ω, |Real.log (max (s ω) a) - clippedLog a R (s ω ^ 2)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω, s ω ^ 2 / R ∂μ := by
      apply integral_mono_ae herr.abs (hsecond.div_const R)
      filter_upwards [hspos] with ω hω
      exact cutoffLog_clipped_abs_error_le_sq_div ha haR hR hω
    _ = _ := integral_div R _

end CircularLawSection6
