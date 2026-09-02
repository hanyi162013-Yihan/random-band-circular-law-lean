import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-! # Elementary positive-log estimates -/

noncomputable section

namespace BernoulliSection10

/-- The logarithmic triangle inequality used for forward growth losses. -/
theorem posLog_le_abs_log_sub_log_add_posLog (a b : ℝ) :
    Real.posLog a ≤ |Real.log a - Real.log b| + Real.posLog b := by
  rw [Real.posLog_apply, Real.posLog_apply]
  apply max_le
  · exact add_nonneg (abs_nonneg _) (le_max_left _ _)
  · have hdiff : Real.log a - Real.log b ≤
        |Real.log a - Real.log b| := le_abs_self _
    have hb : Real.log b ≤ max 0 (Real.log b) := le_max_right _ _
    linarith

/-- The logarithmic triangle inequality used for inverse small-ball losses. -/
theorem posLog_inv_le_abs_log_sub_log_add_posLog_inv (a b : ℝ) :
    Real.posLog a⁻¹ ≤ |Real.log a - Real.log b| + Real.posLog b⁻¹ := by
  rw [Real.posLog_apply, Real.posLog_apply, Real.log_inv, Real.log_inv]
  apply max_le
  · exact add_nonneg (abs_nonneg _) (le_max_left _ _)
  · have hdiff : -(Real.log a - Real.log b) ≤
        |Real.log a - Real.log b| := neg_le_abs _
    have hb : -Real.log b ≤ max 0 (-Real.log b) := le_max_right _ _
    linarith

end BernoulliSection10
