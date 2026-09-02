import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Section 8 clipping, including a zero determinant

`Real.log 0 = 0` is not the logarithmic convention in (8.30). We instead
clamp the nonnegative argument away from zero before taking its logarithm.
For a nonnegative cap this gives exactly `clip [-B,B] (log x)` at positive
`x`, and gives `-B` at `x = 0`. No invertibility or density assumption is
used. The definition is continuous, so it also supplies measurability of
the clipped pressure from continuity of a concrete matrix norm.
-/

open scoped Topology

noncomputable section

namespace BernoulliSection8

def clippedLog (B x : ℝ) : ℝ :=
  min B (Real.log (max (Real.exp (-B)) x))

theorem clippedLog_le (B x : ℝ) : clippedLog B x ≤ B :=
  min_le_left _ _

theorem neg_le_clippedLog {B : ℝ} (hB : 0 ≤ B) (x : ℝ) :
    -B ≤ clippedLog B x := by
  apply le_min (by linarith)
  exact (Real.le_log_iff_exp_le
    ((Real.exp_pos (-B)).trans_le (le_max_left _ _))).2 (le_max_left _ _)

theorem abs_clippedLog_le {B : ℝ} (hB : 0 ≤ B) (x : ℝ) :
    |clippedLog B x| ≤ B :=
  abs_le.mpr ⟨neg_le_clippedLog hB x, clippedLog_le B x⟩

@[simp] theorem clippedLog_zero {B : ℝ} (hB : 0 ≤ B) :
    clippedLog B 0 = -B := by
  simp only [clippedLog, max_eq_left (Real.exp_pos _).le, Real.log_exp]
  exact min_eq_right (by linarith)

theorem clippedLog_of_pos (B : ℝ) {x : ℝ} (hx : 0 < x) :
    clippedLog B x = min B (max (-B) (Real.log x)) := by
  by_cases h : Real.exp (-B) ≤ x
  · have hlog : -B ≤ Real.log x := (Real.le_log_iff_exp_le hx).2 h
    simp [clippedLog, max_eq_right h, max_eq_right hlog]
  · have hxexp : x ≤ Real.exp (-B) := le_of_lt (lt_of_not_ge h)
    have hlog : Real.log x ≤ -B := (Real.log_le_iff_le_exp hx).2 hxexp
    simp [clippedLog, max_eq_left hxexp, max_eq_left hlog]

theorem clippedLog_eq_log {B x : ℝ}
    (hlo : Real.exp (-B) ≤ x) (hhi : x ≤ Real.exp B) :
    clippedLog B x = Real.log x := by
  have hx : 0 < x := (Real.exp_pos _).trans_le hlo
  exact by
    rw [clippedLog, max_eq_right hlo, min_eq_right]
    exact (Real.log_le_iff_le_exp hx).2 hhi

theorem clippedLog_eq_log_of_log_bounds {B x : ℝ} (hx : 0 < x)
    (hlo : -B ≤ Real.log x) (hhi : Real.log x ≤ B) :
    clippedLog B x = Real.log x := by
  rw [clippedLog_of_pos B hx, max_eq_right hlo, min_eq_right hhi]

theorem continuous_clippedLog (B : ℝ) : Continuous (clippedLog B) := by
  apply continuous_const.min
  apply (continuous_const.max continuous_id).log
  intro x
  exact ne_of_gt ((Real.exp_pos (-B)).trans_le (le_max_left _ x))

end BernoulliSection8
