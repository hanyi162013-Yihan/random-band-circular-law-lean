import CircularLawSection6.NegativeMomentCutoff

/-! # A deterministic logarithmic regularization error

Hard lower cutoffs control the small singular values. The extra smooth
regularization error is at most t²/(2a²), so tight negative moments suffice
for removal in probability, without a uniform expected negative moment.
-/

open MeasureTheory Filter Topology
open CircularLawSections56.Section5
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem regularized_log_ge_log {s t : ℝ} (hs : 0 < s) :
    Real.log s ≤ (1 / 2 : ℝ) * Real.log (s ^ 2 + t ^ 2) := by
  have h := Real.log_le_log (sq_pos_of_pos hs)
    (le_add_of_nonneg_right (sq_nonneg t) : s ^ 2 ≤ s ^ 2 + t ^ 2)
  rw [Real.log_pow] at h
  norm_num at h
  linarith

theorem regularized_log_le_cutoff {s a t : ℝ}
    (hs : 0 ≤ s) (ha : 0 < a) (ht : 0 < t) :
    (1 / 2 : ℝ) * Real.log (s ^ 2 + t ^ 2) ≤
      Real.log (max s a) + t ^ 2 / (2 * a ^ 2) := by
  let u := max s a
  have hu : 0 < u := ha.trans_le (le_max_right _ _)
  have hsu : s ^ 2 ≤ u ^ 2 :=
    (sq_le_sq₀ hs hu.le).2 (le_max_left _ _)
  have hau : a ^ 2 ≤ u ^ 2 :=
    (sq_le_sq₀ ha.le hu.le).2 (le_max_right _ _)
  have hpos : 0 < s ^ 2 + t ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos ht)
  have hlog := Real.log_le_log hpos (add_le_add hsu (le_refl (t ^ 2)))
  have hratio : 0 < (u ^ 2 + t ^ 2) / u ^ 2 := by positivity
  have hratioLog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div (by positivity) (sq_pos_of_pos hu).ne', Real.log_pow] at hratioLog
  have hratioId : (u ^ 2 + t ^ 2) / u ^ 2 - 1 = t ^ 2 / u ^ 2 := by
    field_simp [hu.ne']
    ring
  rw [hratioId] at hratioLog
  have hdiv : t ^ 2 / u ^ 2 ≤ t ^ 2 / a ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg t) (sq_pos_of_pos ha) hau
  have hid : t ^ 2 / (2 * a ^ 2) = (1 / 2 : ℝ) * (t ^ 2 / a ^ 2) := by ring
  rw [hid]
  change (1 / 2 : ℝ) * Real.log (s ^ 2 + t ^ 2) ≤
    Real.log u + (1 / 2 : ℝ) * (t ^ 2 / a ^ 2)
  norm_num at hratioLog
  linarith

end CircularLawSection6
