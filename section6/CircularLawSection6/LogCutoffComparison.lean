import CircularLawSection6.SingularSpectralCoupling
import CircularLawSections56.Section6.Potentials
import Mathlib.Algebra.Order.Group.MinMax

/-! # The actual logarithmic cutoff is Lipschitz

This specializes the proved singular-value comparison to the precise cutoff
used in Section 6, with its explicit `1/a` constant and dimension
normalization. There is no cutoff-comparison hypothesis.
-/

open scoped BigOperators
open TaoVuReplacement

noncomputable section

namespace CircularLawSection6

theorem abs_log_sub_log_le_div {a x y : ℝ} (ha : 0 < a) (hx : a ≤ x) (hy : a ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / a := by
  have ordered {x y : ℝ} (hay : a ≤ y) (hyx : y ≤ x) :
      Real.log x - Real.log y ≤ (x - y) / a := by
    have hypos := ha.trans_le hay
    have hxpos := hypos.trans_le hyx
    have h := Real.log_le_sub_one_of_pos (div_pos hxpos hypos)
    rw [Real.log_div hxpos.ne' hypos.ne'] at h
    calc
      _ ≤ (x - y) / y := by
        convert h using 1 <;> field_simp <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) ha hay
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (ha.trans_le hy) h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact ordered hy h
  · rw [abs_sub_comm (Real.log x), abs_sub_comm x,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (ha.trans_le hx) h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact ordered hx h

theorem log_max_lipschitz {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    |Real.log (max x a) - Real.log (max y a)| ≤ a⁻¹ * |x - y| := by
  calc
    _ ≤ |max x a - max y a| / a := abs_log_sub_log_le_div ha (le_max_right _ _) (le_max_right _ _)
    _ ≤ |x - y| / a := div_le_div_of_nonneg_right (abs_max_sub_max_le_abs x y a) ha.le
    _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def operatorCutoffPotential (T : Module.End ℂ E) (a : ℝ) : ℝ :=
  (∑ i : Fin (Module.finrank ℂ E), Real.log (max (T.singularValues i) a)) /
    (Module.finrank ℂ E : ℝ)

theorem operatorCutoffPotential_difference_le (A B : Module.End ℂ E)
    (hA : Function.Injective A) (hB : Function.Injective B) {a : ℝ} (ha : 0 < a) :
    |operatorCutoffPotential A a - operatorCutoffPotential B a| ≤
      (a⁻¹ * Real.sqrt ((Module.finrank ℂ E : ℝ) * operatorHilbertSchmidtSq (A - B))) /
        (Module.finrank ℂ E : ℝ) := by
  unfold operatorCutoffPotential
  rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right
    (singularValues_lipschitz_sum A B hA hB (fun x => Real.log (max x a))
      (inv_nonneg.mpr ha.le) (log_max_lipschitz ha)) (Nat.cast_nonneg _)

theorem sqrt_mul_div_dimension {n e : ℝ} (hn : 0 < n) :
    Real.sqrt (n * e) / n = Real.sqrt e / Real.sqrt n := by
  rw [Real.sqrt_mul hn.le]
  have hs := Real.sq_sqrt hn.le
  have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  field_simp
  nlinarith

theorem operatorCutoffPotential_difference_le_normalized (A B : Module.End ℂ E)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdim : 0 < Module.finrank ℂ E) {a : ℝ} (ha : 0 < a) :
    |operatorCutoffPotential A a - operatorCutoffPotential B a| ≤
      Real.sqrt (operatorHilbertSchmidtSq (A - B)) /
        (a * Real.sqrt (Module.finrank ℂ E : ℝ)) := by
  have h := operatorCutoffPotential_difference_le A B hA hB ha
  rw [mul_div_assoc, sqrt_mul_div_dimension (Nat.cast_pos.mpr hdim)] at h
  convert h using 1 <;> ring

end CircularLawSection6
