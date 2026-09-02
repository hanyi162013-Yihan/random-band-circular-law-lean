import CircularLawSections56.Section5.Section4CompletedAssembly

/-! # Harmless enlargement of the accepted finite Section 4 constant

Section 5 can use the maximum of its own explicit transfer constant and the
constant supplied by Section 4. The caller need not reprove Section 4 with a
possibly smaller preselected numerical constant.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5

theorem CompletedSection4PressureInput.mono
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    {μ : ∀ n, Measure (Ω n)} {active : ℕ → Bool}
    {raw : ∀ n, Ω n → ℝ} {Y : ∀ n, ι n → Ω n → ℝ}
    {scale W : ℕ → ℕ} {C D : ℝ}
    (h : CompletedSection4PressureInput μ active raw Y scale W C)
    (hCD : C ≤ D) (hW : ∀ n, active n = true → 0 < W n) :
    CompletedSection4PressureInput μ active raw Y scale W D where
  seam_integrable := h.seam_integrable
  seam_bound := by
    intro n hn
    have hl : 0 ≤ paperLogEW W n :=
      zero_le_one.trans (one_le_paperLogEW_of_bandwidth_pos W n (hW n hn))
    exact (h.seam_bound n hn).trans (mul_le_mul_of_nonneg_right hCD
      (mul_nonneg (Nat.cast_nonneg (W n)) hl))
  pressure_memLp := h.pressure_memLp
  pressure_bound := by
    intro n hn
    have hl : 0 ≤ paperLogEW W n :=
      zero_le_one.trans (one_le_paperLogEW_of_bandwidth_pos W n (hW n hn))
    exact (h.pressure_bound n hn).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD (Real.sqrt_nonneg _)) hl)

end CircularLawSections56.Section5
