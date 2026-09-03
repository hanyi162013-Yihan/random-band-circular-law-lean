import CircularLawSection6.NegativeMomentCutoff

/-! # Finite-prefix transport on genuinely varying probability spaces -/

open MeasureTheory Filter Topology
open CircularLawSections56.Section5

namespace CircularLawSection6

theorem tendstoInProbabilityTri_shift_iff
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (a : ℝ) (K : ℕ) :
    TendstoInProbabilityTri (fun n => μ (n + K)) (fun n => X (n + K)) a ↔
      TendstoInProbabilityTri μ X a := by
  constructor
  · intro h ε hε
    exact (tendsto_add_atTop_iff_nat K).mp (h ε hε)
  · intro h ε hε
    exact (h ε hε).comp (tendsto_add_atTop_nat K)

theorem boundedInProbabilityTri_shift
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (h : BoundedInProbabilityTri μ X) (K : ℕ) :
    BoundedInProbabilityTri (fun n => μ (n + K)) (fun n => X (n + K)) := by
  intro δ hδ
  obtain ⟨C, hC, hbound⟩ := h δ hδ
  exact ⟨C, hC, (tendsto_add_atTop_nat K).eventually hbound⟩

end CircularLawSection6
