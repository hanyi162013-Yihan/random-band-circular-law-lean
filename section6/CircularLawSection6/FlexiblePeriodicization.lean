import CircularLawSection6.OneBlockPeriodicization

/-! # Periodicization with an exact direct branch

Every matrix admits either one unchanged block or blocks of the desired
mesoscopic size. Thus the cutoff error is controlled by the original
mesoscopic scale, not by its minimum with the matrix dimension.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem exists_one_or_periodic_block_lengths {N H m₀ : ℕ}
    (hfitN : 2 * H + 1 ≤ N) (hfitm : 2 * H + 1 ≤ m₀) :
    ∃ (q : ℕ) (len : Fin q → ℕ), 0 < q ∧ (∑ j, len j) = N ∧
      (∀ j, 2 * H + 1 ≤ len j ∧ len j ≤ 2 * m₀) ∧
      (q = 1 ∨ ∀ j, m₀ ≤ len j) := by
  by_cases hlarge : m₀ ≤ N
  · obtain ⟨q, len, hq, hsum, hlen⟩ := exists_periodic_block_lengths (by omega : 0 < m₀) hlarge
    exact ⟨q, len, hq, hsum,
      fun j => ⟨hfitm.trans (hlen j).1, (hlen j).2.le⟩,
      Or.inr (fun j => (hlen j).1)⟩
  · refine ⟨1, fun _ => N, by decide, by simp, ?_, Or.inl rfl⟩
    intro j
    exact ⟨hfitN, by omega⟩

theorem one_or_periodicization_expected_cutoff_ae
    {q : ℕ} (len : Fin q → ℕ) [∀ j, NeZero (len j)] [NeZero (∑ j, len j)]
    {H m₀ : ℕ} (hm₀ : 0 < m₀) (hmin : q = 1 ∨ ∀ j, m₀ ≤ len j)
    (hfit : ∀ j, 2 * H + 1 ≤ len j)
    (b : Fin (2 * H + 1) → ℂ) (hb : ∑ s, ‖b s‖ ^ 2 = 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν) (hMoment : (∫ u : ℂ, ‖u‖ ^ 2 ∂ν) = 1) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ a : ℝ, 0 < a →
      Integrable (fun ω =>
        |matrixCutoffPotential (routedBandMatrix (fullBlockRoute len H) b ω - z • 1) a -
          matrixCutoffPotential (routedBandMatrix (periodicBlockRoute len H) b ω - z • 1) a|)
        (Measure.pi (fun _ : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) => ν)) ∧
      (∫ ω,
        |matrixCutoffPotential (routedBandMatrix (fullBlockRoute len H) b ω - z • 1) a -
          matrixCutoffPotential (routedBandMatrix (periodicBlockRoute len H) b ω - z • 1) a|
        ∂Measure.pi (fun _ : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) => ν)) ≤
          Real.sqrt (8 * (H : ℝ) / m₀) / a := by
  rcases hmin with hq | hmin
  · subst q
    filter_upwards with z
    intro a ha
    simp only [oneBlock_matrix_eq, sub_self, abs_zero, integral_zero]
    exact ⟨integrable_const 0, div_nonneg (Real.sqrt_nonneg _) ha.le⟩
  · exact periodicization_expected_cutoff_ae len hm₀ hmin hfit b hb ν hInt hMoment

end CircularLawSection6
