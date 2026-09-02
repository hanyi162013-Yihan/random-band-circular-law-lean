import CircularLawSections56.Section5.TaperModelVariance
import CircularLawSections56.Section5.SourceAtomMoments

/-! # Actual band matrices supply Section 3's elementary moment record

Entry integrability, centering and normalized row second moments follow from
the source atom moment assumption and the literal IID sampling map. They are
not additional random-matrix estimates at the taper short-ring boundary.
-/

open MeasureTheory
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace CircularLawSections56.Section5
open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights ShortRingAnchor

theorem integral_comp_measurePreserving_eq_complex
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} {F : Ω → Ξ}
    (hF : MeasurePreserving F μ ν) (g : Ξ → ℂ) (hg : Integrable g ν) :
    (∫ ω, g (F ω) ∂μ) = ∫ x, g x ∂ν := by
  have hm : AEStronglyMeasurable g (Measure.map F μ) := by
    rw [hF.map_eq]
    exact hg.aestronglyMeasurable
  rw [← integral_map hF.measurable.aemeasurable hm, hF.map_eq]

theorem paperIndicatorX_entry_first_moment
    (N d : ℕ) [NeZero N] (hfit : d + 2 ≤ N) (center : Fin (d + 1))
    (b : Fin (d + 2) → ℂ) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => u) ν) (hMean : ∫ u : ℂ, u ∂ν = 0)
    (i j : ZMod N) :
    Integrable (fun ω => paperIndicatorX N d center b ω i j) (iidMeasure ν (N * (d + 2))) ∧
      (∫ ω, paperIndicatorX N d center b ω i j ∂iidMeasure ν (N * (d + 2))) = 0 := by
  classical
  by_cases hslot : ∃ s : Fin (d + 2), j = i - (center.val : ZMod N) + (s.val : ZMod N)
  · obtain ⟨s, rfl⟩ := hslot
    have hMP : MeasurePreserving (fun ω => ω (paperIndicatorFlatIndex N d i s))
        (iidMeasure ν (N * (d + 2))) ν :=
      ⟨measurable_pi_apply _, iidMeasure_map_coordinate ν _⟩
    have hpoint (ω : Fin (N * (d + 2)) → ℂ) :
        paperIndicatorX N d center b ω i (i - (center.val : ZMod N) + (s.val : ZMod N)) =
          b s * ω (paperIndicatorFlatIndex N d i s) := by
      rw [paperIndicatorX, paperScalarBandMatrix_entry_slot N d hfit]
      rfl
    simp_rw [hpoint]
    refine ⟨?_, ?_⟩
    · simpa only [Function.comp_apply] using (hMP.integrable_comp_of_integrable hInt).const_mul (b s)
    · rw [integral_const_mul, integral_comp_measurePreserving_eq_complex hMP _ hInt, hMean, mul_zero]
  · have hs : ∀ s : Fin (d + 2), j ≠ i - (center.val : ZMod N) + (s.val : ZMod N) := by
      simpa only [not_exists] using hslot
    simp only [paperIndicatorX, paperScalarBandMatrix, hs, if_false, Finset.sum_const_zero,
      integral_zero]
    exact ⟨integrable_zero _ _ _, trivial⟩

theorem literal_source_centered_row_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (hc₀ : ∀ n, 0 < c₀ n) (hfit : ∀ n, d n + 2 ≤ k n + 1)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (hMom : ∀ n, AtomMomentAssumption21 (ν n) id)
    (samples : ∀ n, Ω → Fin ((k n + 1) * (d n + 2)) → ℂ)
    (hSamples : ∀ n, MeasurePreserving (samples n) μ (iidMeasure (ν n) ((k n + 1) * (d n + 2)))) :
    CenteredMatrixRowSecondMomentInputs μ
      (fun n ω => literalIndicatorMatrix (k n) (d n) (center n) (profile n).b (samples n ω)) 1 := by
  have hfirst (n : ℕ) (i j : Fin (k n + 1)) :=
    paperIndicatorX_entry_first_moment (k n + 1) (d n) (hfit n) (center n) (profile n).b
      (ν n) (hMom n).integrable (hMom n).centered
      ((ZMod.finEquiv (k n + 1)) i) ((ZMod.finEquiv (k n + 1)) j)
  have hsecond (n : ℕ) (i j : Fin (k n + 1)) :=
    paperIndicatorX_entry_second_moment (k n + 1) (d n) (hfit n) (center n) (profile n) (hc₀ n)
      (ν n) (hMom n).normSqIntegrable (hMom n).unitSecondMoment
      ((ZMod.finEquiv (k n + 1)) i) ((ZMod.finEquiv (k n + 1)) j)
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · intro n i j
    exact (hSamples n).integrable_comp_of_integrable (hfirst n i j).1
  · intro n i j
    exact (hSamples n).integrable_comp_of_integrable (hsecond n i j).1
  · intro n i j
    exact (integral_comp_measurePreserving_eq_complex (hSamples n) _ (hfirst n i j).1).trans
      (hfirst n i j).2
  · intro n i
    have he (j : Fin (k n + 1)) :=
      (integral_comp_measurePreserving_eq (hSamples n) _ (hsecond n i j).1).trans (hsecond n i j).2
    change (∑ j : Fin (k n + 1), ∫ ω,
      ‖paperIndicatorX (k n + 1) (d n) (center n) (profile n).b (samples n ω)
        ((ZMod.finEquiv (k n + 1)) i) ((ZMod.finEquiv (k n + 1)) j)‖ ^ 2 ∂μ) = 1
    calc
      _ = ∑ j : Fin (k n + 1), cyclicVarianceProfile (k n + 1) (d n + 2)
          ((center n).val : ZMod (k n + 1)) (profile n).q
          ((ZMod.finEquiv (k n + 1)) i) ((ZMod.finEquiv (k n + 1)) j) := by
        apply Finset.sum_congr rfl
        intro j _
        exact he j
      _ = 1 :=
        ((ZMod.finEquiv (k n + 1)).toEquiv.sum_comp
          (fun j => cyclicVarianceProfile (k n + 1) (d n + 2)
            ((center n).val : ZMod (k n + 1)) (profile n).q ((ZMod.finEquiv (k n + 1)) i) j)).trans
          ((cyclicVarianceProfile_row_sum (k n + 1) (d n + 2)
            ((center n).val : ZMod (k n + 1)) (profile n).q _).trans (profile n).normalized)

end CircularLawSections56.Section5
