import CircularLawSections56.Section5.AtomFreshFinite
import ShortRingAnchor.AtomAssumption21

/-! # Reuse the existing Section 3 Assumption 2.1 moment record

The source record explicitly contains centering, unit second moment, and finite
third absolute moment. The second-moment integrability needed by Section 5 is
derived, not requested again. The real branch uses `ofReal` without imposing
a planar density on its pushed-forward law.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5
open CircularLawSection4 ShortRingAnchor

theorem real_source_moments_complexify
    (ρ : Measure ℝ) (h : AtomMomentAssumption21 ρ Complex.ofReal) :
    AtomMomentAssumption21 (realComplexAtomLaw ρ) id := by
  refine ⟨stronglyMeasurable_id, ?_, ?_, ?_⟩
  · rw [realComplexAtomLaw, integral_map Complex.continuous_ofReal.measurable.aemeasurable
      stronglyMeasurable_id.aestronglyMeasurable]
    exact h.centered
  · have hc : Continuous (fun u : ℂ => ‖u‖ ^ 2) := continuous_norm.pow 2
    change (∫ u : ℂ, ‖u‖ ^ 2 ∂Measure.map Complex.ofReal ρ) = 1
    rw [integral_map Complex.continuous_ofReal.measurable.aemeasurable
      hc.measurable.aestronglyMeasurable]
    exact h.unitSecondMoment
  · apply (integrable_map_measure
      (continuous_norm.pow 3).measurable.aestronglyMeasurable
      Complex.continuous_ofReal.measurable.aemeasurable).2
    exact h.thirdMomentIntegrable

theorem real_source_moments_second_integrable
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (h : AtomMomentAssumption21 ρ Complex.ofReal) :
    Integrable (fun u : ℝ => u ^ 2) ρ := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h.normSqIntegrable

theorem real_source_moments_second_eq_one
    (ρ : Measure ℝ) (h : AtomMomentAssumption21 ρ Complex.ofReal) :
    (∫ u : ℝ, u ^ 2 ∂ρ) = 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h.unitSecondMoment

theorem AtomTransferControl.real_of_source_moments
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (L : ℝ) (hL : 0 ≤ L)
    (hDensity : RealIntervalBound ρ (ENNReal.ofReal L))
    (h : AtomMomentAssumption21 ρ Complex.ofReal) :
    AtomTransferControl (realComplexAtomLaw ρ) (realFreshLogConstant L)
      (Real.log (max 1 (2 * L)) + 1) :=
  AtomTransferControl.real ρ L hL hDensity (real_source_moments_second_integrable ρ h)
    (real_source_moments_second_eq_one ρ h).le

theorem AtomTransferControl.complex_of_source_moments
    (f : ℂ → ENNReal) [IsProbabilityMeasure (volume.withDensity f)] (L : ℝ) (hL : 0 ≤ L)
    (hDensity : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L)
    (h : AtomMomentAssumption21 (volume.withDensity f) id) :
    AtomTransferControl (volume.withDensity f) (uniformFreshNegativeConstant L)
      ((Real.log (max 1 (Real.pi * L)) + 1) / 2) :=
  AtomTransferControl.complex f L hL hDensity h.normSqIntegrable h.unitSecondMoment.le

theorem real_source_density_interval_bound
    (f : ℝ → ENNReal) (L : ℝ)
    (hDensity : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ ENNReal.ofReal L) :
    RealIntervalBound (volume.withDensity f) (ENNReal.ofReal L) :=
  realIntervalBound_withDensity hDensity

end CircularLawSections56.Section5
