import ShortRingAnchor.BoundedDensityRepresentative
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Construct the source density record from literal measure domination -/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
set_option autoImplicit false
namespace BernoulliSection10Source
open ShortRingAnchor

/-- The Radon--Nikodym derivative supplies the source's density record;
it is not an additional assumption on a dominated probability law. -/
def boundedDensityOfMeasureLe
    {E : Type*} [MeasurableSpace E] {μ ν : Measure E}
    [SigmaFinite μ] [SigmaFinite ν] {L : ℝ}
    (h : μ ≤ ENNReal.ofReal L • ν) :
    HasBoundedDensityWithRespectTo (top := ∞) μ ν := by
  have hac : μ ≪ ν := by
    intro s hs
    apply le_antisymm ?_ zero_le
    simpa only [Measure.smul_apply, smul_eq_mul, hs, mul_zero] using h s
  refine
    { density := μ.rnDeriv ν
      densityAEMeasurable := (μ.measurable_rnDeriv ν).aemeasurable
      bound := ENNReal.ofReal L
      bound_lt_top := ENNReal.ofReal_lt_top
      density_le_bound := ?_
      law_eq_withDensity := (Measure.withDensity_rnDeriv_eq μ ν hac).symm }
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν)
  intro s _ _
  have he := (Measure.setLIntegral_rnDeriv_le (μ := μ) (ν := ν) s).trans (h s)
  simpa only [lintegral_const, Measure.restrict_apply_univ, Measure.smul_apply,
    smul_eq_mul] using he

/-- The real high-band source requires an everywhere bounded measurable
density. It is constructed from the original law and normalized exactly. -/
theorem exists_real_density_representative
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {L : ℝ}
    (h : μ ≤ ENNReal.ofReal L • (volume : Measure ℝ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ f : ℝ → ℝ≥0∞, Measurable f ∧
      (∫⁻ x, f x) = 1 ∧ (∀ x, f x ≤ ENNReal.ofReal ρ) ∧
      volume.withDensity f = μ := by
  obtain ⟨ρ, hρ, f, hf, hbound, hlaw⟩ :=
    (boundedDensityOfMeasureLe h).exists_measurable_bounded_density
  refine ⟨ρ, hρ, f, hf, ?_, hbound, hlaw⟩
  have he := congrArg (fun ν : Measure ℝ => ν univ) hlaw
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    measure_univ] using he

end BernoulliSection10Source
