import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.Prod

/-! # Integrating an invariant angular average

Joint integrability is proved from measurability, invariance, and integrability
of the original observable. It is not an extra Fubini assumption.
-/

open MeasureTheory Set Real

noncomputable section

namespace CircularLawSection6

def phaseAverage (f : ℝ → ℝ) : ℝ := (2 * π)⁻¹ * ∫ θ in 0..2 * π, f θ

theorem integral_comp_preserving_real {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Measurable f) :
    (∫ ω, f (T ω) ∂μ) = ∫ ω, f ω ∂μ := by
  rw [← integral_map_of_stronglyMeasurable hT.measurable hf.stronglyMeasurable, hT.map_eq]

theorem invariant_phase_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (T : ℝ → Ω → Ω)
    (hT : Measurable (fun v : ℝ × Ω => T v.1 v.2))
    (hpres : ∀ θ, MeasurePreserving (T θ) μ μ)
    {f : Ω → ℝ} (hf : Measurable f) (hfi : Integrable f μ) :
    Integrable (fun v : ℝ × Ω => f (T v.1 v.2))
      ((volume.restrict (Ioc 0 (2 * π))).prod μ) := by
  apply (integrable_prod_iff (hf.comp hT).aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ (fun θ => (hpres θ).integrable_comp_of_integrable hfi)
  · change Integrable (fun θ => ∫ ω, ‖f (T θ ω)‖ ∂μ) (volume.restrict (Ioc 0 (2 * π)))
    have heq (θ : ℝ) : (∫ ω, ‖f (T θ ω)‖ ∂μ) = ∫ ω, ‖f ω‖ ∂μ :=
      integral_comp_preserving_real (hpres θ) hf.norm
    simpa only [heq] using
      (integrable_const (∫ ω, ‖f ω‖ ∂μ) :
        Integrable (fun _ : ℝ => ∫ ω, ‖f ω‖ ∂μ) (volume.restrict (Ioc 0 (2 * π))))

theorem invariant_phaseAverage_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (T : ℝ → Ω → Ω)
    (hT : Measurable (fun v : ℝ × Ω => T v.1 v.2))
    (hpres : ∀ θ, MeasurePreserving (T θ) μ μ)
    {f : Ω → ℝ} (hf : Measurable f) (hfi : Integrable f μ) :
    Integrable (fun ω => phaseAverage (fun θ => f (T θ ω))) μ ∧
      (∫ ω, phaseAverage (fun θ => f (T θ ω)) ∂μ) = ∫ ω, f ω ∂μ := by
  have hp := invariant_phase_integrable T hT hpres hf hfi
  have hp' : Integrable (Function.uncurry (fun ω θ => f (T θ ω)))
      (μ.prod (volume.restrict (Ioc 0 (2 * π)))) := hp.swap
  have hπ : 0 ≤ 2 * π := by positivity
  constructor
  · simpa only [phaseAverage, intervalIntegral.integral_of_le hπ] using
      hp.integral_prod_right.const_mul ((2 * π)⁻¹)
  · simp only [phaseAverage, intervalIntegral.integral_of_le hπ]
    rw [integral_const_mul, integral_integral_swap hp']
    simp only [integral_comp_preserving_real (hpres _) hf]
    rw [← intervalIntegral.integral_of_le hπ, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity : 2 * π ≠ 0), one_mul]

end CircularLawSection6
