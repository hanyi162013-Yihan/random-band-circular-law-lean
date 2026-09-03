import BernoulliSection10.Section3Inputs
import BernoulliSection10.ResetSandwichLaw
import ShortRingAnchor.AtomAssumption21
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! The explicit circular Gaussian atom used by the Section 3 adapter.
Its moments are proved here, so no extra reference-moment assumption is needed. -/

open MeasureTheory ProbabilityTheory
noncomputable section
namespace BernoulliSection8.Section3Bridge
open BernoulliSection10 BernoulliSection10.SourceInputs ShortRingAnchor

def gaussianAtom : ℝ × ℝ → ℂ := Complex.equivRealProdCLM.symm

theorem gaussianAtom_hasGaussianLaw : HasGaussianLaw gaussianAtom circularGaussianPairLaw := by
  letI : IsGaussian circularGaussianPairLaw := by
    unfold circularGaussianPairLaw
    infer_instance
  exact IsGaussian.hasGaussianLaw_id.map Complex.equivRealProdCLM.symm.toContinuousLinearMap

theorem gaussianAtom_measurable : Measurable gaussianAtom :=
  Complex.equivRealProdCLM.symm.continuous.measurable

theorem gaussian_coordinate_second_moment :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 (1 / 2)) = (1 / 2 : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1 / 2)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

theorem gaussianAtom_moments : AtomMomentAssumption21 circularGaussianPairLaw gaussianAtom := by
  have hf : MeasurePreserving (Prod.fst : ℝ × ℝ → ℝ) circularGaussianPairLaw
      (gaussianReal 0 (1 / 2)) := measurePreserving_fst
  have hs : MeasurePreserving (Prod.snd : ℝ × ℝ → ℝ) circularGaussianPairLaw
      (gaussianReal 0 (1 / 2)) := measurePreserving_snd
  have hmeanf : (∫ x : ℝ × ℝ, x.1 ∂circularGaussianPairLaw) = 0 := by
    simpa using real_integral_comp_measurePreserving hf measurable_id
  have hmeans : (∫ x : ℝ × ℝ, x.2 ∂circularGaussianPairLaw) = 0 := by
    simpa using real_integral_comp_measurePreserving hs measurable_id
  have hsq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 (1 / 2)) := by
    simpa only [Real.norm_eq_abs, sq_abs, id_eq] using
      (memLp_id_gaussianReal (μ := 0) (v := 1 / 2) 2).integrable_norm_pow' (p := 2)
  have hsqf : (∫ x : ℝ × ℝ, x.1 ^ 2 ∂circularGaussianPairLaw) = (1 / 2 : ℝ) :=
    (real_integral_comp_measurePreserving hf (by fun_prop)).trans
      gaussian_coordinate_second_moment
  have hsqs : (∫ x : ℝ × ℝ, x.2 ^ 2 ∂circularGaussianPairLaw) = (1 / 2 : ℝ) :=
    (real_integral_comp_measurePreserving hs (by fun_prop)).trans
      gaussian_coordinate_second_moment
  refine ⟨gaussianAtom_measurable.stronglyMeasurable, ?_, ?_, ?_⟩
  · apply Complex.ext
    · simpa [gaussianAtom] using
        (integral_re gaussianAtom_hasGaussianLaw.integrable).symm.trans hmeanf
    · simpa [gaussianAtom] using
        (integral_im gaussianAtom_hasGaussianLaw.integrable).symm.trans hmeans
  · have heq (x : ℝ × ℝ) : ‖gaussianAtom x‖ ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [gaussianAtom, pow_two]
    have hfi : Integrable (fun x : ℝ × ℝ => x.1 ^ 2) circularGaussianPairLaw :=
      hf.integrable_comp_of_integrable hsq
    have hsi : Integrable (fun x : ℝ × ℝ => x.2 ^ 2) circularGaussianPairLaw :=
      hs.integrable_comp_of_integrable hsq
    simp_rw [heq]
    rw [integral_add hfi hsi, hsqf, hsqs]
    norm_num
  · exact (gaussianAtom_hasGaussianLaw.memLp (p := 3) (by norm_num)).integrable_norm_pow'

end BernoulliSection8.Section3Bridge
