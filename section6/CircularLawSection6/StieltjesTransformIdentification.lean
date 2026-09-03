import CircularLawSection6.StieltjesHardEdge
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The genuine complex Stieltjes transform and the hard-edge kernel

The imaginary part of the complex resolvent integral is exactly the Poisson
integral used in the hard-edge estimate. Integrability is proved from finite
mass and a positive imaginary height; it is not supplied as an extra premise.
-/

open MeasureTheory Set
noncomputable section

namespace CircularLawSection6

def singularStieltjesKernel (t s : ℝ) : ℂ :=
  ((s : ℂ) - (t : ℂ) * Complex.I)⁻¹

theorem singularStieltjes_denominator_norm {t : ℝ} (ht : 0 < t) (s : ℝ) :
    t ≤ ‖(s : ℂ) - (t : ℂ) * Complex.I‖ := by
  simpa only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul,
    add_zero, zero_sub, abs_neg, abs_of_pos ht] using
    Complex.abs_im_le_norm ((s : ℂ) - (t : ℂ) * Complex.I)

theorem singularStieltjesKernel_im (t s : ℝ) :
    (singularStieltjesKernel t s).im = singularPoissonKernel t s := by
  simp [singularStieltjesKernel, singularPoissonKernel, Complex.inv_im,
    Complex.normSq_apply, pow_two]

theorem singularStieltjesKernel_norm_le {t : ℝ} (ht : 0 < t) (s : ℝ) :
    ‖singularStieltjesKernel t s‖ ≤ 1 / t := by
  unfold singularStieltjesKernel
  rw [norm_inv, ← one_div]
  exact one_div_le_one_div_of_le ht (singularStieltjes_denominator_norm ht s)

theorem singularStieltjesKernel_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (singularStieltjesKernel t) := by
  apply Continuous.inv₀ (by fun_prop)
  intro s
  exact norm_pos_iff.mp (ht.trans_le (singularStieltjes_denominator_norm ht s))

theorem singularStieltjesKernel_integrable (σ : Measure ℝ) [IsFiniteMeasure σ]
    {t : ℝ} (ht : 0 < t) : Integrable (singularStieltjesKernel t) σ := by
  apply (integrable_const (1 / t)).mono'
  · exact (singularStieltjesKernel_continuous ht).measurable.aestronglyMeasurable
  · exact ae_of_all σ (singularStieltjesKernel_norm_le ht)

def singularStieltjesTransform (σ : Measure ℝ) (t : ℝ) : ℂ :=
  ∫ s, singularStieltjesKernel t s ∂σ

theorem singularStieltjesTransform_im (σ : Measure ℝ) [IsFiniteMeasure σ]
    {t : ℝ} (ht : 0 < t) :
    (singularStieltjesTransform σ t).im = ∫ s, singularPoissonKernel t s ∂σ := by
  unfold singularStieltjesTransform
  have hi : (∫ s, (singularStieltjesKernel t s).im ∂σ) =
      (∫ s, singularStieltjesKernel t s ∂σ).im := by
    simpa only [RCLike.im_eq_complex_im] using
      integral_im (singularStieltjesKernel_integrable σ ht)
  exact hi.symm.trans (integral_congr_ae (ae_of_all σ (singularStieltjesKernel_im t)))

theorem hardEdge_mass_le_of_stieltjes_norm (σ : Measure ℝ) [IsFiniteMeasure σ]
    {t C : ℝ} (ht : 0 < t) (hbound : ‖singularStieltjesTransform σ t‖ ≤ C) :
    σ.real (Icc 0 t) ≤ 2 * C * t := by
  apply hardEdge_mass_le_of_poisson_bound σ ht
  rw [← singularStieltjesTransform_im σ ht]
  exact (Complex.im_le_norm _).trans hbound

theorem hardEdge_cdf_le_of_stieltjes_norm (σ : Measure ℝ) [IsFiniteMeasure σ]
    (hpos : ∀ᵐ s ∂σ, 0 ≤ s) {t C : ℝ} (ht : 0 < t)
    (hbound : ‖singularStieltjesTransform σ t‖ ≤ C) :
    σ.real (Iic t) ≤ 2 * C * t := by
  apply hardEdge_cdf_le_of_poisson_bound σ hpos ht
  rw [← singularStieltjesTransform_im σ ht]
  exact (Complex.im_le_norm _).trans hbound

end CircularLawSection6
