import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Isometry

/-! # The actual normalized circular complex Gaussian

The real standard Gaussian on `ℂ` has two unit-variance real coordinates.
Scaling it by `1 / sqrt 2` gives the manuscript's complex atoms, with
`E |g|² = 1`. Gaussianity, mean zero, and rotation invariance are proved from
mathlib's concrete distribution, not assumed as an abstract atom interface.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace CircularLawSection6

def complexGaussianScale : ℂ →L[ℝ] ℂ :=
  (Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ ℂ

@[simp] theorem complexGaussianScale_apply (z : ℂ) :
    complexGaussianScale z = (Real.sqrt 2)⁻¹ • z := rfl

def circularComplexGaussian : Measure ℂ :=
  (stdGaussian ℂ).map complexGaussianScale

instance circularComplexGaussian_isProbability : IsProbabilityMeasure circularComplexGaussian :=
  Measure.isProbabilityMeasure_map complexGaussianScale.continuous.measurable.aemeasurable

instance circularComplexGaussian_isGaussian : IsGaussian circularComplexGaussian := by
  unfold circularComplexGaussian
  infer_instance

theorem circularComplexGaussian_integrable : Integrable (fun z : ℂ => z)
    circularComplexGaussian := IsGaussian.integrable_id

theorem circularComplexGaussian_mean : (∫ z : ℂ, z ∂circularComplexGaussian) = 0 := by
  rw [circularComplexGaussian, integral_map complexGaussianScale.continuous.measurable.aemeasurable
    (by fun_prop)]
  rw [complexGaussianScale.integral_comp_id_comm IsGaussian.integrable_id,
    integral_id_stdGaussian, map_zero]

theorem circularComplexGaussian_sq_integrable :
    Integrable (fun z : ℂ => ‖z‖ ^ 2) circularComplexGaussian := by
  simpa only [id_eq] using
    (IsGaussian.memLp_two_id (μ := circularComplexGaussian)).integrable_norm_pow (by decide)

theorem realStandardComplexGaussian_secondMoment :
    (∫ z : ℂ, ‖z‖ ^ 2 ∂stdGaussian ℂ) = 2 := by
  have hr : (∫ z : ℂ, z.re ^ 2 ∂stdGaussian ℂ) = 1 := by
    have h := variance_dual_stdGaussian Complex.reCLM
    rw [variance_of_integral_eq_zero (by fun_prop)
      (integral_strongDual_stdGaussian Complex.reCLM), Complex.reCLM_norm, one_pow] at h
    exact h
  have hi : (∫ z : ℂ, z.im ^ 2 ∂stdGaussian ℂ) = 1 := by
    have h := variance_dual_stdGaussian Complex.imCLM
    rw [variance_of_integral_eq_zero (by fun_prop)
      (integral_strongDual_stdGaussian Complex.imCLM), Complex.imCLM_norm, one_pow] at h
    exact h
  have hri : Integrable (fun z : ℂ => z.re ^ 2) (stdGaussian ℂ) :=
    (IsGaussian.memLp_dual _ Complex.reCLM 2 (by simp)).integrable_sq
  have hii : Integrable (fun z : ℂ => z.im ^ 2) (stdGaussian ℂ) :=
    (IsGaussian.memLp_dual _ Complex.imCLM 2 (by simp)).integrable_sq
  simp_rw [Complex.sq_norm, Complex.normSq_apply, ← pow_two]
  rw [integral_add hri hii, hr, hi]
  norm_num

theorem complexGaussianScale_norm_sq (z : ℂ) :
    ‖complexGaussianScale z‖ ^ 2 = (1 / 2 : ℝ) * ‖z‖ ^ 2 := by
  simp [Real.norm_eq_abs, mul_pow, inv_pow, Real.sq_sqrt]

theorem circularComplexGaussian_secondMoment :
    (∫ z : ℂ, ‖z‖ ^ 2 ∂circularComplexGaussian) = 1 := by
  rw [circularComplexGaussian, integral_map complexGaussianScale.continuous.measurable.aemeasurable
    (by fun_prop)]
  simp_rw [complexGaussianScale_norm_sq]
  rw [integral_const_mul, realStandardComplexGaussian_secondMoment]
  norm_num

theorem circularComplexGaussian_rotation (a : Circle) :
    circularComplexGaussian.map (fun z : ℂ => (a : ℂ) * z) = circularComplexGaussian := by
  have hrot : Measurable (fun z : ℂ => (a : ℂ) * z) := by fun_prop
  have hscale : Measurable complexGaussianScale := complexGaussianScale.continuous.measurable
  have hcomm : (fun z : ℂ => (a : ℂ) * z) ∘ complexGaussianScale =
      complexGaussianScale ∘ rotation a := by
    ext z
    simp [Algebra.smul_def, mul_left_comm]
  rw [circularComplexGaussian, Measure.map_map hrot hscale, hcomm,
    ← Measure.map_map hscale (rotation a).continuous.measurable,
    stdGaussian_map]

theorem circularComplexGaussian_rotation_preserving (a : Circle) :
    MeasurePreserving (fun z : ℂ => (a : ℂ) * z)
      circularComplexGaussian circularComplexGaussian :=
  ⟨by fun_prop, circularComplexGaussian_rotation a⟩

/-- Atomlessness follows from the concrete Gaussian law and its nonzero second
moment; it is needed later in the diagonal/cofactor nonvanishing argument. -/
instance circularComplexGaussian_nullSingleton : NullSingletonClass circularComplexGaussian := by
  apply IsGaussian.nullSingletonClass
  intro z hz
  have hm := circularComplexGaussian_mean
  have hs := circularComplexGaussian_secondMoment
  rw [hz, integral_dirac] at hm hs
  simp [hm] at hs

end CircularLawSection6
