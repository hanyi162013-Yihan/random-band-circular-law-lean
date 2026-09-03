/- Source snapshot: upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/DensityScaling.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

open scoped ENNReal

open MeasureTheory

namespace LivshytsProjectionFormalization

noncomputable section

/-- Translation followed by a nonzero real dilation on a finite-dimensional real vector space.
The exponent in the Jacobian is the real dimension of the space. -/
theorem lintegral_comp_add_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [Measure.IsAddHaarMeasure mu]
    (f : E → ℝ≥0∞) (hf : Measurable f) (a : E) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ x, f (a + r • x) ∂mu) =
      ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| * ∫⁻ x, f x ∂mu := by
  calc
    (∫⁻ x, f (a + r • x) ∂mu) =
        ∫⁻ y, f (a + y) ∂Measure.map (r • ·) mu := by
          simpa only [Function.comp_apply] using
            (MeasureTheory.lintegral_map
              (μ := mu) (f := fun y ↦ f (a + y)) (g := fun x ↦ r • x)
              (hf.comp (measurable_const.add measurable_id))
              (measurable_const_smul r)).symm
    _ = ∫⁻ y, f (a + y)
          ∂(ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| • mu) := by
          rw [Measure.map_addHaar_smul mu hr]
    _ = ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| *
          ∫⁻ y, f (a + y) ∂mu := by
          rw [lintegral_smul_measure]
          rfl
    _ = ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| * ∫⁻ x, f x ∂mu := by
          congr 1
          calc
            (∫⁻ y, f (a + y) ∂mu) =
                ∫⁻ y, f y ∂Measure.map (a + ·) mu := by
                  simpa only [Function.comp_apply] using
                    (MeasureTheory.lintegral_map
                      (μ := mu) (f := f) (g := fun y ↦ a + y) hf
                      (measurable_const.add measurable_id)).symm
            _ = ∫⁻ y, f y ∂mu := by
              rw [Measure.IsAddLeftInvariant.map_add_left_eq_self]

/-- The one-dimensional real specialization of `lintegral_comp_add_smul`. -/
theorem real_lintegral_comp_add_mul
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    (∫⁻ x : ℝ, f (a + r * x)) = ENNReal.ofReal |r⁻¹| * ∫⁻ x : ℝ, f x := by
  simpa only [smul_eq_mul, Module.finrank_self, pow_one] using
    (lintegral_comp_add_smul volume f hf a hr)

/-- For a positive real dilation, the real Jacobian is `r⁻¹`. -/
theorem real_lintegral_comp_add_mul_of_pos
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x : ℝ, f (a + r * x)) = ENNReal.ofReal r⁻¹ * ∫⁻ x : ℝ, f x := by
  simpa [abs_of_pos (inv_pos.mpr hr)] using real_lintegral_comp_add_mul f hf a hr.ne'

/-- The complex plane has real dimension two, hence a real dilation has Jacobian `r⁻²`. -/
theorem complex_lintegral_comp_add_real_smul_of_pos
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) (a : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫⁻ z : ℂ, f (a + r • z)) = ENNReal.ofReal (r⁻¹ ^ 2) * ∫⁻ z : ℂ, f z := by
  simpa [Complex.finrank_real_complex, inv_pow, abs_of_pos hr] using
    (lintegral_comp_add_smul volume f hf a hr.ne')

/-- Candidate density of `a + r X` when `X` has density `f`. -/
def realAffineDensity (f : ℝ → ℝ≥0∞) (a r y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |r⁻¹| * f (r⁻¹ * (y - a))

theorem measurable_realAffineDensity
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (a r : ℝ) :
    Measurable (realAffineDensity f a r) := by
  unfold realAffineDensity
  exact measurable_const.mul (hf.comp (by fun_prop))

/-- A real density bounded by `K` becomes bounded by `K / |r|` after dilation by `r`. -/
theorem realAffineDensity_le
    {f : ℝ → ℝ≥0∞} {K : ℝ} (hf : ∀ x, f x ≤ ENNReal.ofReal K)
    (a : ℝ) {r : ℝ} (_hr : r ≠ 0) (y : ℝ) :
    realAffineDensity f a r y ≤ ENNReal.ofReal (K / |r|) := by
  rw [realAffineDensity]
  calc
    ENNReal.ofReal |r⁻¹| * f (r⁻¹ * (y - a)) ≤
        ENNReal.ofReal |r⁻¹| * ENNReal.ofReal K := by gcongr; exact hf _
    _ = ENNReal.ofReal (K / |r|) := by
      rw [← ENNReal.ofReal_mul (abs_nonneg r⁻¹)]
      congr 1
      rw [abs_inv, inv_mul_eq_div]

end

end LivshytsProjectionFormalization

