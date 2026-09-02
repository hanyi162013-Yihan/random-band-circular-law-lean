import Mathlib.MeasureTheory.Integral.Prod

/-!
# Uniform section bounds on a probability product

This small Fubini helper upgrades a uniform integrability and integral bound
on every inner section to the corresponding statement on the whole product
probability space.  It is used when selected fresh atoms are integrated
first and all frozen atoms are averaged afterwards.
-/

open scoped MeasureTheory
open MeasureTheory

namespace CircularLawSection4

/-- A nonnegative measurable function whose inner sections are integrable
and have a uniform integral bound is integrable on the product, with the
same bound after averaging the outer probability variable. -/
theorem integrable_prod_and_integral_le_of_forall_integrable_integral_le
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    (mu : Measure Alpha) (nu : Measure Beta)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (F : Alpha × Beta → ℝ) (hF : Measurable F)
    (hF0 : ∀ z, 0 ≤ F z) (C : ℝ) (_hC : 0 ≤ C)
    (hsectionInt : ∀ y, Integrable (fun x => F (x, y)) mu)
    (hsectionBound : ∀ y, ∫ x, F (x, y) ∂mu ≤ C) :
    Integrable F (mu.prod nu) ∧ ∫ z, F z ∂(mu.prod nu) ≤ C := by
  let G : Beta → ℝ := fun y => ∫ x, ‖F (x, y)‖ ∂mu
  have hGstrong : StronglyMeasurable G := by
    exact hF.norm.stronglyMeasurable.integral_prod_left'
  have hGnonneg : ∀ y, 0 ≤ G y := by
    intro y
    exact integral_nonneg fun x => norm_nonneg (F (x, y))
  have hGle : ∀ y, G y ≤ C := by
    intro y
    have hnorm : (fun x => ‖F (x, y)‖) = fun x => F (x, y) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 (x, y))]
    simpa only [G, hnorm] using hsectionBound y
  have hGint : Integrable G nu := by
    apply (integrable_const C).mono' hGstrong.aestronglyMeasurable
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (hGnonneg y)]
    exact hGle y
  have hFint : Integrable F (mu.prod nu) :=
    (integrable_prod_iff' hF.aestronglyMeasurable).2
      ⟨ae_of_all nu hsectionInt, hGint⟩
  refine ⟨hFint, ?_⟩
  rw [integral_prod_symm F hFint]
  calc
    (∫ y, ∫ x, F (x, y) ∂mu ∂nu) ≤ ∫ _y : Beta, C ∂nu :=
      integral_mono hFint.integral_prod_right (integrable_const C)
        hsectionBound
    _ = C := by simp

end CircularLawSection4
