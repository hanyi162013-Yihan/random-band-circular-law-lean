import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Polar integration as a radial integral of circle averages

An ordinary analytic change-of-variables lemma used to compute the circular
logarithmic potential; this is not a random-matrix input.
-/

open Filter Set MeasureTheory Real
open scoped Topology

noncomputable section

namespace ShortRingAnchor.BC12

/-- Integrability is transported through polar coordinates with its
Jacobian, so the subsequent use of Fubini does not use total integrals of
nonintegrable functions. -/
theorem integrable_polar_lift {f : ℂ → ℝ} (hf : Measurable f) (hint : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm p))
      polarCoord.target := by
  constructor
  · have hm : Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
      simp only [Complex.polarCoord_symm_apply]
      fun_prop
    exact (measurable_fst.mul (hf.comp hm)).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_norm]
    calc
      (∫⁻ p in polarCoord.target,
          ENNReal.ofReal ‖p.1 * f (Complex.polarCoord.symm p)‖) =
          ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 * ENNReal.ofReal ‖f (Complex.polarCoord.symm p)‖ := by
        apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp
        dsimp only
        rw [norm_mul, Real.norm_of_nonneg hp.1.le, ENNReal.ofReal_mul hp.1.le]
      _ = ∫⁻ w : ℂ, ENNReal.ofReal ‖f w‖ := by
        simpa only [smul_eq_mul] using
          Complex.lintegral_comp_polarCoord_symm (fun w : ℂ => ENNReal.ofReal ‖f w‖)
      _ < ⊤ := (hasFiniteIntegral_iff_norm f).mp hint.hasFiniteIntegral

/-- Angular integration over the polar chart agrees with the circle
average, although the chart uses angles `(-π,π)` and the average `(0,2π)`. -/
theorem angular_integral_eq_circleAverage (f : ℂ → ℝ) (r : ℝ) :
    (∫ theta in Ioo (-Real.pi) Real.pi,
      f (Complex.polarCoord.symm (r, theta))) =
        (2 * Real.pi) * circleAverage f 0 r := by
  have hav := circleAverage_eq_integral_add (f := f) (c := 0) (R := r) (-Real.pi)
  rw [intervalIntegral.integral_comp_add_right (fun theta => f (circleMap 0 r theta))] at hav
  have hend : 2 * Real.pi + -Real.pi = Real.pi := by ring
  rw [zero_add, hend, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo] at hav
  simp only [smul_eq_mul] at hav
  have hmap (theta : ℝ) : Complex.polarCoord.symm (r, theta) = circleMap 0 r theta := by
    simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  simp_rw [hmap]
  rw [hav]
  field_simp

/-- Planar Lebesgue integration as the radial integral of circle averages.
The integrability premise is established separately for the logarithm. -/
theorem integral_eq_radial_circleAverage {f : ℂ → ℝ}
    (hf : Measurable f) (hint : Integrable f) :
    (∫ w, f w) = ∫ r in Ioi (0 : ℝ),
      (2 * Real.pi * r) * circleAverage f 0 r := by
  have hp := integrable_polar_lift hf hint
  have hmeasure : (volume : Measure (ℝ × ℝ)).restrict polarCoord.target =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
    rw [Measure.prod_restrict]
    rfl
  unfold IntegrableOn at hp
  rw [hmeasure] at hp
  rw [← Complex.integral_comp_polarCoord_symm f]
  change (∫ p, p.1 * f (Complex.polarCoord.symm p)
    ∂(volume.restrict polarCoord.target)) = _
  rw [hmeasure]
  rw [← integral_integral (f := fun r theta => r * f (Complex.polarCoord.symm (r, theta))) hp]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only
  rw [integral_const_mul, angular_integral_eq_circleAverage]
  ring

end ShortRingAnchor.BC12
