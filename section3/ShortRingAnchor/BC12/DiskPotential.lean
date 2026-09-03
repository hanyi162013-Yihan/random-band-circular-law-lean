import ShortRingAnchor.BC12.LogIntegrability
import ShortRingAnchor.BC12.PolarAverage
import ShortRingAnchor.SourceStatement
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# The explicit circular logarithmic potential

This verifies manuscript formula (2.1) for the limiting integral in the
Ginibre correlation argument.  Circle averages, polar integration, and a
one-dimensional substitution suffice; no potential formula is assumed.
-/

open Filter Set MeasureTheory Real
open scoped Topology

noncomputable section

namespace ShortRingAnchor.BC12

/-- The radial integrand after angular averaging. -/
def radialLogIntegrand (s r : ℝ) : ℝ :=
  if r ≤ s then r * Real.log s else r * Real.log r

/-- The two branches agree at the joining radius, including zero. -/
theorem continuous_radialLogIntegrand (s : ℝ) : Continuous (radialLogIntegrand s) := by
  unfold radialLogIntegrand
  apply Continuous.if_le (continuous_id.mul continuous_const)
    Real.continuous_mul_log continuous_id continuous_const
  intro r hr
  change r = s at hr
  change r * Real.log s = r * Real.log r
  rw [hr]

/-- Elementary primitive needed for the disk potential; the substitution
`u=r²` is valid at zero, so no logarithmic endpoint is discarded. -/
theorem integral_mul_log_from_zero {b : ℝ} (hb : 0 ≤ b) :
    (∫ r in (0 : ℝ)..b, r * Real.log r) =
      b ^ 2 * Real.log b / 2 - b ^ 2 / 4 := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := 0) (b := b) (f := fun r : ℝ => r ^ 2)
    (f' := fun r => 2 * r) (g := Real.log) (by fun_prop)
    (fun r _ => by
      simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hasDerivAt_pow 2 r)
    (fun r hr => by
      have hr0 : 0 < r := by simpa only [min_eq_left hb] using hr.1
      exact mul_nonneg (by norm_num) hr0.le)
  have hfun : (fun r : ℝ => (Real.log ∘ (fun r : ℝ => r ^ 2)) r * (2 * r)) =
      fun r => 4 * (r * Real.log r) := by
    funext r
    simp only [Function.comp_apply, Real.log_pow]
    ring
  rw [hfun, intervalIntegral.integral_const_mul, zero_pow (by norm_num : 2 ≠ 0),
    integral_log_from_zero, Real.log_pow] at h
  norm_num only at h
  nlinarith

/-- Angular averaging of the logarithmic kernel. -/
theorem circleAverage_log_norm_sub_eq_piecewise (z : ℂ) {r : ℝ} (hr : 0 < r) :
    circleAverage (fun w => Real.log ‖w - z‖) 0 r =
      if r ≤ ‖z‖ then Real.log ‖z‖ else Real.log r := by
  by_cases hsmall : r ≤ ‖z‖
  · rw [if_pos hsmall,
      circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne']
    simp only [zero_sub, norm_neg]
    have hs : 0 < ‖z‖ := hr.trans_le hsmall
    rw [Real.posLog_eq_log (by
      rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg _))]
      exact (one_le_inv_mul₀ hr).mpr hsmall), Real.log_mul (inv_ne_zero hr.ne') hs.ne',
      Real.log_inv]
    ring
  · rw [if_neg hsmall]
    apply circleAverage_log_norm_sub_const_of_mem_closedBall
    simpa only [Metric.mem_closedBall, dist_zero_right, abs_of_pos hr] using (le_of_not_ge hsmall)

/-- The elementary radial integral is the piecewise formula (2.1). -/
theorem integral_radialLogIntegrand (z : ℂ) :
    2 * (∫ r in (0 : ℝ)..1, radialLogIntegrand ‖z‖ r) = circularLogPotential z := by
  have hs := norm_nonneg z
  have hcont := continuous_radialLogIntegrand ‖z‖
  by_cases hinside : ‖z‖ ≤ 1
  · rw [circularLogPotential_of_norm_le hinside,
      ← intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable 0 ‖z‖) (hcont.intervalIntegrable ‖z‖ 1)]
    have hfirst : (∫ r in (0 : ℝ)..‖z‖, radialLogIntegrand ‖z‖ r) =
        Real.log ‖z‖ * ‖z‖ ^ 2 / 2 := by
      calc
        _ = ∫ r in (0 : ℝ)..‖z‖, r * Real.log ‖z‖ := by
          apply intervalIntegral.integral_congr
          intro r hr
          simp only [Set.uIcc_of_le hs, mem_Icc] at hr
          simp [radialLogIntegrand, hr.2]
        _ = _ := by rw [intervalIntegral.integral_mul_const, integral_id]; ring
    have hsecond : (∫ r in ‖z‖..1, radialLogIntegrand ‖z‖ r) =
        (-1 / 4 : ℝ) - (‖z‖ ^ 2 * Real.log ‖z‖ / 2 - ‖z‖ ^ 2 / 4) := by
      calc
        _ = ∫ r in ‖z‖..1, r * Real.log r := by
          apply intervalIntegral.integral_congr
          intro r hr
          simp only [Set.uIcc_of_le hinside, mem_Icc] at hr
          by_cases heq : r = ‖z‖
          · simp [radialLogIntegrand, heq]
          · simp [radialLogIntegrand, not_le.mpr (lt_of_le_of_ne hr.1 (Ne.symm heq))]
        _ = _ := by
          rw [← intervalIntegral.integral_interval_sub_left
            (Real.continuous_mul_log.intervalIntegrable 0 1)
            (Real.continuous_mul_log.intervalIntegrable 0 ‖z‖)]
          rw [integral_mul_log_from_zero zero_le_one, integral_mul_log_from_zero hs]
          norm_num
    rw [hfirst, hsecond]
    ring
  · rw [circularLogPotential_of_one_lt_norm (lt_of_not_ge hinside)]
    have hfirst : (∫ r in (0 : ℝ)..1, radialLogIntegrand ‖z‖ r) =
        Real.log ‖z‖ / 2 := by
      calc
        _ = ∫ r in (0 : ℝ)..1, r * Real.log ‖z‖ := by
          apply intervalIntegral.integral_congr
          intro r hr
          simp only [Set.uIcc_of_le zero_le_one, mem_Icc] at hr
          simp [radialLogIntegrand, hr.2.trans (le_of_not_ge hinside)]
        _ = _ := by rw [intervalIntegral.integral_mul_const, integral_id]; ring
    rw [hfirst]
    ring

/-- Measurability of the limiting open-disk density. -/
theorem measurable_circularDensity : Measurable circularDensity := by
  unfold circularDensity
  exact Measurable.ite (measurableSet_lt continuous_norm.measurable measurable_const)
    measurable_const measurable_const

/-- The limiting disk density is bounded by the same integrable envelope. -/
theorem circularDensity_le_envelope (w : ℂ) : circularDensity w ≤ ginibreEnvelope w := by
  unfold circularDensity ginibreEnvelope
  split_ifs with hw
  · apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    apply Real.one_le_exp_iff.mpr
    nlinarith [norm_nonneg w]
  · positivity

/-- Logarithmic integration over the limiting disk is an actual Bochner
integral, not a default value assigned to a divergent expression. -/
theorem integrable_log_mul_circularDensity (z : ℂ) :
    Integrable (fun w : ℂ => Real.log ‖w - z‖ * circularDensity w) := by
  apply (integrable_abs_log_mul_ginibreEnvelope z).mono'
    (by apply Measurable.aestronglyMeasurable
        exact (by fun_prop : Measurable (fun w : ℂ => Real.log ‖w - z‖)).mul
          measurable_circularDensity)
  exact .of_forall fun w => by
    change ‖Real.log ‖w - z‖ * circularDensity w‖ ≤
      |Real.log ‖w - z‖| * ginibreEnvelope w
    have hc : 0 ≤ circularDensity w := by unfold circularDensity; split_ifs <;> positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (circularDensity_le_envelope w) (abs_nonneg _)

/-- Formula (2.1), proved from polar integration and circle averages.  This
identifies the logarithmic limit for every fixed complex shift. -/
theorem integral_log_mul_circularDensity (z : ℂ) :
    (∫ w : ℂ, Real.log ‖w - z‖ * circularDensity w) = circularLogPotential z := by
  have hmeas : Measurable (fun w : ℂ => Real.log ‖w - z‖ * circularDensity w) :=
    (by fun_prop : Measurable (fun w : ℂ => Real.log ‖w - z‖)).mul measurable_circularDensity
  rw [integral_eq_radial_circleAverage hmeas (integrable_log_mul_circularDensity z)]
  have hangular (r : ℝ) (hr : 0 < r) :
      circleAverage (fun w : ℂ => Real.log ‖w - z‖ * circularDensity w) 0 r =
        (if r < 1 then 1 / Real.pi else 0) *
          circleAverage (fun w : ℂ => Real.log ‖w - z‖) 0 r := by
    change circleAverage (fun w : ℂ => Real.log ‖w - z‖ * circularDensity w) 0 r =
      ((if r < 1 then 1 / Real.pi else 0) : ℝ) •
        circleAverage (fun w : ℂ => Real.log ‖w - z‖) 0 r
    rw [← circleAverage_fun_smul]
    apply circleAverage_congr_sphere
    intro w hw
    have hn : ‖w‖ = r := by
      simpa only [Metric.mem_sphere, dist_zero_right, abs_of_pos hr] using hw
    simp only [smul_eq_mul, circularDensity, hn]
    ring
  calc
    (∫ r in Ioi (0 : ℝ), (2 * Real.pi * r) *
        circleAverage (fun w : ℂ => Real.log ‖w - z‖ * circularDensity w) 0 r) =
        ∫ r in Ioi (0 : ℝ), (Iio 1).indicator
          (fun r => 2 * radialLogIntegrand ‖z‖ r) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [hangular r hr, circleAverage_log_norm_sub_eq_piecewise z hr]
      by_cases hsmall : r < 1
      · simp only [Set.indicator, Set.mem_Iio, if_pos hsmall, radialLogIntegrand]
        split_ifs <;> field_simp
      · simp [hsmall]
    _ = ∫ r in Ioo (0 : ℝ) 1, 2 * radialLogIntegrand ‖z‖ r := by
      rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
      rw [show Iio (1 : ℝ) ∩ Ioi 0 = Ioo 0 1 by ext r; exact and_comm]
    _ = 2 * (∫ r in (0 : ℝ)..1, radialLogIntegrand ‖z‖ r) := by
      rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
        integral_Ioc_eq_integral_Ioo]
    _ = circularLogPotential z := integral_radialLogIntegrand z

end ShortRingAnchor.BC12
