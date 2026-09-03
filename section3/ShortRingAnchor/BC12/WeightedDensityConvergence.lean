import ShortRingAnchor.BC12.GinibreDensityLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Weighted convergence of the explicit Ginibre densities

This proves the dominated-convergence part of BC12 Theorem 3.4 directly
from its finite one-point formula.  It applies to unbounded test functions
whenever the displayed Gaussian envelope is integrable.  In particular it
does not mistake weak convergence alone for logarithmic convergence.
-/

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

namespace ShortRingAnchor.BC12

/-- A dimension-independent envelope proved in `GinibreKernel`. -/
def ginibreEnvelope (w : ℂ) : ℝ := Real.exp (1 - ‖w‖ ^ 2 / 4) / Real.pi

/-- The open-disk density; the choice on the circle does not affect integrals. -/
def circularDensity (w : ℂ) : ℝ := if ‖w‖ < 1 then 1 / Real.pi else 0

/-- Measurability of the explicit finite correlation expression. -/
theorem measurable_ginibreOnePointDensity (n : ℕ) :
    Measurable (ginibreOnePointDensity n) := by
  unfold ginibreOnePointDensity poissonCutoff expPartialSum
  fun_prop

/-- A global envelope also covering dimension zero by its exact zero formula. -/
theorem ginibreOnePointDensity_le_envelope (n : ℕ) (w : ℂ) :
    ginibreOnePointDensity n w ≤ ginibreEnvelope w := by
  cases n with
  | zero =>
      simp only [ginibreOnePointDensity, poissonCutoff, expPartialSum,
        Finset.range_zero, Finset.sum_empty, mul_zero, zero_div]
      exact div_nonneg (Real.exp_pos _).le Real.pi_pos.le
  | succ n => exact ginibreOnePointDensity_le_gaussian (Nat.succ_pos n) w

/-- The excluded unit circle has planar Lebesgue measure zero; no geometric
or probabilistic hypothesis is required. -/
theorem norm_ne_one_ae_complex : ∀ᵐ w : ℂ, ‖w‖ ≠ 1 := by
  rw [ae_iff]
  simpa only [not_ne_iff, Metric.sphere, dist_zero_right] using
    (Measure.addHaar_sphere (volume : Measure ℂ) (0 : ℂ) 1)

/-- Weighted Gaussian integrability gives integrability against every
explicit finite Ginibre density. -/
theorem integrable_mul_ginibreOnePointDensity
    {f : ℂ → ℝ} (hf : Measurable f)
    (hint : Integrable (fun w => |f w| * ginibreEnvelope w)) (n : ℕ) :
    Integrable (fun w => f w * ginibreOnePointDensity n w) := by
  apply hint.mono' (hf.mul (measurable_ginibreOnePointDensity n)).aestronglyMeasurable
  exact .of_forall fun w => by
    change ‖f w * ginibreOnePointDensity n w‖ ≤ |f w| * ginibreEnvelope w
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ginibreOnePointDensity_nonneg n w)]
    exact mul_le_mul_of_nonneg_left (ginibreOnePointDensity_le_envelope n w) (abs_nonneg _)

/-- BC12's mean circular limit, now valid also for Gaussian-integrable
unbounded test functions.  The density convergence and domination are
proved, not supplied as assumptions. -/
theorem integral_mul_ginibreOnePointDensity_tendsto
    {f : ℂ → ℝ} (hf : Measurable f)
    (hint : Integrable (fun w => |f w| * ginibreEnvelope w)) :
    Tendsto (fun n : ℕ => ∫ w, f w * ginibreOnePointDensity n w) atTop
      (nhds (∫ w, f w * circularDensity w)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun w => |f w| * ginibreEnvelope w)
  · intro n
    exact (hf.mul (measurable_ginibreOnePointDensity n)).aestronglyMeasurable
  · exact hint
  · intro n
    exact .of_forall fun w => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ginibreOnePointDensity_nonneg n w)]
      exact mul_le_mul_of_nonneg_left (ginibreOnePointDensity_le_envelope n w) (abs_nonneg _)
  · filter_upwards [norm_ne_one_ae_complex] with w hw
    exact tendsto_const_nhds.mul (ginibreOnePointDensity_tendsto w hw)

/-- Uniform weighted second moments, used after the exact two-point formula. -/
theorem integral_sq_mul_ginibreOnePointDensity_le
    {f : ℂ → ℝ} (hf : Measurable f)
    (hint : Integrable (fun w => (f w) ^ 2 * ginibreEnvelope w)) (n : ℕ) :
    (∫ w, (f w) ^ 2 * ginibreOnePointDensity n w) ≤
      ∫ w, (f w) ^ 2 * ginibreEnvelope w := by
  have hfinite : Integrable (fun w => (f w) ^ 2 * ginibreOnePointDensity n w) :=
    integrable_mul_ginibreOnePointDensity (hf.pow_const 2)
      (by simpa only [abs_pow, sq_abs] using hint) n
  exact integral_mono hfinite hint (fun w =>
    mul_le_mul_of_nonneg_left (ginibreOnePointDensity_le_envelope n w) (sq_nonneg _))

end ShortRingAnchor.BC12
