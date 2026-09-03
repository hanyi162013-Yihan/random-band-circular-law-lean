import ShortRingAnchor.BC12.WeightedDensityConvergence
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The logarithmic test function is admissible

This supplies the analytic step not justified by BC12's weak circular law:
both `|log |w-z||` and its square are integrable against the proved Gaussian
envelope.  The shift `z` is arbitrary and the dominating constant depends
on `z`.  No probability or exact-ensemble formula is assumed in this file.
-/

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

namespace ShortRingAnchor.BC12

/-- Near zero the polar-coordinate Jacobian cancels the logarithmic
singularity.  At infinity a cubic bound suffices. -/
theorem radial_log_sq_le {r : ℝ} (hr : 0 < r) :
    r * (Real.log r) ^ 2 ≤ 4 + r ^ 3 := by
  by_cases hsmall : r ≤ 1
  · have h := (Real.abs_log_mul_self_rpow_lt r (1 / 2) hr hsmall (by norm_num)).le
    have hs : (r ^ (1 / 2 : ℝ)) ^ 2 = r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      norm_num
    have hsquare := mul_self_le_mul_self (abs_nonneg _) h
    norm_num only at hsquare
    rw [← sq, sq_abs, mul_pow, hs] at hsquare
    nlinarith [pow_nonneg hr.le 3]
  · have hlog0 : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
    have hlog : Real.log r ≤ r := (Real.log_le_sub_one_of_pos hr).trans (by linarith)
    have hsq : (Real.log r) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
    have := mul_le_mul_of_nonneg_left hsq hr.le
    nlinarith

/-- Elementary Gaussian integrability in the complex plane, proved by
polar integration and the real Gaussian moment theorem. -/
theorem integrable_complex_gaussian {b : ℝ} (hb : 0 < b) :
    Integrable (fun w : ℂ => Real.exp (-b * ‖w‖ ^ 2)) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun r : ℝ => Real.exp (-b * r ^ 2))]
  simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul,
    Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_sq hb (s := 1) (by norm_num))

/-- Squared logarithms are Gaussian integrable in two real dimensions;
the polar Jacobian is essential here. -/
theorem integrable_log_sq_mul_complex_gaussian {b : ℝ} (hb : 0 < b) :
    Integrable (fun w : ℂ => (Real.log ‖w‖) ^ 2 * Real.exp (-b * ‖w‖ ^ 2)) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun r : ℝ => (Real.log r) ^ 2 * Real.exp (-b * r ^ 2))]
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul]
  have hbound : IntegrableOn (fun r : ℝ =>
      4 * Real.exp (-b * r ^ 2) + r ^ 3 * Real.exp (-b * r ^ 2)) (Ioi 0) := by
    exact ((integrable_exp_neg_mul_sq hb).const_mul 4).integrableOn.add
      (by simpa only [Real.rpow_natCast] using
        (integrableOn_rpow_mul_exp_neg_mul_sq hb (s := (3 : ℕ)) (by norm_num)))
  apply hbound.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hrpos : 0 < r := hr
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    r * ((Real.log r) ^ 2 * Real.exp (-b * r ^ 2)) =
        (r * (Real.log r) ^ 2) * Real.exp (-b * r ^ 2) := by ring
    _ ≤ (4 + r ^ 3) * Real.exp (-b * r ^ 2) :=
      mul_le_mul_of_nonneg_right (radial_log_sq_le hrpos) (Real.exp_pos _).le
    _ = _ := by ring

/-- Translating the envelope costs only a finite, shift-dependent constant. -/
theorem ginibreEnvelope_le_shifted_gaussian (w z : ℂ) :
    ginibreEnvelope w ≤
      (Real.exp (1 + ‖z‖ ^ 2 / 4) / Real.pi) *
        Real.exp (-(1 / 8 : ℝ) * ‖w - z‖ ^ 2) := by
  have htri := norm_sub_le w z
  have hsq : ‖w - z‖ ^ 2 ≤ 2 * ‖w‖ ^ 2 + 2 * ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖w‖ - ‖z‖), norm_nonneg (w - z), norm_nonneg w, norm_nonneg z]
  unfold ginibreEnvelope
  calc
    _ ≤ Real.exp ((1 + ‖z‖ ^ 2 / 4) + (-(1 / 8 : ℝ) * ‖w - z‖ ^ 2)) /
        Real.pi := by
      apply div_le_div_of_nonneg_right _ Real.pi_pos.le
      exact Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_add]; ring

/-- The already proved global envelope has a finite integral. -/
theorem integrable_ginibreEnvelope : Integrable ginibreEnvelope := by
  have h := (integrable_complex_gaussian (b := 1 / 4) (by norm_num)).const_mul
    (Real.exp 1 / Real.pi)
  convert h using 1
  funext w
  change Real.exp (1 - ‖w‖ ^ 2 / 4) / Real.pi =
    (Real.exp 1 / Real.pi) * Real.exp (-(1 / 4 : ℝ) * ‖w‖ ^ 2)
  rw [show 1 - ‖w‖ ^ 2 / 4 = 1 + (-(1 / 4 : ℝ) * ‖w‖ ^ 2) by ring,
    Real.exp_add]
  ring

/-- No restriction on `z`: the squared logarithmic test function satisfies
the exact analytic premise of the correlation-to-convergence theorem. -/
theorem integrable_log_sq_mul_ginibreEnvelope (z : ℂ) :
    Integrable (fun w : ℂ => (Real.log ‖w - z‖) ^ 2 * ginibreEnvelope w) := by
  have h := ((integrable_log_sq_mul_complex_gaussian (b := 1 / 8)
    (by norm_num)).comp_sub_right z).const_mul (Real.exp (1 + ‖z‖ ^ 2 / 4) / Real.pi)
  apply h.mono' (by unfold ginibreEnvelope; fun_prop)
  exact .of_forall fun w => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold ginibreEnvelope; positivity)]
    calc
      _ ≤ (Real.log ‖w - z‖) ^ 2 *
          ((Real.exp (1 + ‖z‖ ^ 2 / 4) / Real.pi) *
            Real.exp (-(1 / 8 : ℝ) * ‖w - z‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (ginibreEnvelope_le_shifted_gaussian w z) (sq_nonneg _)
      _ = _ := by ring

/-- Absolute logarithmic integrability follows from `|t| ≤ 1 + t²` and
the separately proved squared-logarithm estimate. -/
theorem integrable_abs_log_mul_ginibreEnvelope (z : ℂ) :
    Integrable (fun w : ℂ => |Real.log ‖w - z‖| * ginibreEnvelope w) := by
  apply (integrable_ginibreEnvelope.add (integrable_log_sq_mul_ginibreEnvelope z)).mono'
    (by apply Measurable.aestronglyMeasurable; unfold ginibreEnvelope; fun_prop)
  exact .of_forall fun w => by
    change ‖|Real.log ‖w - z‖| * ginibreEnvelope w‖ ≤
      ginibreEnvelope w + (Real.log ‖w - z‖) ^ 2 * ginibreEnvelope w
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold ginibreEnvelope; positivity)]
    have he : 0 ≤ ginibreEnvelope w := by unfold ginibreEnvelope; positivity
    have ht : |Real.log ‖w - z‖| ≤ 1 + (Real.log ‖w - z‖) ^ 2 := by
      nlinarith [sq_nonneg (|Real.log ‖w - z‖| - 1), sq_abs (Real.log ‖w - z‖)]
    calc
      _ ≤ (1 + (Real.log ‖w - z‖) ^ 2) * ginibreEnvelope w :=
        mul_le_mul_of_nonneg_right ht he
      _ = _ := by ring

end ShortRingAnchor.BC12
