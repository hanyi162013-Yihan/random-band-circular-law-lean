import CircularLawSections56.Section5.UniformLogarithmicWeights
import CircularLawSection4.PaperPressureRealConcentration

/-! # Section 4's explicit constants for polynomial endpoint weights

These estimates justify using the same finite Section 4 results for taper
profiles. Their constants depend on the fixed logarithmic weight exponent,
the density bound, and z, but not on the bandwidth. No uniform-in-size Section 4
constant for the taper is silently postulated.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1200000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

def logarithmicFiberConstant (A B : ℝ) (z : ℂ) : ℝ :=
  8 * (Real.log (max 1 B) + A + 4) ^ 2 + 2 * (3 * ‖z‖ + 3) ^ 2

theorem logarithmicFiberConstant_nonneg (A B : ℝ) (z : ℂ) :
    0 ≤ logarithmicFiberConstant A B z := by
  unfold logarithmicFiberConstant
  positivity

theorem fiberScaleLog_le_logarithmic
    (d : ℕ) (c₀ A B : ℝ) (hc₀ : 0 < c₀) (hA : 0 ≤ A)
    (hc : |Real.log c₀| ≤ A * dimensionLogScale d) :
    Real.log (max 1 (B / ((1 / 2 : ℝ) * Real.sqrt (c₀ / (d + 2 : ℝ))))) ≤
      (Real.log (max 1 B) + A + 3) * dimensionLogScale d := by
  have hs : 0 < Real.sqrt (c₀ / (d + 2 : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hH := one_le_dimensionLogScale d
  have ht : Real.log (d + 2 : ℝ) ≤ dimensionLogScale d := by
    unfold dimensionLogScale
    linarith
  have hB : 0 ≤ Real.log (max 1 B) := Real.log_nonneg (le_max_left _ _)
  have hweight := negative_log_profile_sqrt_le d c₀ hc₀
  have hw : -Real.log (Real.sqrt (c₀ / (d + 2 : ℝ))) ≤
      (A + 1) * dimensionLogScale d / 2 := by linarith
  calc
    _ ≤ Real.log (max 1 ((max 1 B) /
        ((1 / 2 : ℝ) * Real.sqrt (c₀ / (d + 2 : ℝ))))) := by
      apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      exact max_le_max le_rfl (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))
    _ ≤ _ := by
      rw [← Real.posLog_eq_log_max_one (by positivity), Real.posLog]
      apply max_le
      · positivity
      · rw [Real.log_div (by positivity) (by positivity),
          Real.log_mul (by norm_num) hs.ne', Real.log_div (by norm_num) (by norm_num),
          Real.log_one]
        have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
          linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
        nlinarith [mul_nonneg hB (sub_nonneg.2 hH),
          mul_nonneg hA (zero_le_one.trans hH)]

theorem logarithmic_fiber_second_moment_bound
    (d : ℕ) (c₀ A B : ℝ) (z : ℂ) (hc₀ : 0 < c₀) (hA : 0 ≤ A)
    (hc : |Real.log c₀| ≤ A * dimensionLogScale d) :
    2 * oneSidedLogSecondMomentBound
        (B / ((1 / 2 : ℝ) * Real.sqrt (c₀ / (d + 2 : ℝ)))) 1 +
      2 * (3 * Real.log (d + 2 : ℝ) ^ 2 + 3 + 3 * ‖z‖ ^ 2) ≤
      logarithmicFiberConstant A B z * dimensionLogScale d ^ 2 := by
  have hH := one_le_dimensionLogScale d
  have hn := fiberScaleLog_le_logarithmic d c₀ A B hc₀ hA hc
  have hn0 : 0 ≤ Real.log (max 1
      (B / ((1 / 2 : ℝ) * Real.sqrt (c₀ / (d + 2 : ℝ))))) :=
    Real.log_nonneg (le_max_left _ _)
  have hn1 : Real.log (max 1
      (B / ((1 / 2 : ℝ) * Real.sqrt (c₀ / (d + 2 : ℝ))))) + 1 ≤
      (Real.log (max 1 B) + A + 4) * dimensionLogScale d := by
    nlinarith only [hn, hH]
  have hnsq := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log (max 1
      (B / ((1 / 2 : ℝ) * Real.sqrt (c₀ / (d + 2 : ℝ))))) + 1) hn1 2
  have hpsq := pow_le_pow_left₀ (Real.sqrt_nonneg _)
    (freshRow_sqrt_moment_le_uniform d z) 2
  rw [Real.sq_sqrt (by positivity)] at hpsq
  dsimp only [oneSidedLogSecondMomentBound, logarithmicFiberConstant]
  simp only [div_one]
  nlinarith only [hnsq, hpsq]

theorem complexPaperPressureFiberL2Bound_le_logarithmic
    (d : ℕ) (c₀ A L : ℝ) (z : ℂ) (hc₀ : 0 < c₀) (hA : 0 ≤ A)
    (hc : |Real.log c₀| ≤ A * dimensionLogScale d) :
    complexPaperPressureFiberL2Bound d c₀ L z ≤
      logarithmicFiberConstant A (max 1 (Real.pi * L)) z * dimensionLogScale d ^ 2 := by
  simpa only [complexPaperPressureFiberL2Bound, mul_one] using
    logarithmic_fiber_second_moment_bound d c₀ A (max 1 (Real.pi * L)) z hc₀ hA hc

theorem realPaperPressureFiberL2Bound_le_logarithmic
    (d : ℕ) (c₀ A L : ℝ) (z : ℂ) (hc₀ : 0 < c₀) (hA : 0 ≤ A)
    (hc : |Real.log c₀| ≤ A * dimensionLogScale d) :
    realPaperPressureFiberL2Bound d c₀ L z (1 / 2) ≤
      logarithmicFiberConstant A (4 * L) z * dimensionLogScale d ^ 2 :=
  logarithmic_fiber_second_moment_bound d c₀ A (4 * L) z hc₀ hA hc

theorem logarithmic_raw_seam_bound
    (d W : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    (c₀ A J negative : ℝ) (z : ℂ) (hc₀ : 0 < c₀) (hA : 0 ≤ A) (hJ : 0 ≤ J)
    (hc : |Real.log c₀| ≤ A * dimensionLogScale d)
    (hnegative : negative ≤ J * (d + 1 : ℝ) * dimensionLogScale d) :
    paperIsolatedCoefficientLoss d c₀ + negative + paperFreshPositiveBound d z ≤
      (6 * (A + 4 + J + uniformFreshPositiveConstant z)) *
        ((W : ℝ) * Real.log (Real.exp 1 * (W : ℝ))) := by
  let C := A + 4 + J + uniformFreshPositiveConstant z
  have hC : 0 ≤ C := by unfold C uniformFreshPositiveConstant; positivity
  have hsum := add_le_add (add_le_add
    (paperIsolatedCoefficientLoss_le_logarithmic d c₀ A hc₀ hA hc) hnegative)
    (paperFreshPositiveBound_le_uniform d z)
  have hraw : paperIsolatedCoefficientLoss d c₀ + negative + paperFreshPositiveBound d z ≤
      C * (d + 1 : ℝ) * dimensionLogScale d := by
    simpa only [C, add_mul] using hsum
  have hlog := mul_le_mul_of_nonneg_left (dimensionLogScale_le_logEW d W hW hd)
    (mul_nonneg hC (show (0 : ℝ) ≤ d + 1 by positivity))
  have hd' : (d : ℝ) + 1 = 2 * (W : ℝ) := by exact_mod_cast hd
  rw [hd'] at hlog
  apply hraw.trans
  rw [hd']
  nlinarith only [hlog]

theorem logarithmic_pressure_fluctuation_bound
    (d W ell scale : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W) (hell : ell ≤ scale)
    (B V : ℝ) (hV : 0 ≤ V) (hB : B ≤ V * dimensionLogScale d ^ 2) :
    Real.sqrt ((d + 2 : ℝ) * 2 * (ell : ℝ) * B) ≤
      Real.sqrt (54 * V) * Real.sqrt ((W : ℝ) * (scale : ℝ)) *
        Real.log (Real.exp 1 * (W : ℝ)) := by
  let H := Real.log (Real.exp 1 * (W : ℝ))
  have hscale := dimensionLogScale_le_logEW d W hW hd
  have hH : 0 ≤ H := by linarith [one_le_dimensionLogScale d]
  have hd' : (d : ℝ) + 1 = 2 * (W : ℝ) := by exact_mod_cast hd
  have hw : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hdim : (d + 2 : ℝ) * 2 ≤ 6 * (W : ℝ) := by linarith
  have hlength := mul_le_mul hdim (Nat.cast_le.2 hell) (Nat.cast_nonneg ell)
    (show (0 : ℝ) ≤ 6 * (W : ℝ) by positivity)
  have hsq := pow_le_pow_left₀ (zero_le_one.trans (one_le_dimensionLogScale d)) hscale 2
  have hfiber : B ≤ 9 * V * H ^ 2 := by
    have hv := mul_le_mul_of_nonneg_left hsq hV
    nlinarith only [hB, hv]
  have hraw : (d + 2 : ℝ) * 2 * (ell : ℝ) * B ≤
      (54 * V) * ((W : ℝ) * (scale : ℝ)) * H ^ 2 := by
    calc
      _ ≤ ((d + 2 : ℝ) * 2 * (ell : ℝ)) * (9 * V * H ^ 2) :=
        mul_le_mul_of_nonneg_left hfiber (by positivity)
      _ ≤ (6 * (W : ℝ) * (scale : ℝ)) * (9 * V * H ^ 2) :=
        mul_le_mul_of_nonneg_right hlength (by positivity)
      _ = _ := by ring
  apply (Real.sqrt_le_sqrt hraw).trans_eq
  rw [Real.sqrt_mul (by positivity : 0 ≤ (54 * V) * ((W : ℝ) * (scale : ℝ))),
    Real.sqrt_mul (by positivity : 0 ≤ 54 * V), Real.sqrt_sq hH]

end CircularLawSections56.Section5
