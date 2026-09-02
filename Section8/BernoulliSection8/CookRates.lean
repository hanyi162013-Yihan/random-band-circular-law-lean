import BernoulliSection9.TerminalUniformCook
import BernoulliSection10.AsymptoticScales

/-!
# Averaged Cook errors tend to zero

The slow Cook failure is multiplied by the logarithmic height per site,
not by the number of cells. These scalar limits justify that operation
for the exact floor-safe Cook bound used in Section 9.
-/

open Filter
open scoped Topology

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10

theorem tendsto_log_mul_width_div_rpow {b a : ℝ} (hb : 0 < b) (ha : 0 < a) :
    Tendsto (fun W : ℕ => Real.log (b * W) / (W : ℝ) ^ a) atTop (𝓝 0) := by
  have hi : Tendsto (fun W : ℕ => ((W : ℝ) ^ a)⁻¹) atTop (𝓝 0) :=
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hl := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop
  have h := (hi.const_mul (Real.log b)).add hl
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with W hW
  rw [Real.log_mul hb.ne' (by exact_mod_cast hW.ne'), add_div]
  simp only [div_eq_mul_inv, Function.comp_def]

theorem width_third_power_cubed (W : ℕ) :
    ((W : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = W := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg W)]
  norm_num

theorem tendsto_cookRadicand_mul_logScale_sq :
    Tendsto (fun W : ℕ => (9 * Real.log (3 * (W : ℝ)) / W) *
      densityLogScale W ^ 2) atTop (𝓝 0) := by
  have h1 := tendsto_log_mul_width_div_rpow (by norm_num : (0 : ℝ) < 3)
    (by norm_num : (0 : ℝ) < 1 / 3)
  have h2 := tendsto_densityLogScale_div_rpow (by norm_num : (0 : ℝ) < 1 / 3)
  have h := ((h1.mul h2).mul h2).const_mul 9
  simp only [zero_mul, mul_zero] at h
  apply h.congr'
  filter_upwards with W
  change 9 * ((Real.log (3 * (W : ℝ)) / (W : ℝ) ^ (1 / 3 : ℝ) *
    (densityLogScale W / (W : ℝ) ^ (1 / 3 : ℝ))) *
    (densityLogScale W / (W : ℝ) ^ (1 / 3 : ℝ))) = _
  rw [div_mul_div_comm, div_mul_div_comm]
  rw [show (W : ℝ) ^ (1 / 3 : ℝ) * (W : ℝ) ^ (1 / 3 : ℝ) *
    (W : ℝ) ^ (1 / 3 : ℝ) = W by
      simpa only [pow_succ, pow_zero, one_mul] using width_third_power_cubed W]
  ring

theorem tendsto_cookSqrt_mul_logScale :
    Tendsto (fun W : ℕ => Real.sqrt (9 * Real.log (3 * (W : ℝ)) / W) *
      densityLogScale W) atTop (𝓝 0) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    tendsto_cookRadicand_mul_logScale_sq
  simp only [Real.sqrt_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with W hW
  dsimp only [Function.comp_def]
  rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (densityLogScale_nonneg hW)]

theorem tendsto_exp_neg_width_mul_logScale {c : ℝ} (hc : 0 < c) :
    Tendsto (fun W : ℕ => Real.exp (-c * W) * densityLogScale W)
      atTop (𝓝 0) := by
  have he := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc).comp
    tendsto_natCast_atTop_atTop
  have hl := tendsto_densityLogScale_div_rpow (by norm_num : (0 : ℝ) < 1)
  simp only [Real.rpow_one] at he hl
  have h := he.mul hl
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with W hW
  have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  dsimp
  field_simp

/-- This is the numerical limit needed after averaging the capped reset
losses. It holds for every Cook constant and positive exponential rate. -/
theorem tendsto_uniformCookFailureBound_mul_logScale (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun W : ℕ => uniformCookFailureBound C c W * densityLogScale W)
      atTop (𝓝 0) := by
  have h1 := tendsto_cookSqrt_mul_logScale.const_mul C
  have h2 := tendsto_exp_neg_width_mul_logScale (by positivity : 0 < c / 4)
  have h := h1.add h2
  simp only [mul_zero, zero_add] at h
  convert h using 1
  funext W
  dsimp [uniformCookFailureBound]
  rw [show -(c / 4) * (W : ℝ) = -c * W / 4 by ring]
  ring

end BernoulliSection8
