import BernoulliSection10.AsymptoticErrors

/-! # The normalized anchor fluctuation scale in (10.34) -/

open Filter Topology

noncomputable section

namespace BernoulliSection10

theorem sqrt_width_times_length_div_dimension_le
    {w l N : ℝ} (hw : 0 ≤ w) (hN : 0 < N) (hl : l ≤ N) :
    Real.sqrt (w * l) / N ≤ Real.sqrt (w / N) := by
  rw [div_le_iff₀ hN]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [mul_pow, Real.sq_sqrt (div_nonneg hw hN.le)]
    calc
      w * l ≤ w * N := mul_le_mul_of_nonneg_left hl hw
      _ = w / N * N ^ 2 := by field_simp

theorem densitySqrtWidth_div_anchor_le {W : ℕ} (hW : 0 < W) :
    Real.sqrt ((W : ℝ) / densityAnchorSize W) ≤
      1 / (W : ℝ) ^ (1 / 400 : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hp : ((W : ℝ) ^ (1 / 400 : ℝ)) ^ 2 =
        (W : ℝ) ^ (1 / 200 : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg W)]
      norm_num
    rw [div_pow, one_pow, hp]
    exact densityWidth_div_anchor_le hW

theorem densityCore_fluctuation_div_anchor_le {W : ℕ} (hW : 0 < W) :
    Real.sqrt ((W : ℝ) * ((densityCoreSites W * W : ℕ) : ℝ)) /
      densityAnchorSize W ≤ 1 / (W : ℝ) ^ (1 / 400 : ℝ) := by
  apply (sqrt_width_times_length_div_dimension_le (Nat.cast_nonneg W)
    (Nat.cast_pos.mpr (densityAnchorSize_pos hW)) ?_).trans
      (densitySqrtWidth_div_anchor_le hW)
  exact_mod_cast Nat.mul_le_mul_right W (by simp [densityCellSites] :
    densityCoreSites W ≤ densityCellSites W)

theorem tendsto_densityAnchorSize : Tendsto densityAnchorSize atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_gt_atTop 0] with W hW
  unfold densityAnchorSize
  exact Nat.le_mul_of_pos_left W (densityCellSites_pos W)

theorem tendsto_densityAnchor_seam_scale :
    Tendsto (fun W : ℕ => (W : ℝ) * densityLogScale W / densityAnchorSize W)
      atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_
    (tendsto_densityLogScale_div_rpow (by norm_num : (0 : ℝ) < 1 / 200))
  · filter_upwards [eventually_gt_atTop 0] with W hW
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg W) (densityLogScale_nonneg hW))
      (Nat.cast_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with W hW
    have h := mul_le_mul_of_nonneg_right (densityWidth_div_anchor_le hW)
      (densityLogScale_nonneg hW)
    simpa only [div_mul_eq_mul_div, one_mul, mul_div_assoc] using h

theorem tendsto_densityAnchor_fluctuation_scale :
    Tendsto (fun W : ℕ =>
      Real.sqrt ((W : ℝ) * ((densityCoreSites W * W : ℕ) : ℝ)) * densityLogScale W /
        densityAnchorSize W) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_
    (tendsto_densityLogScale_div_rpow (by norm_num : (0 : ℝ) < 1 / 400))
  · filter_upwards [eventually_gt_atTop 0] with W hW
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (densityLogScale_nonneg hW))
      (Nat.cast_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with W hW
    have h := mul_le_mul_of_nonneg_right (densityCore_fluctuation_div_anchor_le hW)
      (densityLogScale_nonneg hW)
    simpa only [div_mul_eq_mul_div, one_mul, mul_div_assoc] using h

end BernoulliSection10
