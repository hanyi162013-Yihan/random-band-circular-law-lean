import BernoulliSection10.AsymptoticErrors

/-! # The occupied-cell dimension ratio in (10.52) -/

open Filter Topology

noncomputable section

namespace BernoulliSection10

theorem densityCell_dimension_defect_bounds
    {m W : ℕ} (hm : 3 ≤ m) (hW : 0 < W) :
    0 ≤ 1 - (densityCellCount m W : ℝ) * densityAnchorSize W / ((m : ℝ) * W) ∧
      1 - (densityCellCount m W : ℝ) * densityAnchorSize W / ((m : ℝ) * W) ≤
        2 * ((densityAnchorSize W : ℝ) / ((m : ℝ) * W)) := by
  rw [densityCell_dimension_ratio hm hW]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hWpos : (0 : ℝ) < W := Nat.cast_pos.mpr hW
  have hq : 3 + densityRemainderSites m W ≤ 2 * densityCellSites W := by
    have hq := densityRemainderSites_lt m W
    have hc : 3 ≤ densityCellSites W := by simp [densityCellSites]
    omega
  constructor
  · have : 0 ≤ (3 + (densityRemainderSites m W : ℝ)) / m := by positivity
    linarith only [this]
  · have hcancel : (densityAnchorSize W : ℝ) / ((m : ℝ) * W) =
        (densityCellSites W : ℝ) / m := by
      simp only [densityAnchorSize, Nat.cast_mul]
      field_simp
    rw [hcancel]
    have hqr : (3 : ℝ) + densityRemainderSites m W ≤ 2 * densityCellSites W := by
      exact_mod_cast hq
    have h := div_le_div_of_nonneg_right hqr hmpos.le
    rw [mul_div_assoc] at h
    linarith only [h]

/-- The complete cells occupy asymptotically all target scalar dimensions.
This is the final limit in (10.52), with literal floor/modulus choices. -/
theorem tendsto_densityCell_dimension_ratio
    {W m : ℕ → ℕ} (hW : Tendsto W atTop atTop)
    (hm : ∀ᶠ n in atTop, 3 ≤ m n)
    (hlong : ∀ᶠ n in atTop, (W n : ℝ) ^ (101 / 100 : ℝ) ≤ m n * W n) :
    Tendsto (fun n => (densityCellCount (m n) (W n) : ℝ) * densityAnchorSize (W n) /
      ((m n : ℝ) * W n)) atTop (𝓝 1) := by
  have hpos : ∀ᶠ n in atTop, 0 < W n := hW.eventually (eventually_gt_atTop 0)
  have hinv : Tendsto (fun n => 1 / (W n : ℝ) ^ (1 / 200 : ℝ)) atTop (𝓝 0) := by
    have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp
      (tendsto_natCast_atTop_atTop.comp hW)
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hp
  have hdefect : Tendsto (fun n => 1 -
      (densityCellCount (m n) (W n) : ℝ) * densityAnchorSize (W n) /
        ((m n : ℝ) * W n)) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_
      (show Tendsto (fun n => 10 * (1 / (W n : ℝ) ^ (1 / 200 : ℝ)))
        atTop (𝓝 0) from by simpa using hinv.const_mul 10)
    · filter_upwards [hm, hpos] with n hmn hWn
      exact (densityCell_dimension_defect_bounds hmn hWn).1
    · filter_upwards [hm, hpos, hlong] with n hmn hWn hln
      have hl : (W n : ℝ) ^ (101 / 100 : ℝ) ≤ ((m n * W n : ℕ) : ℝ) := by
        simpa only [Nat.cast_mul] using hln
      have h := densityAnchor_div_long_dimension_le hWn hl
      simp only [Nat.cast_mul] at h
      have hh := (densityCell_dimension_defect_bounds hmn hWn).2
      calc
        _ ≤ 2 * ((densityAnchorSize (W n) : ℝ) / ((m n : ℝ) * W n)) := hh
        _ ≤ 2 * (5 / (W n : ℝ) ^ (1 / 200 : ℝ)) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
        _ = 10 * (1 / (W n : ℝ) ^ (1 / 200 : ℝ)) := by ring
  have h := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hdefect
  simpa only [sub_sub_cancel, sub_zero] using h

end BernoulliSection10
