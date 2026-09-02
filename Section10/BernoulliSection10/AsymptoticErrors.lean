import BernoulliSection10.AsymptoticScales

/-!
# Vanishing deterministic errors in Section 10

This module proves the long-branch scale comparisons directly from
`N ≥ W^(101/100)` and the ceiling-defined anchor size. These comparisons
are the deterministic part of (10.49) and (10.54); they do not assume
any probability estimate or log-determinant limit.
-/

open Filter
open scoped Topology

noncomputable section

namespace BernoulliSection10

theorem density_rpow_ratio {W : ℕ} (hW : 0 < W) (a b : ℝ) :
    (W : ℝ) ^ a / (W : ℝ) ^ (a + b) = 1 / (W : ℝ) ^ b := by
  have hWa : (W : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast hW) a).ne'
  rw [Real.rpow_add (by exact_mod_cast hW)]
  field_simp

theorem densityWidth_div_anchor_le {W : ℕ} (hW : 0 < W) :
    (W : ℝ) / densityAnchorSize W ≤ 1 / (W : ℝ) ^ (1 / 200 : ℝ) := by
  have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hW
  calc
    (W : ℝ) / densityAnchorSize W = 1 / (densityCellSites W : ℝ) := by
      rw [densityAnchorSize, Nat.cast_mul]
      field_simp
    _ ≤ 1 / (W : ℝ) ^ (1 / 200 : ℝ) :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hW) _)
        (rpow_le_densityCellSites W)

theorem densityAnchor_div_long_dimension_le {N W : ℕ} (hW : 0 < W)
    (hlong : (W : ℝ) ^ (101 / 100 : ℝ) ≤ N) :
    (densityAnchorSize W : ℝ) / N ≤ 5 / (W : ℝ) ^ (1 / 200 : ℝ) := by
  calc
    (densityAnchorSize W : ℝ) / N ≤
        (5 * (W : ℝ) ^ (201 / 200 : ℝ)) / (W : ℝ) ^ (101 / 100 : ℝ) :=
      div_le_div₀ (by positivity) (densityAnchorSize_le_five_mul_rpow hW)
        (Real.rpow_pos_of_pos (by exact_mod_cast hW) _) hlong
    _ = 5 / (W : ℝ) ^ (1 / 200 : ℝ) := by
      rw [show (101 / 100 : ℝ) = 201 / 200 + 1 / 200 by norm_num,
        mul_div_assoc, density_rpow_ratio hW]
      ring

theorem densityWidth_div_long_dimension_le {N W : ℕ} (hW : 0 < W)
    (hlong : (W : ℝ) ^ (101 / 100 : ℝ) ≤ N) :
    (W : ℝ) / N ≤ 1 / ((W : ℝ) ^ (1 / 200 : ℝ)) ^ 2 := by
  calc
    (W : ℝ) / N ≤ (W : ℝ) / (W : ℝ) ^ (101 / 100 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity)
        (Real.rpow_pos_of_pos (by exact_mod_cast hW) _) hlong
    _ = 1 / ((W : ℝ) ^ (1 / 200 : ℝ)) ^ 2 := by
      conv_lhs => lhs; rw [← Real.rpow_one (W : ℝ)]
      rw [show (101 / 100 : ℝ) = 1 + 1 / 100 by norm_num,
        density_rpow_ratio hW]
      congr 1
      rw [← Real.rpow_mul_natCast (by positivity)]
      norm_num

theorem densitySqrtWidth_div_long_dimension_le {N W : ℕ} (hW : 0 < W)
    (hlong : (W : ℝ) ^ (101 / 100 : ℝ) ≤ N) :
    Real.sqrt ((W : ℝ) / N) ≤ 1 / (W : ℝ) ^ (1 / 200 : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · simpa only [div_pow, one_pow] using densityWidth_div_long_dimension_le hW hlong

/-- The literal deterministic sum inside (10.54), without its unspecified
constant. Probability estimates multiplying this scale are separate. -/
def densityTargetErrorScale (W N : ℕ) : ℝ :=
  (W : ℝ) * densityLogScale W / densityAnchorSize W +
    Real.sqrt ((W : ℝ) / N) * densityLogScale W +
    (densityAnchorSize W : ℝ) * densityLogScale W / N +
    (W : ℝ) * densityLogScale W / N +
    densityLogScale W / (W : ℝ) ^ (1 / 400 : ℝ)

theorem densityTargetErrorScale_nonneg {W : ℕ} (hW : 0 < W) (N : ℕ) :
    0 ≤ densityTargetErrorScale W N := by
  have hlog := densityLogScale_nonneg hW
  unfold densityTargetErrorScale
  positivity

theorem densityTargetErrorScale_le {N W : ℕ} (hW : 0 < W)
    (hlong : (W : ℝ) ^ (101 / 100 : ℝ) ≤ N) :
    densityTargetErrorScale W N ≤
      8 * (densityLogScale W / (W : ℝ) ^ (1 / 200 : ℝ)) +
        densityLogScale W / (W : ℝ) ^ (1 / 400 : ℝ) := by
  have hlog := densityLogScale_nonneg hW
  have h1 := mul_le_mul_of_nonneg_right (densityWidth_div_anchor_le hW) hlog
  have h2 := mul_le_mul_of_nonneg_right (densitySqrtWidth_div_long_dimension_le hW hlong) hlog
  have h3 := mul_le_mul_of_nonneg_right (densityAnchor_div_long_dimension_le hW hlong) hlog
  have hp : 1 ≤ (W : ℝ) ^ (1 / 200 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hW) (by norm_num)
  have hw : (W : ℝ) / N ≤ 1 / (W : ℝ) ^ (1 / 200 : ℝ) := by
    apply (densityWidth_div_long_dimension_le hW hlong).trans
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h4 := mul_le_mul_of_nonneg_right hw hlog
  dsimp [densityTargetErrorScale]
  simp only [div_mul_eq_mul_div, one_mul, mul_div_assoc] at h1 h2 h3 h4 ⊢
  linarith

/-- Every normalized deterministic error in the long branch vanishes for
an arbitrary bandwidth sequence tending to infinity. -/
theorem tendsto_densityTargetErrorScale {W N : ℕ → ℕ}
    (hW : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, (W n : ℝ) ^ (101 / 100 : ℝ) ≤ N n) :
    Tendsto (fun n => densityTargetErrorScale (W n) (N n)) atTop (𝓝 0) := by
  have hpos : ∀ᶠ n in atTop, 0 < W n := hW.eventually (eventually_gt_atTop 0)
  have hlim1 := (tendsto_densityLogScale_div_rpow (by norm_num : (0 : ℝ) < 1 / 200)).comp hW
  have hlim2 := (tendsto_densityLogScale_div_rpow (by norm_num : (0 : ℝ) < 1 / 400)).comp hW
  apply squeeze_zero' (hpos.mono fun n hn => densityTargetErrorScale_nonneg hn (N n))
    (Filter.Eventually.and hpos hlong |>.mono fun _ hn => densityTargetErrorScale_le hn.1 hn.2)
  simpa using (hlim1.const_mul 8).add hlim2

/-- The scalar upper bound in the remainder Markov estimate, (10.48)--(10.49). -/
theorem tendsto_densityRemainderErrorScale {W N : ℕ → ℕ}
    (hW : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, (W n : ℝ) ^ (101 / 100 : ℝ) ≤ N n) :
    Tendsto (fun n => (densityAnchorSize (W n) : ℝ) * densityLogScale (W n) / N n)
      atTop (𝓝 0) := by
  have hpos : ∀ᶠ n in atTop, 0 < W n := hW.eventually (eventually_gt_atTop 0)
  apply squeeze_zero' (hpos.mono fun n hn => by
      exact div_nonneg (mul_nonneg (by positivity) (densityLogScale_nonneg hn)) (by positivity))
    (Filter.Eventually.and hpos hlong |>.mono fun n hn => ?_)
    (show Tendsto (fun n => 5 * (densityLogScale (W n) / (W n : ℝ) ^ (1 / 200 : ℝ)))
      atTop (𝓝 0) from by
        simpa using ((tendsto_densityLogScale_div_rpow
          (by norm_num : (0 : ℝ) < 1 / 200)).comp hW).const_mul 5)
  have h := mul_le_mul_of_nonneg_right (densityAnchor_div_long_dimension_le hn.1 hn.2)
    (densityLogScale_nonneg hn.1)
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using h

end BernoulliSection10
