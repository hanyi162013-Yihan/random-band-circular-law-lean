import BernoulliSection10Complex.CyclicStitchedPressure
import BernoulliSection10.AnchorScales

/-! # Vanishing of the complete normalized long-ring error -/

open Filter Topology

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

def densityGlobalErrorConstant (L : ℝ) (z : ℂ) : ℝ :=
  physicalSeamConstant L z + remainderHodgeConstant L z +
    densityCellMeanErrorConstant L z + densityConcentrationConstant L

theorem cyclicStitchedPressureError_nonneg
    (L : ℝ) (W K q : ℕ) (hW : 0 < W) (z : ℂ) :
    0 ≤ cyclicStitchedPressureError L W K q z := by
  have := physicalSeamConstant_nonneg L z
  have := remainderHodgeConstant_nonneg L z
  have := densityCellMeanErrorConstant_nonneg L z
  have := densityConcentrationConstant_nonneg L
  have := densityLogScale_nonneg hW
  unfold cyclicStitchedPressureError stitchedPressureErrorBound
  positivity

theorem cyclicStitchedPressureError_div_le
    (L : ℝ) (W K q N : ℕ) (hW : 0 < W) (z : ℂ)
    (hq : q ≤ densityCellSites W)
    (hsize : (K * densityCellSites W + q + 3) * W ≤ N) :
    cyclicStitchedPressureError L W K q z / N ≤
      densityGlobalErrorConstant L z * densityTargetErrorScale W N := by
  have hS := physicalSeamConstant_nonneg L z
  have hR := remainderHodgeConstant_nonneg L z
  have hM := densityCellMeanErrorConstant_nonneg L z
  have hD := densityConcentrationConstant_nonneg L
  have hlog := densityLogScale_nonneg hW
  have hNr : (0 : ℝ) < N := by
    exact_mod_cast (Nat.lt_of_lt_of_le (Nat.mul_pos (by omega) hW) hsize)
  have hell : (0 : ℝ) < densityAnchorSize W := Nat.cast_pos.mpr (densityAnchorSize_pos hW)
  have hKell : (K : ℝ) * densityAnchorSize W ≤ N := by
    have hk : K * densityCellSites W * W ≤ N :=
      (Nat.mul_le_mul_right W (by omega : K * densityCellSites W ≤
        K * densityCellSites W + q + 3)).trans hsize
    simpa only [densityAnchorSize, Nat.cast_mul, mul_assoc] using
      (show ((K * densityCellSites W * W : ℕ) : ℝ) ≤ N by exact_mod_cast hk)
  have hqell : (q : ℝ) * W ≤ densityAnchorSize W := by
    exact_mod_cast Nat.mul_le_mul_right W hq
  have hKratio : (K : ℝ) / N ≤ 1 / (densityAnchorSize W : ℝ) := by
    apply (div_le_div_iff₀ hNr hell).mpr
    simpa only [one_mul] using hKell
  have hmean : (K : ℝ) * (densityCellMeanErrorConstant L z * W * densityLogScale W) / N ≤
      densityCellMeanErrorConstant L z *
        ((W : ℝ) * densityLogScale W / densityAnchorSize W) := by
    have h := mul_le_mul_of_nonneg_right hKratio
      (mul_nonneg (mul_nonneg hM (Nat.cast_nonneg W)) hlog)
    calc
      (K : ℝ) * (densityCellMeanErrorConstant L z * W * densityLogScale W) / N =
          ((K : ℝ) / N) * (densityCellMeanErrorConstant L z * W * densityLogScale W) := by ring
      _ ≤ (1 / (densityAnchorSize W : ℝ)) *
          (densityCellMeanErrorConstant L z * W * densityLogScale W) := h
      _ = densityCellMeanErrorConstant L z *
          ((W : ℝ) * densityLogScale W / densityAnchorSize W) := by ring
  have hrem : (q : ℝ) * remainderHodgeConstant L z * W * densityLogScale W / N ≤
      remainderHodgeConstant L z *
        ((densityAnchorSize W : ℝ) * densityLogScale W / N) := by
    have h := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hqell hNr.le) (mul_nonneg hR hlog)
    calc
      (q : ℝ) * remainderHodgeConstant L z * W * densityLogScale W / N =
          ((q : ℝ) * W / N) * (remainderHodgeConstant L z * densityLogScale W) := by ring
      _ ≤ ((densityAnchorSize W : ℝ) / N) *
          (remainderHodgeConstant L z * densityLogScale W) := h
      _ = remainderHodgeConstant L z *
          ((densityAnchorSize W : ℝ) * densityLogScale W / N) := by ring
  have hlength : ((K * densityCellSites W * W : ℕ) : ℝ) ≤ N := by
    simpa only [densityAnchorSize, Nat.cast_mul, mul_assoc] using hKell
  have hconc : densityConcentrationConstant L *
      Real.sqrt ((W : ℝ) * ((K * densityCellSites W * W : ℕ) : ℝ)) * densityLogScale W / N ≤
      densityConcentrationConstant L * (Real.sqrt ((W : ℝ) / N) * densityLogScale W) := by
    have h := mul_le_mul_of_nonneg_right
      (sqrt_width_times_length_div_dimension_le (Nat.cast_nonneg W) hNr hlength)
      (mul_nonneg hD hlog)
    calc
      densityConcentrationConstant L *
          Real.sqrt ((W : ℝ) * ((K * densityCellSites W * W : ℕ) : ℝ)) * densityLogScale W / N =
        (Real.sqrt ((W : ℝ) * ((K * densityCellSites W * W : ℕ) : ℝ)) / N) *
          (densityConcentrationConstant L * densityLogScale W) := by ring
      _ ≤ Real.sqrt ((W : ℝ) / N) * (densityConcentrationConstant L * densityLogScale W) := h
      _ = densityConcentrationConstant L * (Real.sqrt ((W : ℝ) / N) * densityLogScale W) := by ring
  let A := (W : ℝ) * densityLogScale W / densityAnchorSize W
  let B := Real.sqrt ((W : ℝ) / N) * densityLogScale W
  let C := (densityAnchorSize W : ℝ) * densityLogScale W / N
  let D := (W : ℝ) * densityLogScale W / N
  let G := densityGlobalErrorConstant L z
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD' : 0 ≤ D := by dsimp [D]; positivity
  have hG : 0 ≤ G := by dsimp [G, densityGlobalErrorConstant]; positivity
  have hSG : physicalSeamConstant L z ≤ G := by dsimp [G, densityGlobalErrorConstant]; linarith
  have hRG : remainderHodgeConstant L z ≤ G := by dsimp [G, densityGlobalErrorConstant]; linarith
  have hMG : densityCellMeanErrorConstant L z ≤ G := by dsimp [G, densityGlobalErrorConstant]; linarith
  have hDG : densityConcentrationConstant L ≤ G := by dsimp [G, densityGlobalErrorConstant]; linarith
  have hmajor : cyclicStitchedPressureError L W K q z / N ≤
      physicalSeamConstant L z * D + remainderHodgeConstant L z * C +
        (densityCellMeanErrorConstant L z * A + densityConcentrationConstant L * B) := by
    unfold cyclicStitchedPressureError stitchedPressureErrorBound
    simp only [add_div]
    apply add_le_add
    · apply add_le_add
      · exact le_of_eq (by dsimp [D]; ring)
      · exact hrem
    · exact add_le_add hmean hconc
  have hweighted : physicalSeamConstant L z * D + remainderHodgeConstant L z * C +
      (densityCellMeanErrorConstant L z * A + densityConcentrationConstant L * B) ≤
        G * (A + B + C + D) := by
    nlinarith only [mul_le_mul_of_nonneg_right hSG hD',
      mul_le_mul_of_nonneg_right hRG hC, mul_le_mul_of_nonneg_right hMG hA,
      mul_le_mul_of_nonneg_right hDG hB]
  apply (hmajor.trans hweighted).trans
  apply mul_le_mul_of_nonneg_left _ hG
  change A + B + C + D ≤ A + B + C + D + densityLogScale W / (W : ℝ) ^ (1 / 400 : ℝ)
  exact le_add_of_nonneg_right (div_nonneg hlog (Real.rpow_nonneg (Nat.cast_nonneg W) _))

theorem tendsto_cyclicStitchedPressureError_div
    (L : ℝ) (z : ℂ) (W K q N : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hq : ∀ᶠ n in atTop, q n ≤ densityCellSites (W n))
    (hsize : ∀ᶠ n in atTop, (K n * densityCellSites (W n) + q n + 3) * W n ≤ N n)
    (hlong : ∀ᶠ n in atTop, (W n : ℝ) ^ (101 / 100 : ℝ) ≤ N n) :
    Tendsto (fun n => cyclicStitchedPressureError L (W n) (K n) (q n) z / N n)
      atTop (𝓝 0) := by
  have hpos := hW.eventually (eventually_gt_atTop 0)
  apply squeeze_zero' ?_ ?_
    (show Tendsto (fun n => densityGlobalErrorConstant L z * densityTargetErrorScale (W n) (N n))
      atTop (𝓝 0) from by
        simpa using (tendsto_densityTargetErrorScale hW hlong).const_mul (densityGlobalErrorConstant L z))
  · filter_upwards [hpos] with n hn
    exact div_nonneg (cyclicStitchedPressureError_nonneg L (W n) (K n) (q n) hn z)
      (Nat.cast_nonneg _)
  · filter_upwards [hpos, hq, hsize] with n hn hqn hsn
    exact cyclicStitchedPressureError_div_le L (W n) (K n) (q n) (N n) hn z hqn hsn

end BernoulliSection10Complex

