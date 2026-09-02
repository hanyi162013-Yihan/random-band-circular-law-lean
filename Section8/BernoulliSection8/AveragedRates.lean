import BernoulliSection8.CookRates
import BernoulliSection8.MesoscopicScales
import BernoulliSection8.BandwidthLedger

/-! # Rates after averaging the capped resets -/

open Filter
open scoped Topology

noncomputable section

namespace BernoulliSection8

open BernoulliSection10

theorem tendsto_siteCount_exp_mul_logScale
    (m W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log ((m n * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n => (m n : ℝ) * Real.exp (-c * (W n : ℝ)) * densityLogScale (W n))
      atTop (𝓝 0) := by
  have h1 := tendsto_siteCount_mul_exp_neg_width m W hW hlog 1 (half_pos hc)
  have h2 := (tendsto_exp_neg_width_mul_logScale (half_pos hc)).comp hW
  have h := h1.mul h2
  simp only [one_mul, mul_zero] at h
  convert h using 1
  funext n
  dsimp only [Function.comp_def]
  rw [show -c * (W n : ℝ) = -(c / 2) * (W n : ℝ) +
    -(c / 2) * (W n : ℝ) by ring, Real.exp_add]
  ring

theorem tendsto_logScale_div_cellSites :
    Tendsto (fun W : ℕ => densityLogScale W / cellSites W) atTop (𝓝 0) := by
  apply squeeze_zero' _ _
    (tendsto_densityLogScale_div_rpow (by norm_num : (0 : ℝ) < 1 / 200))
  · filter_upwards [eventually_gt_atTop 0] with W hW
    exact div_nonneg (densityLogScale_nonneg hW) (Nat.cast_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with W hW
    exact div_le_div_of_nonneg_left (densityLogScale_nonneg hW)
      (Real.rpow_pos_of_pos (by exact_mod_cast hW) _) (rpow_le_cellSites W)

/-- The precise three kinds of errors in the mean reset budget: base
loss per core, the averaged Cook failure, and exceptional Nguyen fibers.
The number of cells does not multiply the Cook term. -/
def averagedResetError (base cap c : ℝ) (slow : ℕ → ℝ) (m W : ℕ) : ℝ :=
  base * (densityLogScale W / cellSites W) +
    cap * (slow W * densityLogScale W) +
    cap * ((9 + 3 * (m : ℝ)) * Real.exp (-c * (W : ℝ)) * densityLogScale W)

theorem tendsto_averagedResetError
    (base cap : ℝ) {c : ℝ} (hc : 0 < c) (slow : ℕ → ℝ)
    (hslow : Tendsto (fun W => slow W * densityLogScale W) atTop (𝓝 0))
    (m W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log ((m n * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => averagedResetError base cap c slow (m n) (W n)) atTop (𝓝 0) := by
  have hbase := (tendsto_logScale_div_cellSites.comp hW).const_mul base
  have hslow' := (hslow.comp hW).const_mul cap
  have he := ((tendsto_exp_neg_width_mul_logScale hc).comp hW).const_mul 9
  have hm := (tendsto_siteCount_exp_mul_logScale m W hW hlog hc).const_mul 3
  have h := (hbase.add hslow').add ((he.add hm).const_mul cap)
  simp only [mul_zero, zero_add] at h
  convert h using 1
  funext n
  dsimp [averagedResetError]
  ring

end BernoulliSection8
