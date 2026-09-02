import BernoulliSection8.MesoscopicScales
import BernoulliSection8.CookRates

/-! # The exact many-cell anchor satisfies the logarithmic bandwidth condition -/

open Filter
open scoped Topology

noncomputable section

namespace BernoulliSection8

theorem tendsto_log_anchorSize_div_width :
    Tendsto (fun W : ℕ => Real.log (anchorSize W) / (W : ℝ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun W : ℕ => Real.log 13 / (W : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, Function.comp_def, mul_zero] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (Real.log 13)
  have hl : Tendsto (fun W : ℕ => (101 / 100 : ℝ) * (Real.log W / (W : ℝ)))
      atTop (𝓝 0) := by
    simpa using (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul (101 / 100 : ℝ)
  apply squeeze_zero' _ _ (show Tendsto
    (fun W : ℕ => Real.log 13 / (W : ℝ) + (101 / 100 : ℝ) * (Real.log W / (W : ℝ)))
    atTop (𝓝 0) from by simpa using hi.add hl)
  · exact Filter.Eventually.of_forall fun W => div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with W hW
    have hp : (0 : ℝ) < anchorSize W := by exact_mod_cast anchorSize_pos hW
    have hbound := Real.log_le_log hp (anchorSize_le_thirteen_mul_rpow hW)
    rw [Real.log_mul (by norm_num : (13 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos (by exact_mod_cast hW) _).ne',
      Real.log_rpow (by exact_mod_cast hW : (0 : ℝ) < W)] at hbound
    have h := div_le_div_of_nonneg_right hbound (Nat.cast_nonneg W)
    simpa only [add_div, mul_div_assoc] using h

/-- The ambient site sequence used by the anchor pressure estimate has
exactly the anchor scalar dimension. -/
theorem tendsto_log_anchorSites_mul_width_div_width
    (W : ℕ → ℕ) (hW : Tendsto W atTop atTop) :
    Tendsto (fun n => Real.log ((anchorSites (W n) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0) := by
  simpa only [anchorSize, Nat.mul_comm, Function.comp_def] using
    tendsto_log_anchorSize_div_width.comp hW

end BernoulliSection8
