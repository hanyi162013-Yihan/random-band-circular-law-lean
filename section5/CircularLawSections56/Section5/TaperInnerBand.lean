import CircularLawSections56.Section5.TaperModelVariance
import CircularLawSections56.Section5.PaperMesoscopicScaleLimits

/-! # The literal inner half-band in the taper short-ring argument

The floor in `W' = W / 2`, its small-width exceptions, the variance constants,
the effective bandwidth, and the loss of half the exponent margin are explicit.
-/

open Filter MeasureTheory Topology
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000
set_option autoImplicit false

namespace CircularLawSections56.Section5

def taperInnerBandSlot (W : ℕ) (s : Fin (2 * (W / 2) + 1)) : Fin (2 * W + 1) :=
  ⟨W - W / 2 + s.val, by have := s.isLt; omega⟩

theorem taperInnerBandSlot_grid_bound (W : ℕ) (s : Fin (2 * (W / 2) + 1)) :
    |taperGrid W (taperInnerBandSlot W s)| ≤ 1 / 2 := by
  have hle : W / 2 ≤ W := Nat.div_le_self W 2
  have hs : (s.val : ℝ) ≤ 2 * (W / 2 : ℕ) := by
    exact_mod_cast (show s.val ≤ 2 * (W / 2) by omega)
  have hs0 : 0 ≤ (s.val : ℝ) := Nat.cast_nonneg _
  have hh : 2 * (W / 2 : ℕ) ≤ (W : ℝ) := by
    exact_mod_cast (show 2 * (W / 2) ≤ W by omega)
  rw [taperGrid, abs_div, abs_of_pos (by positivity : 0 < (W + 1 : ℝ))]
  apply (div_le_iff₀ (by positivity)).2
  change |((W - W / 2 + s.val : ℕ) : ℝ) - (W : ℝ)| ≤ 1 / 2 * (W + 1 : ℝ)
  rw [Nat.cast_add, Nat.cast_sub hle]
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem taper_half_width_comparison (W : ℕ) (hW : 2 ≤ W) :
    0 < W / 2 ∧ 2 * (W / 2) ≤ W ∧ W ≤ 3 * (W / 2) := by omega

theorem taper_half_width_tendsto (W : ℕ → ℕ) (hW : Tendsto W atTop atTop) :
    Tendsto (fun n => W n / 2) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [hW.eventually_ge_atTop (2 * b)] with n hn
  omega

namespace PolynomialTaperProfile

theorem varianceMatrix_inner_halfband_lower
    (p : PolynomialTaperProfile) (N W : ℕ) [NeZero N]
    (hW : 2 ≤ W) (hfit : 2 * W + 1 ≤ N)
    (i : ZMod N) (s : Fin (2 * (W / 2) + 1)) :
    (p.lowerWeightConstant / 3) / (W / 2 : ℕ) ≤
      p.varianceMatrix N W i (i - (W / 2 : ℕ) + (s.val : ZMod N)) := by
  have hWpos : 0 < W := by omega
  have hh := taper_half_width_comparison W hW
  have hWr : (W : ℝ) ≤ 3 * (W / 2 : ℕ) := by exact_mod_cast hh.2.2
  have hslot : i - (W : ZMod N) + ((taperInnerBandSlot W s).val : ZMod N) =
      i - (W / 2 : ℕ) + (s.val : ZMod N) := by
    change i - (W : ZMod N) + ((W - W / 2 + s.val : ℕ) : ZMod N) = _
    rw [Nat.cast_add, Nat.cast_sub (Nat.div_le_self W 2)]
    abel
  calc
    _ = p.lowerWeightConstant / (3 * (W / 2 : ℕ)) := by ring
    _ ≤ p.lowerWeightConstant / (W : ℝ) :=
      div_le_div_of_nonneg_left p.lowerWeightConstant_pos.le (Nat.cast_pos.2 hWpos) hWr
    _ ≤ p.varianceMatrix N W i (i - (W : ZMod N) + ((taperInnerBandSlot W s).val : ZMod N)) :=
      p.varianceMatrix_inner_lower N W hWpos hfit i _ (taperInnerBandSlot_grid_bound W s)
    _ = _ := congrArg (p.varianceMatrix N W i) hslot

theorem varianceMatrix_upper_halfband
    (p : PolynomialTaperProfile) (N W : ℕ) [NeZero N]
    (hW : 2 ≤ W) (hfit : 2 * W + 1 ≤ N) (i j : ZMod N) :
    p.varianceMatrix N W i j ≤ p.upperWeightConstant / (W / 2 : ℕ) := by
  apply (p.varianceMatrix_upper N W (by omega) hfit i j).trans
  apply div_le_div_of_nonneg_left p.upperWeightConstant_pos.le
    (Nat.cast_pos.2 (taper_half_width_comparison W hW).1)
  exact_mod_cast Nat.div_le_self W 2

def maxWeight (p : PolynomialTaperProfile) (W : ℕ) : ℝ :=
  finiteSignedMax Finset.univ Finset.univ_nonempty (p.weight W)

def effectiveBandwidth (p : PolynomialTaperProfile) (W : ℕ) : ℝ := (p.maxWeight W)⁻¹

theorem maxWeight_linear_bounds (p : PolynomialTaperProfile) (W : ℕ) (hW : 0 < W) :
    p.lowerWeightConstant / (W : ℝ) ≤ p.maxWeight W ∧
      p.maxWeight W ≤ p.upperWeightConstant / (W : ℝ) := by
  constructor
  · exact (p.weight_center_linear W hW).trans
      (le_finiteSignedMax Finset.univ_nonempty (p.weight W) (Finset.mem_univ _))
  · exact finiteSignedMax_le Finset.univ_nonempty (p.weight W)
      (fun i _ => p.weight_upper_linear W hW i)

theorem effectiveBandwidth_comparable (p : PolynomialTaperProfile) (W : ℕ) (hW : 0 < W) :
    (W : ℝ) / p.upperWeightConstant ≤ p.effectiveBandwidth W ∧
      p.effectiveBandwidth W ≤ (W : ℝ) / p.lowerWeightConstant := by
  have hb := p.maxWeight_linear_bounds W hW
  have hl : 0 < p.lowerWeightConstant / (W : ℝ) :=
    div_pos p.lowerWeightConstant_pos (Nat.cast_pos.2 hW)
  have hm : 0 < p.maxWeight W := hl.trans_le hb.1
  constructor
  · have h := one_div_le_one_div_of_le hm hb.2
    simpa only [one_div, inv_div, effectiveBandwidth] using h
  · have h := one_div_le_one_div_of_le hl hb.1
    simpa only [one_div, inv_div, effectiveBandwidth] using h

end PolynomialTaperProfile

theorem eventually_high_band_after_halving
    (M W : ℕ → ℕ) (βsmall βlarge : ℝ) (hβ : βsmall < βlarge)
    (hM : Tendsto M atTop atTop) (hW : Tendsto W atTop atTop)
    (hband : ∀ᶠ n in atTop, (M n : ℝ) ^ βlarge ≤ W n) :
    ∀ᶠ n in atTop, (M n : ℝ) ^ βsmall ≤ (W n / 2 : ℕ) := by
  have hMr : Tendsto (fun n => (M n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hM
  have hgap := ((tendsto_rpow_atTop (sub_pos.2 hβ)).comp hMr).eventually_ge_atTop 3
  filter_upwards [hgap, hband, hM.eventually_ge_atTop 1, hW.eventually_ge_atTop 2]
    with n hgapn hbandn hMn hWn
  change 3 ≤ (M n : ℝ) ^ (βlarge - βsmall) at hgapn
  have hm : 0 < (M n : ℝ) := Nat.cast_pos.2 (by omega)
  have hmul := mul_le_mul_of_nonneg_left hgapn (Real.rpow_nonneg hm.le βsmall)
  have he : (M n : ℝ) ^ βsmall * (M n : ℝ) ^ (βlarge - βsmall) =
      (M n : ℝ) ^ βlarge := by
    rw [← Real.rpow_add hm]
    congr 1
    ring
  have hhalf : (W n : ℝ) ≤ 3 * (W n / 2 : ℕ) := by
    exact_mod_cast (taper_half_width_comparison (W n) hWn).2.2
  rw [he] at hmul
  linarith

/-- The exact `ω` to `ω/2` exponent-margin reduction in the manuscript. -/
theorem eventually_taper_high_band_margin
    (M W : ℕ → ℕ) (ω : ℝ) (hω : 0 < ω)
    (hM : Tendsto M atTop atTop) (hW : Tendsto W atTop atTop)
    (hband : ∀ᶠ n in atTop, (M n : ℝ) ^ (8 / 9 + ω) ≤ W n) :
    ∀ᶠ n in atTop, (M n : ℝ) ^ (8 / 9 + ω / 2) ≤ (W n / 2 : ℕ) :=
  eventually_high_band_after_halving M W _ _ (by linarith) hM hW hband

end CircularLawSections56.Section5
