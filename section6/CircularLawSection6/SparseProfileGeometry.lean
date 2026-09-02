import CircularLawSection6.ProfileMassLimits
import Mathlib.Algebra.Order.Floor.Semifield

/-! # Sparse-regime sampling geometry

These are consequences of `W → ∞`, `N → ∞`, and `W/N → 0`. They discharge
the geometric hypotheses of the actual profile quadrature limit theorems.
-/

open Filter Topology

namespace CircularLawSection6

theorem half_dimension_ratio_tendsto (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => ((N n / 2 : ℕ) : ℝ) / (N n : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (show 0 ≤ (1 / 2 : ℝ) by norm_num)).comp
    (tendsto_natCast_atTop_atTop.comp hN)
  have heq (n : ℕ) : ⌊(1 / 2 : ℝ) * (N n : ℝ)⌋₊ = N n / 2 := by
    rw [one_div, inv_mul_eq_div, Nat.floor_div_ofNat, Nat.floor_natCast]
  change Tendsto (fun n => (⌊(1 / 2 : ℝ) * (N n : ℝ)⌋₊ : ℝ) / (N n : ℝ))
    atTop (𝓝 (1 / 2 : ℝ)) at h
  simpa only [heq] using h

theorem dimension_over_bandwidth_tendsto (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n)
    (hsparse : Tendsto (fun n => W n / (N n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (N n : ℝ) / W n) atTop atTop := by
  have hpos : ∀ n, 0 < W n / (N n : ℝ) := fun n =>
    div_pos (hW n) (by exact_mod_cast NeZero.pos (N n))
  have h := tendsto_inv_nhdsGT_zero.comp
    (tendsto_nhdsWithin_iff.2 ⟨hsparse, Filter.Eventually.of_forall hpos⟩)
  change Tendsto (fun n => (W n / (N n : ℝ))⁻¹) atTop atTop at h
  simpa only [inv_div] using h

theorem sparse_centered_window_exhausts (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (W : ℕ → ℝ) (hW : ∀ n, 0 < W n)
    (hsparse : Tendsto (fun n => W n / (N n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => -((N n / 2 : ℕ) : ℝ) / W n) atTop atBot ∧
      Tendsto (fun n => (((N n + 1) / 2 : ℕ) : ℝ) / W n) atTop atTop := by
  have hhalf : Tendsto (fun n => ((N n / 2 : ℕ) : ℝ) / W n) atTop atTop := by
    have h := (half_dimension_ratio_tendsto N hN).pos_mul_atTop (by norm_num)
      (dimension_over_bandwidth_tendsto N W hW hsparse)
    convert h using 1
    funext n
    have hN0 : (N n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (N n)
    field_simp [hN0]
  constructor
  · have h := tendsto_neg_atTop_atBot.comp hhalf
    change Tendsto (fun n => -(((N n / 2 : ℕ) : ℝ) / W n)) atTop atBot at h
    simpa only [neg_div] using h
  · apply tendsto_atTop_mono _ hhalf
    intro n
    apply div_le_div_of_nonneg_right _ (hW n).le
    exact_mod_cast (show N n / 2 ≤ (N n + 1) / 2 by omega)

theorem sparse_floor_core_fits (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (W : ℕ → ℝ) (hW : ∀ n, 0 < W n)
    (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (N n : ℝ)) atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) :
    ∀ᶠ n in atTop, 2 * ⌊R * W n⌋₊ + 1 ≤ N n := by
  have hc := (NoncompactProfile.floor_radius_tendsto hWlim hR).mul hsparse
  have hi : Tendsto (fun n => (1 : ℝ) / (N n : ℝ)) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp hN).const_div_atTop 1
  have hcount : Tendsto (fun n => ((2 * ⌊R * W n⌋₊ + 1 : ℕ) : ℝ) / (N n : ℝ))
      atTop (𝓝 0) := by
    have h := (hc.const_mul 2).add hi
    simp only [mul_zero, add_zero] at h
    convert h using 1
    funext n
    have hN0 : (N n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (N n)
    push_cast
    field_simp [(hW n).ne', hN0]
  filter_upwards [hcount.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
  have hNpos : (0 : ℝ) < N n := by exact_mod_cast NeZero.pos (N n)
  have h := (div_lt_one hNpos).1 hn
  exact_mod_cast h.le

theorem NoncompactProfile.normalizer_tendsto_sparse (p : NoncompactProfile)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (N n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => p.normalizer (N n) (W n) / W n) atTop (𝓝 1) := by
  obtain ⟨hl, hr⟩ := sparse_centered_window_exhausts N hN W hW hsparse
  exact p.normalizer_tendsto_of_window_exhaustion N W hW hWlim hl hr

theorem NoncompactProfile.rawCoreMass_tendsto_sparse (p : NoncompactProfile)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (N n : ℝ)) atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n => p.rawCoreMass (N n) ⌊R * W n⌋₊ (W n) / W n) atTop
      (𝓝 (∫ x in -R..R, p.f x)) :=
  p.rawCoreMass_tendsto_of_scaled_radius N _ W hW hWlim
    (sparse_floor_core_fits N hN W hW hWlim hsparse hR) (NoncompactProfile.floor_radius_tendsto hWlim hR)

theorem NoncompactProfile.coreMass_tendsto_sparse (p : NoncompactProfile)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (N n : ℝ)) atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n => p.coreMass (N n) ⌊R * W n⌋₊ (W n)) atTop
      (𝓝 (∫ x in -R..R, p.f x)) := by
  have h := (p.rawCoreMass_tendsto_sparse N hN W hW hWlim hsparse hR).div
    (p.normalizer_tendsto_sparse N hN W hW hWlim hsparse) one_ne_zero
  have heq (n : ℕ) : (p.rawCoreMass (N n) ⌊R * W n⌋₊ (W n) / W n) /
      (p.normalizer (N n) (W n) / W n) = p.coreMass (N n) ⌊R * W n⌋₊ (W n) := by
    rw [div_div_div_cancel_right₀ (hW n).ne', p.coreMass_eq_ratio]
  change Tendsto (fun n => (p.rawCoreMass (N n) ⌊R * W n⌋₊ (W n) / W n) /
    (p.normalizer (N n) (W n) / W n)) atTop (𝓝 ((∫ x in -R..R, p.f x) / 1)) at h
  simpa only [heq, div_one] using h

theorem NoncompactProfile.tailMass_tendsto_sparse (p : NoncompactProfile)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (N n : ℝ)) atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n => p.tailMass (N n) ⌊R * W n⌋₊ (W n)) atTop
      (𝓝 (1 - ∫ x in -R..R, p.f x)) := by
  have heq (n : ℕ) : p.tailMass (N n) ⌊R * W n⌋₊ (W n) =
      1 - p.coreMass (N n) ⌊R * W n⌋₊ (W n) := by
    have h := p.coreMass_add_tailMass (N n) ⌊R * W n⌋₊ (W n)
    linarith
  simpa only [heq] using tendsto_const_nhds.sub
    (p.coreMass_tendsto_sparse N hN W hW hWlim hsparse hR)

theorem NoncompactProfile.limitingCoreMass_tendsto_one (p : NoncompactProfile) :
    Tendsto (fun R : ℕ => ∫ x in -(R : ℝ)..(R : ℝ), p.f x) atTop (𝓝 1) := by
  simpa only [Function.comp_apply, p.integral_one] using MeasureTheory.intervalIntegral_tendsto_integral p.integrable
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop

theorem NoncompactProfile.limitingTailMass_tendsto_zero (p : NoncompactProfile) :
    Tendsto (fun R : ℕ => 1 - ∫ x in -(R : ℝ)..(R : ℝ), p.f x) atTop (𝓝 0) := by
  simpa only [sub_self] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub p.limitingCoreMass_tendsto_one

end CircularLawSection6
