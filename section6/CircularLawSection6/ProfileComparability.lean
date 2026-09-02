import CircularLawSection6.CenteredMesh
import Mathlib.Topology.Order.Compact

/-! # Concrete profile bounds on compact sampling windows

Continuity and strict positivity produce fixed bounds on each compact
window. Finite normalization then gives comparable variance weights.
-/

open Set
open scoped BigOperators

noncomputable section

namespace CircularLawSection6.NoncompactProfile

theorem compact_bounds (p : NoncompactProfile) {R : ℝ} (hR : 0 ≤ R) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ x, |x| ≤ R → m ≤ p.f x ∧ p.f x ≤ M := by
  obtain ⟨m, hm, hml⟩ := isCompact_Icc.exists_forall_le'
    (s := Icc (-R) R) (f := p.f) p.continuous.continuousOn (fun x _ => p.positive x)
  obtain ⟨y, _, hmy⟩ := isCompact_Icc.exists_isMaxOn
    (s := Icc (-R) R) ⟨0, by simpa using hR⟩ p.continuous.continuousOn
  refine ⟨m, p.f y, hm, p.positive y, ?_⟩
  intro x hx
  exact ⟨hml x (abs_le.1 hx), hmy (abs_le.1 hx)⟩

theorem raw_bounds_of_window (p : NoncompactProfile) (N : ℕ) (W : ℝ)
    {R m M : ℝ} (hbounds : ∀ x, |x| ≤ R → m ≤ p.f x ∧ p.f x ≤ M)
    (hwindow : ∀ s : ZMod N, |(centeredOffset N s : ℝ) / W| ≤ R) :
    ∀ s, m ≤ p.raw N W s ∧ p.raw N W s ≤ M :=
  fun s => hbounds _ (hwindow s)

theorem weight_bounds_of_raw_bounds (p : NoncompactProfile)
    (N : ℕ) [NeZero N] (W : ℝ) {m M : ℝ} (hm : 0 < m)
    (hbounds : ∀ s : ZMod N, m ≤ p.raw N W s ∧ p.raw N W s ≤ M) :
    ∀ s, m / ((N : ℝ) * M) ≤ p.weight N W s ∧
      p.weight N W s ≤ M / ((N : ℝ) * m) := by
  have hlo : (N : ℝ) * m ≤ p.normalizer N W := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun s _ => (hbounds s).1)
    simpa only [normalizer, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] using h
  have hhi : p.normalizer N W ≤ (N : ℝ) * M := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun s _ => (hbounds s).2)
    simpa only [normalizer, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] using h
  intro s
  exact ⟨div_le_div₀ (p.positive _).le (hbounds s).1 (p.normalizer_pos N W) hhi,
    div_le_div₀ ((p.positive _).le.trans (hbounds s).2) (hbounds s).2
      (mul_pos (by exact_mod_cast NeZero.pos N) hm) hlo⟩

theorem core_weight_bounds_of_raw_bounds (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (hsize : 2 * H + 1 ≤ N) (W : ℝ)
    {m M : ℝ} (hm : 0 < m)
    (hbounds : ∀ s ∈ coreOffsets N H, m ≤ p.raw N W s ∧ p.raw N W s ≤ M) :
    ∀ s ∈ coreOffsets N H,
      m / (((2 * H + 1 : ℕ) : ℝ) * M) ≤ p.normalizedCoreWeight N H W s ∧
      p.normalizedCoreWeight N H W s ≤ M / (((2 * H + 1 : ℕ) : ℝ) * m) := by
  have hlo : (((2 * H + 1 : ℕ) : ℝ) * m) ≤ p.rawCoreMass N H W := by
    have h := Finset.sum_le_sum (s := coreOffsets N H) (fun s hs => (hbounds s hs).1)
    simpa only [rawCoreMass, Finset.sum_const, card_coreOffsets N H hsize, nsmul_eq_mul] using h
  have hhi : p.rawCoreMass N H W ≤ (((2 * H + 1 : ℕ) : ℝ) * M) := by
    have h := Finset.sum_le_sum (s := coreOffsets N H) (fun s hs => (hbounds s hs).2)
    simpa only [rawCoreMass, Finset.sum_const, card_coreOffsets N H hsize, nsmul_eq_mul] using h
  intro s hs
  exact ⟨div_le_div₀ (p.positive _).le (hbounds s hs).1 (p.rawCoreMass_pos N H W) hhi,
    div_le_div₀ ((p.positive _).le.trans (hbounds s hs).2) (hbounds s hs).2
      (mul_pos (by positivity) hm) hlo⟩

theorem centeredOffset_abs_le_dimension (N : ℕ) [NeZero N] (s : ZMod N) :
    |(centeredOffset N s : ℝ)| ≤ (N : ℝ) := by
  have hb := centeredOffset_bounds N s
  have h : |centeredOffset N s| ≤ (N : ℤ) := by rw [abs_le]; omega
  exact_mod_cast h

theorem dense_sample_window (N : ℕ) [NeZero N] {W κ : ℝ}
    (hκ : 0 < κ) (hW : κ * (N : ℝ) ≤ W) (s : ZMod N) :
    |(centeredOffset N s : ℝ) / W| ≤ κ⁻¹ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hWpos := (mul_pos hκ hN).trans_le hW
  rw [abs_div, abs_of_pos hWpos, ← one_div κ]
  apply (div_le_div_iff₀ hWpos hκ).2
  calc
    _ ≤ (N : ℝ) * κ := mul_le_mul_of_nonneg_right (centeredOffset_abs_le_dimension N s) hκ.le
    _ ≤ _ := by simpa only [one_mul, mul_one, mul_comm] using hW

/-- The dense branch has entry variances comparable with `1/N`, with constants
depending only on the profile and the fixed lower bound for `W/N`. -/
theorem dense_weights_comparable (p : NoncompactProfile) {κ : ℝ} (hκ : 0 < κ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) [NeZero N] (W : ℝ), κ * (N : ℝ) ≤ W →
        ∀ s : ZMod N, c / (N : ℝ) ≤ p.weight N W s ∧ p.weight N W s ≤ C / (N : ℝ) := by
  obtain ⟨m, M, hm, hM, hb⟩ := p.compact_bounds (R := κ⁻¹) (inv_nonneg.2 hκ.le)
  refine ⟨m / M, M / m, div_pos hm hM, div_pos hM hm, ?_⟩
  intro N _ W hW s
  have hr := p.raw_bounds_of_window N W hb (dense_sample_window N hκ hW)
  simpa only [div_div, mul_comm] using p.weight_bounds_of_raw_bounds N W hm hr s

/-- After normalization, a fixed compact core has entry variances comparable
with `1/W`. All constants are independent of `N` and `W`. -/
theorem core_weights_comparable (p : NoncompactProfile) {R : ℝ} (hR : 0 < R) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) [NeZero N] (W : ℝ), 1 ≤ W → 2 * ⌊R * W⌋₊ + 1 ≤ N →
        ∀ s ∈ coreOffsets N ⌊R * W⌋₊,
          c / W ≤ p.normalizedCoreWeight N ⌊R * W⌋₊ W s ∧
            p.normalizedCoreWeight N ⌊R * W⌋₊ W s ≤ C / W := by
  obtain ⟨m, M, hm, hM, hb⟩ := p.compact_bounds hR.le
  refine ⟨m / (M * (2 * R + 1)), M / (m * R), by positivity, by positivity, ?_⟩
  intro N _ W hW hsize s hs
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW
  let H := ⌊R * W⌋₊
  let k : ℝ := (2 * H + 1 : ℕ)
  have hk : 0 < k := by dsimp [k]; positivity
  have hfloor : (H : ℝ) ≤ R * W := Nat.floor_le (mul_nonneg hR.le hWpos.le)
  have hfloor' : R * W < (H : ℝ) + 1 := Nat.lt_floor_add_one (R * W)
  have hkLower : R * W ≤ k := by dsimp [k]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) H]
  have hkUpper : k ≤ (2 * R + 1) * W := by dsimp [k]; push_cast; nlinarith
  have hraw : ∀ t ∈ coreOffsets N H, m ≤ p.raw N W t ∧ p.raw N W t ≤ M := by
    intro t ht
    apply hb
    have ht' : |(centeredOffset N t : ℝ)| ≤ (H : ℝ) := by
      exact_mod_cast (mem_coreOffsets N H t).1 ht
    rw [abs_div, abs_of_pos hWpos]
    exact (div_le_iff₀ hWpos).2 (ht'.trans hfloor)
  have hweight := p.core_weight_bounds_of_raw_bounds N H hsize W hm hraw s hs
  have hl : (m / (M * (2 * R + 1))) / W ≤ m / (k * M) := by
    rw [div_div]
    apply div_le_div₀ hm.le le_rfl (mul_pos hk hM)
    calc
      k * M ≤ ((2 * R + 1) * W) * M := mul_le_mul_of_nonneg_right hkUpper hM.le
      _ = _ := by ring
  have hu : M / (k * m) ≤ (M / (m * R)) / W := by
    rw [div_div]
    apply div_le_div₀ hM.le le_rfl (mul_pos (mul_pos hm hR) hWpos)
    calc
      m * R * W = (R * W) * m := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hkLower hm.le
  exact ⟨hl.trans hweight.1, hweight.2.trans hu⟩

end CircularLawSection6.NoncompactProfile
