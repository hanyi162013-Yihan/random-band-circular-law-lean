import CircularLawSection6.CoreBandIdentification
import CircularLawSection6.SparseProfileGeometry

/-! # Canonical finite-band data for the floor-radius core

A core of half-width `H >= 1` has `2H+1` active offsets, so the literal
Section 5 band parameter is `d=2H-1` and its center is `H`. The excluded
radius-zero prefix is handled by an eventual statement, not an impossible
center filler. Compact profile bounds produce the actual Section 5 weights
with constants independent of matrix size and bandwidth.
-/

open MeasureTheory Filter Topology
open CircularLawSection4

noncomputable section

namespace CircularLawSection6

def canonicalCoreBand (H : ℕ) : ℕ := 2 * H - 1

def canonicalCoreCenter (H : ℕ) (hH : 0 < H) : Fin (canonicalCoreBand H + 1) :=
  ⟨H, by unfold canonicalCoreBand; omega⟩

theorem canonicalCoreBand_width {H : ℕ} (hH : 0 < H) :
    canonicalCoreBand H + 2 = 2 * H + 1 := by
  unfold canonicalCoreBand
  omega

theorem canonicalCoreCenter_symmetric {H : ℕ} (hH : 0 < H) :
    canonicalCoreBand H + 1 = 2 * (canonicalCoreCenter H hH).val := by
  simp only [canonicalCoreBand, canonicalCoreCenter]
  omega

theorem floor_radius_atTop (W : ℕ → ℝ) (hW : Tendsto W atTop atTop)
    {R : ℝ} (hR : 0 < R) : Tendsto (fun n => ⌊R * W n⌋₊) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(hW.const_mul_atTop hR).eventually_ge_atTop (b : ℝ)] with n hn
  exact Nat.le_floor hn

theorem canonicalCoreBand_atTop (W : ℕ → ℝ) (hW : Tendsto W atTop atTop)
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n => canonicalCoreBand ⌊R * W n⌋₊ + 1) atTop atTop := by
  apply tendsto_atTop_mono _ (floor_radius_atTop W hW hR)
  intro n
  unfold canonicalCoreBand
  omega

theorem canonical_floor_core_eventually_fits (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (W : ℕ → ℝ) (hW : ∀ n, 0 < W n)
    (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (N n : ℝ)) atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ n in atTop, 0 < ⌊R * W n⌋₊ ∧ canonicalCoreBand ⌊R * W n⌋₊ + 2 ≤ N n := by
  filter_upwards [(floor_radius_atTop W hWlim hR).eventually_ge_atTop 1,
    sparse_floor_core_fits N hN W hW hWlim hsparse hR.le] with n hn hfit
  have hpos : 0 < ⌊R * W n⌋₊ := hn
  exact ⟨hpos, by rwa [canonicalCoreBand_width hpos]⟩

namespace NoncompactProfile

theorem canonical_core_paper_weights (p : NoncompactProfile) {R : ℝ} (hR : 0 < R) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) [NeZero N] (W : ℝ), 0 < W →
        ∀ (hH : 0 < ⌊R * W⌋₊), 2 * ⌊R * W⌋₊ + 1 ≤ N →
          ∃ profile : PaperIndicatorWeights (canonicalCoreBand ⌊R * W⌋₊ + 1) c C,
            ∀ s, profile.q s = p.coreBandWeight N (canonicalCoreBand ⌊R * W⌋₊)
              (canonicalCoreCenter ⌊R * W⌋₊ hH) W s := by
  obtain ⟨m, M, hm, hM, hb⟩ := p.compact_bounds hR.le
  refine ⟨m / M, M / m, div_pos hm hM, div_pos hM hm, ?_⟩
  intro N _ W hW hH hfit
  have hraw : ∀ t ∈ coreOffsets N ⌊R * W⌋₊,
      m ≤ p.raw N W t ∧ p.raw N W t ≤ M := by
    intro t ht
    apply hb
    have hbound : |(centeredOffset N t : ℝ)| ≤ (⌊R * W⌋₊ : ℝ) := by
      exact_mod_cast (mem_coreOffsets N ⌊R * W⌋₊ t).1 ht
    rw [abs_div, abs_of_pos hW]
    exact (div_le_iff₀ hW).2 (hbound.trans (Nat.floor_le (mul_nonneg hR.le hW.le)))
  exact ⟨p.corePaperWeights N (canonicalCoreBand ⌊R * W⌋₊)
    (by rwa [canonicalCoreBand_width hH]) (canonicalCoreCenter _ hH)
    (canonicalCoreCenter_symmetric hH) W hm hraw, fun _ => rfl⟩

end NoncompactProfile
end CircularLawSection6
