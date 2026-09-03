import CircularLawSection6.ClampedCoreGeometry

/-! # Uniformly comparable literal profiles for globally clamped cores

The compact bounds are constructed from the original positive continuous
profile. Small indices use normalized uniform weights with the same bounds.
At every fitting positive index the weights are exactly the actual sampled
core weights, not a comparison profile supplied by the caller.
-/

open MeasureTheory
open CircularLawSection4
open scoped BigOperators

noncomputable section

namespace CircularLawSection6

structure CoreRadiusBounds (p : NoncompactProfile) (R : ℝ) where
  radius_nonneg : 0 ≤ R
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  lower_le_upper : lower ≤ upper
  bounds : ∀ x, |x| ≤ R → lower ≤ p.f x ∧ p.f x ≤ upper

def NoncompactProfile.coreRadiusBounds (p : NoncompactProfile) {R : ℝ} (hR : 0 ≤ R) :
    CoreRadiusBounds p R := Classical.choice (by
  obtain ⟨m, M, hm, hM, hb⟩ := p.compact_bounds hR
  have h0 := hb 0 (by simpa only [abs_zero] using hR)
  exact ⟨⟨hR, m, M, hm, hM, h0.1.trans h0.2, hb⟩⟩)

namespace CoreRadiusBounds

variable {p : NoncompactProfile} {R : ℝ}

def uniformWeights (B : CoreRadiusBounds p R) (d : ℕ) :
    PaperIndicatorWeights d (B.lower / B.upper) (B.upper / B.lower) where
  q := fun _ => 1 / (d + 1 : ℝ)
  normalized := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, one_div]
    exact mul_inv_cancel₀ (by positivity)
  lower _ := div_le_div_of_nonneg_right
    ((div_le_one B.upper_pos).2 B.lower_le_upper) (by positivity)
  upper _ := div_le_div_of_nonneg_right
    ((one_le_div B.lower_pos).2 B.lower_le_upper) (by positivity)

theorem raw_bounds (B : CoreRadiusBounds p R) (N H : ℕ) [NeZero N]
    (W : ℝ) (hW : 0 < W) (hHW : (H : ℝ) ≤ R * W) :
    ∀ t ∈ coreOffsets N H, B.lower ≤ p.raw N W t ∧ p.raw N W t ≤ B.upper := by
  intro t ht
  apply B.bounds
  have hbound : |(centeredOffset N t : ℝ)| ≤ (H : ℝ) := by
    exact_mod_cast (mem_coreOffsets N H t).1 ht
  rw [abs_div, abs_of_pos hW]
  exact (div_le_iff₀ hW).2 (hbound.trans hHW)

def coreWeights (B : CoreRadiusBounds p R) (N H : ℕ) [NeZero N]
    (hH : 0 < H) (hfit : 2 * H + 1 ≤ N) (W : ℝ) (hW : 0 < W)
    (hHW : (H : ℝ) ≤ R * W) :
    PaperIndicatorWeights (canonicalCoreBand H + 1) (B.lower / B.upper) (B.upper / B.lower) :=
  p.corePaperWeights N (canonicalCoreBand H)
    (by rwa [canonicalCoreBand_width hH]) (canonicalCoreCenter H hH)
    (canonicalCoreCenter_symmetric hH) W B.lower_pos (B.raw_bounds N H W hW hHW)

def clampedWeights (B : CoreRadiusBounds p R) (W : ℝ) (n : ℕ) :
    PaperIndicatorWeights (canonicalCoreBand (clampedCoreHalfWidth R W n) + 1)
      (B.lower / B.upper) (B.upper / B.lower) :=
  if h : 2 ≤ n ∧ 0 < W ∧ 0 < ⌊R * W⌋₊ then
    B.coreWeights (n + 1) (clampedCoreHalfWidth R W n)
      (clampedCoreHalfWidth_pos R W n) (clampedCoreHalfWidth_fits R W h.1) W h.2.1
      ((by exact_mod_cast clampedCoreHalfWidth_le_floor R W n h.2.2 :
        (clampedCoreHalfWidth R W n : ℝ) ≤ (⌊R * W⌋₊ : ℝ)).trans
        (Nat.floor_le (mul_nonneg B.radius_nonneg h.2.1.le)))
  else B.uniformWeights (canonicalCoreBand (clampedCoreHalfWidth R W n) + 1)

theorem clampedWeights_q (B : CoreRadiusBounds p R) (W : ℝ) (n : ℕ)
    (hn : 2 ≤ n) (hW : 0 < W) (hf : 0 < ⌊R * W⌋₊)
    (s : Fin (canonicalCoreBand (clampedCoreHalfWidth R W n) + 1 + 1)) :
    (B.clampedWeights W n).q s =
      p.coreBandWeight (n + 1) (canonicalCoreBand (clampedCoreHalfWidth R W n))
        (canonicalCoreCenter _ (clampedCoreHalfWidth_pos R W n)) W s := by
  have h : 2 ≤ n ∧ 0 < W ∧ 0 < ⌊R * W⌋₊ := ⟨hn, hW, hf⟩
  simp only [clampedWeights, dif_pos h, coreWeights,
    NoncompactProfile.corePaperWeights]

end CoreRadiusBounds
end CircularLawSection6
