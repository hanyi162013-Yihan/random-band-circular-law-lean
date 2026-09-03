import CircularLawSection6.SampledProfile

/-! # A dimension-uniform diagonal lower bound for every bandwidth

Bounded variation gives a global upper bound on the profile. Its strictly
positive value at zero then controls the diagonal variance after either
full normalization or compact-core normalization. No sparse/dense split
and no positive lower bound on the entire real line is needed.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace CircularLawSection6.NoncompactProfile

def globalUpperBound (p : NoncompactProfile) : ℝ :=
  p.f 0 + (eVariationOn p.f univ).toReal

theorem globalUpperBound_pos (p : NoncompactProfile) : 0 < p.globalUpperBound :=
  add_pos_of_pos_of_nonneg (p.positive 0) ENNReal.toReal_nonneg

theorem le_globalUpperBound (p : NoncompactProfile) (x : ℝ) : p.f x ≤ p.globalUpperBound := by
  have h := p.boundedVariation.sub_le (x := x) (y := 0) (mem_univ x) (mem_univ 0)
  unfold globalUpperBound
  linarith

def diagonalComparisonConstant (p : NoncompactProfile) : ℝ := p.f 0 / p.globalUpperBound

theorem diagonalComparisonConstant_pos (p : NoncompactProfile) :
    0 < p.diagonalComparisonConstant := div_pos (p.positive 0) p.globalUpperBound_pos

theorem diagonalComparisonConstant_le_one (p : NoncompactProfile) :
    p.diagonalComparisonConstant ≤ 1 :=
  (div_le_one p.globalUpperBound_pos).2 (p.le_globalUpperBound 0)

theorem normalizer_le_globalUpperBound (p : NoncompactProfile)
    (N : ℕ) [NeZero N] (W : ℝ) : p.normalizer N W ≤ (N : ℝ) * p.globalUpperBound := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (s : ZMod N) _ => p.le_globalUpperBound ((centeredOffset N s : ℝ) / W))
  simpa only [normalizer, raw, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] using h

theorem rawCoreMass_le_normalizer (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) : p.rawCoreMass N H W ≤ p.normalizer N W := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro s _ _
  exact (p.positive _).le

theorem diagonal_weight_ge (p : NoncompactProfile) (N : ℕ) [NeZero N] (W : ℝ) :
    p.diagonalComparisonConstant / (N : ℝ) ≤ p.weight N W 0 := by
  simp only [weight, raw, centeredOffset_zero, Int.cast_zero, zero_div]
  calc
    _ = p.f 0 / ((N : ℝ) * p.globalUpperBound) := by
      unfold diagonalComparisonConstant
      rw [div_div, mul_comm]
    _ ≤ _ := div_le_div₀ (p.positive 0).le le_rfl (p.normalizer_pos N W)
      (p.normalizer_le_globalUpperBound N W)

theorem diagonal_normalizedCoreWeight_ge (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) :
    p.diagonalComparisonConstant / (N : ℝ) ≤ p.normalizedCoreWeight N H W 0 := by
  simp only [normalizedCoreWeight, raw, centeredOffset_zero, Int.cast_zero, zero_div]
  calc
    _ = p.f 0 / ((N : ℝ) * p.globalUpperBound) := by
      unfold diagonalComparisonConstant
      rw [div_div, mul_comm]
    _ ≤ _ := div_le_div₀ (p.positive 0).le le_rfl (p.rawCoreMass_pos N H W)
      ((p.rawCoreMass_le_normalizer N H W).trans (p.normalizer_le_globalUpperBound N W))

end CircularLawSection6.NoncompactProfile
