import CircularLawSections56.Section5.TaperDiscreteAsymptotics
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

/-! # Doubly stochastic variance profile of the actual taper

The cyclic profile has row and column sums one. Under the manuscript's
non-aliasing condition its entry upper bound and inner-band lower bound are
exactly the discrete bounds needed by the accepted Section 3 anchor.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5

def cyclicVarianceProfile (N D : ℕ) [NeZero N] (center : ZMod N) (q : Fin D → ℝ) :
    Matrix (ZMod N) (ZMod N) ℝ :=
  fun i j => ∑ s : Fin D, if j = i - center + (s.val : ZMod N) then q s else 0

theorem cyclicVarianceProfile_nonneg (N D : ℕ) [NeZero N]
    (center : ZMod N) (q : Fin D → ℝ) (hq : ∀ s, 0 ≤ q s) (i j : ZMod N) :
    0 ≤ cyclicVarianceProfile N D center q i j := by
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact hq s
  · exact le_rfl

theorem cyclicVarianceProfile_row_sum (N D : ℕ) [NeZero N]
    (center : ZMod N) (q : Fin D → ℝ) (i : ZMod N) :
    ∑ j, cyclicVarianceProfile N D center q i j = ∑ s, q s := by
  unfold cyclicVarianceProfile
  rw [Finset.sum_comm]
  simp

theorem cyclicVarianceProfile_column_sum (N D : ℕ) [NeZero N]
    (center : ZMod N) (q : Fin D → ℝ) (j : ZMod N) :
    ∑ i, cyclicVarianceProfile N D center q i j = ∑ s, q s := by
  have he (i : ZMod N) (s : Fin D) :
      j = i - center + (s.val : ZMod N) ↔ i = j + center - (s.val : ZMod N) := by
    constructor <;> intro h <;> rw [h] <;> abel
  unfold cyclicVarianceProfile
  simp_rw [he]
  rw [Finset.sum_comm]
  simp

theorem cyclicVarianceProfile_slot (N D : ℕ) [NeZero N] (hFit : D ≤ N)
    (center : ZMod N) (q : Fin D → ℝ) (i : ZMod N) (s : Fin D) :
    cyclicVarianceProfile N D center q i (i - center + (s.val : ZMod N)) = q s := by
  have hinj : Function.Injective (fun t : Fin D => (t.val : ZMod N)) := by
    intro a b hab
    apply Fin.ext
    exact CharP.natCast_injOn_Iio (ZMod N) N
      (lt_of_lt_of_le a.isLt hFit) (lt_of_lt_of_le b.isLt hFit) hab
  have he (t : Fin D) :
      i - center + (s.val : ZMod N) = i - center + (t.val : ZMod N) ↔ s = t := by
    exact add_left_cancel_iff.trans hinj.eq_iff
  unfold cyclicVarianceProfile
  simp_rw [he]
  simp

theorem cyclicVarianceProfile_entry_le (N D : ℕ) [NeZero N] (hFit : D ≤ N)
    (center : ZMod N) (q : Fin D → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hq : ∀ s, q s ≤ C) (i j : ZMod N) : cyclicVarianceProfile N D center q i j ≤ C := by
  by_cases h : ∃ s : Fin D, j = i - center + (s.val : ZMod N)
  · obtain ⟨s, rfl⟩ := h
    rw [cyclicVarianceProfile_slot N D hFit]
    exact hq s
  · have hs : ∀ s : Fin D, j ≠ i - center + (s.val : ZMod N) := by simpa using h
    simpa only [cyclicVarianceProfile, hs, if_false, Finset.sum_const_zero] using hC

namespace PolynomialTaperProfile

def varianceMatrix (p : PolynomialTaperProfile) (N W : ℕ) [NeZero N] :
    Matrix (ZMod N) (ZMod N) ℝ :=
  cyclicVarianceProfile N (2 * W + 1) (W : ZMod N) (p.weight W)

theorem varianceMatrix_doubly_stochastic (p : PolynomialTaperProfile) (N W : ℕ) [NeZero N] :
    (∀ i j, 0 ≤ p.varianceMatrix N W i j) ∧
      (∀ i, ∑ j, p.varianceMatrix N W i j = 1) ∧
      (∀ j, ∑ i, p.varianceMatrix N W i j = 1) := by
  refine ⟨cyclicVarianceProfile_nonneg N _ _ _ (fun s => (p.weight_pos W s).le), ?_, ?_⟩
  · intro i
    exact (cyclicVarianceProfile_row_sum N _ _ _ i).trans (p.sum_weight W)
  · intro j
    exact (cyclicVarianceProfile_column_sum N _ _ _ j).trans (p.sum_weight W)

theorem varianceMatrix_upper (p : PolynomialTaperProfile) (N W : ℕ) [NeZero N]
    (hW : 0 < W) (hFit : 2 * W + 1 ≤ N) (i j : ZMod N) :
    p.varianceMatrix N W i j ≤ p.upperWeightConstant / (W : ℝ) :=
  cyclicVarianceProfile_entry_le N _ hFit _ _ _
    (div_nonneg p.upperWeightConstant_pos.le (Nat.cast_nonneg _))
    (p.weight_upper_linear W hW) i j

theorem varianceMatrix_inner_lower (p : PolynomialTaperProfile) (N W : ℕ) [NeZero N]
    (hW : 0 < W) (hFit : 2 * W + 1 ≤ N) (i : ZMod N) (s : Fin (2 * W + 1))
    (hs : |taperGrid W s| ≤ 1 / 2) :
    p.lowerWeightConstant / (W : ℝ) ≤
      p.varianceMatrix N W i (i - (W : ZMod N) + (s.val : ZMod N)) := by
  rw [varianceMatrix, cyclicVarianceProfile_slot N _ hFit]
  exact p.weight_inner_linear W hW s hs

end PolynomialTaperProfile

end CircularLawSections56.Section5
