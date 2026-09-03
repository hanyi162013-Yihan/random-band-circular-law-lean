import ShortRingAnchor.DenseV3Model
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Proposition 3.8: the literal full-block cyclic variance profile

Equation (2.13), used in (3.18)--(3.25). There are `s + 3` blocks;
the proposition assumes `0 < s`. No density or spectral hypothesis is
part of this deterministic construction.
-/

noncomputable section
open scoped BigOperators
namespace ShortRingAnchor.Proposition38
open Arxiv2410V3

def siteAdjacent {s : ℕ} (i j : Fin (s + 3)) : Prop :=
  j = i ∨ j = finRotate (s + 3) i ∨ j = (finRotate (s + 3)).symm i

instance {s : ℕ} (i j : Fin (s + 3)) : Decidable (siteAdjacent i j) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Equation (2.13): the underlying three-neighbour mask is symmetric. -/
theorem siteAdjacent_symm {s : ℕ} {i j : Fin (s + 3)} :
    siteAdjacent i j ↔ siteAdjacent j i := by
  simp only [siteAdjacent, Equiv.eq_symm_apply, Equiv.symm_apply_eq]
  aesop

/-- Equation (2.13): the diagonal, forward and backward block positions
are distinct, including at the cyclic boundary. -/
theorem three_positions_distinct (s : ℕ) (i : Fin (s + 3)) :
    finRotate (s + 3) i ≠ i ∧ (finRotate (s + 3)).symm i ≠ i ∧
      finRotate (s + 3) i ≠ (finRotate (s + 3)).symm i := by
  have h1 := coe_finRotate (n := s + 2) i
  have h2 := coe_finRotate (n := s + 2) (finRotate (s + 3) i)
  simp only [Fin.ext_iff, Fin.val_last] at h1 h2
  change (finRotate (s + 3) i).val = if i.val = s + 2 then 0 else i.val + 1 at h1
  change (finRotate (s + 3) (finRotate (s + 3) i)).val =
    if (finRotate (s + 3) i).val = s + 2 then 0 else
      (finRotate (s + 3) i).val + 1 at h2
  have hf : finRotate (s + 3) i ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    split_ifs at h1 <;> omega
  have hff : finRotate (s + 3) (finRotate (s + 3) i) ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    split_ifs at h1 h2 <;> omega
  refine ⟨hf, ?_, ?_⟩
  · intro h
    have hh := congrArg (finRotate (s + 3)) h
    simp only [Equiv.apply_symm_apply] at hh
    exact hf hh.symm
  · intro h
    apply hff
    simpa only [Equiv.apply_symm_apply] using congrArg (finRotate (s + 3)) h

def coefficient (W s : ℕ) (i j : Fin ((s + 3) * W)) : ℝ :=
  if siteAdjacent (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
  then (Real.sqrt (3 * (W : ℝ)))⁻¹ else 0

/-- Equation (2.13): the three active block variances are exactly `1/(3W)`. -/
theorem coefficient_sq (W s : ℕ) (i j : Fin (s + 3)) (a b : Fin W) :
    coefficient W s (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) ^ 2 =
      (if j = i then (3 * (W : ℝ))⁻¹ else 0) +
      (if j = finRotate (s + 3) i then (3 * (W : ℝ))⁻¹ else 0) +
      (if j = (finRotate (s + 3)).symm i then (3 * (W : ℝ))⁻¹ else 0) := by
  have hn : (Real.sqrt (3 * (W : ℝ)))⁻¹ ^ 2 = (3 * (W : ℝ))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  obtain ⟨h1, h2, h3⟩ := three_positions_distinct s i
  simp only [coefficient, Equiv.symm_apply_apply, siteAdjacent]
  by_cases hd : j = i
  · subst j
    simp only [h1.symm, h2.symm, if_true, if_false, true_or, hn, add_zero]
  · by_cases hb : j = finRotate (s + 3) i
    · subst j
      simp only [h1, h3, if_true, if_false, or_true, true_or, hn, zero_add, add_zero]
    · by_cases hc : j = (finRotate (s + 3)).symm i
      · subst j
        simp only [h2, h3.symm, if_true, if_false, or_true, hn, zero_add, add_zero]
      · simp only [hd, hb, hc, if_false, false_or, zero_pow (by omega : 2 ≠ 0), add_zero]

/-- Equation (2.13) / v3 Definition 1.2: each row has total variance one. -/
theorem coefficient_row (W s : ℕ) (hW : 0 < W)
    (i : Fin ((s + 3) * W)) : ∑ j, coefficient W s i j ^ 2 = 1 := by
  obtain ⟨⟨j, a⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [← (finProdFinEquiv : Fin (s + 3) × Fin W ≃ Fin ((s + 3) * W)).sum_comp]
  simp only [Fintype.sum_prod_type, coefficient_sq]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib]
  simp
  field_simp
  <;> ring

/-- Equation (2.13): the coefficient matrix is symmetric. -/
theorem coefficient_symm (W s : ℕ) (i j : Fin ((s + 3) * W)) :
    coefficient W s i j = coefficient W s j i := by
  simp only [coefficient, siteAdjacent_symm]

/-- Equation (2.13) / v3 Definition 1.2: each column has total variance one. -/
theorem coefficient_column (W s : ℕ) (hW : 0 < W)
    (j : Fin ((s + 3) * W)) : ∑ i, coefficient W s i j ^ 2 = 1 := by
  simp_rw [coefficient_symm W s _ j]
  exact coefficient_row W s hW j

def varianceProfile (W s : ℕ) (hW : 0 < W) :
    DoublyStochasticVarianceProfile (Fin ((s + 3) * W)) where
  coefficient := coefficient W s
  coefficient_nonneg i j := by unfold coefficient; split_ifs <;> positivity
  row_sq_sum := coefficient_row W s hW
  col_sq_sum := coefficient_column W s hW

/-- Proposition 3.8 before (3.20): the bandwidth is exactly `3W`. -/
theorem varianceProfile_isBandwidth (W s : ℕ) (hW : 0 < W) :
    IsBandwidth (varianceProfile W s hW) (3 * (W : ℝ)) := by
  have hn : (Real.sqrt (3 * (W : ℝ)))⁻¹ ^ 2 = (3 * (W : ℝ))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  refine ⟨by positivity, ?_, ?_⟩
  · intro i j
    change coefficient W s i j ^ 2 ≤ _
    unfold coefficient
    split_ifs
    · exact hn.le
    · simp only [zero_pow (by omega : 2 ≠ 0)]
      positivity
  · let i : Fin ((s + 3) * W) := ⟨0, Nat.mul_pos (by omega) hW⟩
    refine ⟨i, i, ?_⟩
    change coefficient W s i i ^ 2 = _
    simp only [coefficient, siteAdjacent, true_or, if_true, hn]

end ShortRingAnchor.Proposition38
