import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring

/-! # Finite spectral comparison through a doubly stochastic coupling

No sorting or choice of an optimal matching is required for averages of a
Lipschitz function. A nonnegative coupling with unit row and column sums
and its squared transport cost suffice. Eigenvector overlaps provide this
coupling in the Hermitian matrix application.
-/

open scoped BigOperators

noncomputable section

namespace CircularLawSection6

variable {ι : Type*} [Fintype ι]

theorem weighted_abs_difference_le_sqrt
    (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j = 1)
    (a b : ι → ℝ) :
    (∑ i, ∑ j, w i j * |a i - b j|) ≤
      Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, ∑ j, w i j * (a i - b j) ^ 2) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (R := ℝ) (s := Finset.univ)
    (r := fun k : ι × ι => w k.1 k.2 * |a k.1 - b k.2|)
    (f := fun k : ι × ι => w k.1 k.2)
    (g := fun k : ι × ι => w k.1 k.2 * (a k.1 - b k.2) ^ 2)
    (fun k _ => hw k.1 k.2)
    (fun k _ => mul_nonneg (hw k.1 k.2) (sq_nonneg _))
    (fun k _ => by simp only [mul_pow, sq_abs]; ring_nf; exact le_rfl)
  simp only [Fintype.sum_prod_type] at h
  have hmass : (∑ i, ∑ j, w i j) = (Fintype.card ι : ℝ) := by simp [hrow]
  rw [hmass] at h
  exact Real.le_sqrt_of_sq_le h

theorem sum_difference_eq_weighted
    (w : ι → ι → ℝ) (hrow : ∀ i, ∑ j, w i j = 1) (hcol : ∀ j, ∑ i, w i j = 1)
    (a b : ι → ℝ) :
    (∑ i, a i) - (∑ j, b j) = ∑ i, ∑ j, w i j * (a i - b j) := by
  have ha : (∑ i, ∑ j, w i j * a i) = ∑ i, a i := by
    simp_rw [← Finset.sum_mul, hrow, one_mul]
  have hb : (∑ i, ∑ j, w i j * b j) = ∑ j, b j := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol, one_mul]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [ha, hb]

theorem lipschitz_sum_difference_le_weighted_cost
    (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, ∑ j, w i j = 1) (hcol : ∀ j, ∑ i, w i j = 1)
    (a b : ι → ℝ) (φ : ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ x y, |φ x - φ y| ≤ K * |x - y|) :
    |(∑ i, φ (a i)) - (∑ j, φ (b j))| ≤
      K * Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, ∑ j, w i j * (a i - b j) ^ 2) := by
  rw [sum_difference_eq_weighted w hrow hcol]
  calc
    _ ≤ ∑ i, |∑ j, w i j * (φ (a i) - φ (b j))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |w i j * (φ (a i) - φ (b j))| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i, ∑ j, w i j * |φ (a i) - φ (b j)| := by
      simp_rw [abs_mul, abs_of_nonneg (hw _ _)]
    _ ≤ ∑ i, ∑ j, w i j * (K * |a i - b j|) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
        (fun j _ => mul_le_mul_of_nonneg_left (hφ (a i) (b j)) (hw i j)))
    _ = K * (∑ i, ∑ j, w i j * |a i - b j|) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (weighted_abs_difference_le_sqrt w hw hrow a b) hK

end CircularLawSection6
