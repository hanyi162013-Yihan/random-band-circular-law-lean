import BernoulliSection10.MultiAffineGrowth

open scoped BigOperators

noncomputable section

namespace BernoulliSection10

set_option maxHeartbeats 800000

/-- A simultaneous Rademacher lower bound.  One sign choice controls the
sum of squared evaluations of an arbitrary finite family of scalar
row-multiaffine tensors. -/
theorem exists_rademacherRows_sum_norm_sq_le
    : ∀ (n : ℕ) {α : Type*} [Fintype α]
      (c : α → MultiAffineTensor ℂ (List.replicate n 1)),
      ∃ x : Fin n → Fin 1 → ℝ,
        (∀ i j, x i j = 1 ∨ x i j = -1) ∧
        (∑ a, ‖c a‖ ^ 2) ≤
          ∑ a, ‖multiAffineEval (c a)
            (finRowsToMultiAffineRows 1 n x)‖ ^ 2 := by
  intro n
  induction n with
  | zero =>
      intro α inst c
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · change (∑ a, ‖c a‖ ^ 2) ≤ ∑ a, ‖c a‖ ^ 2
        exact le_rfl
  | succ n ih =>
      intro α inst c
      let d : α × Fin 2 → MultiAffineTensor ℂ (List.replicate n 1) :=
        fun q ↦ multiAffineTensorHead (c q.1) q.2
      obtain ⟨y, hySign, hy⟩ := ih d
      let A : α → ℂ := fun a ↦
        multiAffineEval (multiAffineTensorHead (c a) 0)
          (finRowsToMultiAffineRows 1 n y)
      let B : α → ℂ := fun a ↦
        multiAffineEval (multiAffineTensorHead (c a) 1)
          (finRowsToMultiAffineRows 1 n y)
      have hcoeff : (∑ a, ‖c a‖ ^ 2) = ∑ q, ‖d q‖ ^ 2 := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro a ha
        change ‖c a‖ ^ 2 = ∑ b : Fin 2,
          ‖multiAffineTensorHead (c a) b‖ ^ 2
        exact PiLp.norm_sq_eq_of_L2
          (fun _ : Fin 2 ↦ MultiAffineTensor ℂ (List.replicate n 1))
          (show PiLp 2 (fun _ : Fin 2 ↦
            MultiAffineTensor ℂ (List.replicate n 1)) from c a)
      have heval : (∑ q, ‖multiAffineEval (d q)
          (finRowsToMultiAffineRows 1 n y)‖ ^ 2) =
          ∑ a, (‖A a‖ ^ 2 + ‖B a‖ ^ 2) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro a ha
        simp only [Fin.sum_univ_two]
        rfl
      have hbase : (∑ a, ‖c a‖ ^ 2) ≤
          ∑ a, (‖A a‖ ^ 2 + ‖B a‖ ^ 2) := by
        rw [hcoeff, ← heval]
        exact hy
      let plus : ℝ := ∑ a, ‖A a + B a‖ ^ 2
      let minus : ℝ := ∑ a, ‖A a - B a‖ ^ 2
      let base : ℝ := ∑ a, (‖A a‖ ^ 2 + ‖B a‖ ^ 2)
      have hpara : plus + minus = 2 * base := by
        simp only [plus, minus, base]
        rw [← Finset.sum_add_distrib]
        simp_rw [parallelogram_law_with_norm ℂ]
        rw [Finset.mul_sum]
      by_cases hp : base ≤ plus
      · let x : Fin (n + 1) → Fin 1 → ℝ :=
          Fin.cons (fun _ ↦ 1) y
        refine ⟨x, ?_, ?_⟩
        · intro i j
          refine Fin.cases ?_ (fun k ↦ ?_) i
          · left
            simp [x]
          · exact hySign k j
        · calc
            (∑ a, ‖c a‖ ^ 2) ≤ base := hbase
            _ ≤ plus := hp
            _ = ∑ a, ‖multiAffineEval (c a)
                  (finRowsToMultiAffineRows 1 (n + 1) x)‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro a ha
              change ‖A a + B a‖ ^ 2 =
                ‖multiAffineEval
                    (multiAffineHeadEval (c a) (fun _ : Fin 1 ↦ 1))
                    (finRowsToMultiAffineRows 1 n y)‖ ^ 2
              rw [show multiAffineHeadEval (c a) (fun _ : Fin 1 ↦ 1) =
                  multiAffineTensorHead (c a) 0 +
                    multiAffineTensorHead (c a) 1 by
                simp [multiAffineHeadEval, affineValue],
                multiAffineEval_add]
      · have hm : base ≤ minus := by
          have hp' : plus < base := lt_of_not_ge hp
          linarith
        let x : Fin (n + 1) → Fin 1 → ℝ :=
          Fin.cons (fun _ ↦ -1) y
        refine ⟨x, ?_, ?_⟩
        · intro i j
          refine Fin.cases ?_ (fun k ↦ ?_) i
          · right
            simp [x]
          · exact hySign k j
        · calc
            (∑ a, ‖c a‖ ^ 2) ≤ base := hbase
            _ ≤ minus := hm
            _ = ∑ a, ‖multiAffineEval (c a)
                  (finRowsToMultiAffineRows 1 (n + 1) x)‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro a ha
              change ‖A a - B a‖ ^ 2 =
                ‖multiAffineEval
                    (multiAffineHeadEval (c a) (fun _ : Fin 1 ↦ -1))
                    (finRowsToMultiAffineRows 1 n y)‖ ^ 2
              rw [show multiAffineHeadEval (c a) (fun _ : Fin 1 ↦ -1) =
                  multiAffineTensorHead (c a) 0 -
                    multiAffineTensorHead (c a) 1 by
                simp [multiAffineHeadEval, affineValue, sub_eq_add_neg],
                multiAffineEval_sub]

/-- In particular, every complex scalar row-multiaffine tensor has a sign
corner whose evaluation norm dominates its Euclidean coefficient norm. -/
theorem exists_rademacherRows_norm_le
    (n : ℕ) (c : MultiAffineTensor ℂ (List.replicate n 1)) :
    ∃ x : Fin n → Fin 1 → ℝ,
      (∀ i j, x i j = 1 ∨ x i j = -1) ∧
      ‖c‖ ≤ ‖multiAffineEval c
        (finRowsToMultiAffineRows 1 n x)‖ := by
  let family : Unit → MultiAffineTensor ℂ (List.replicate n 1) :=
    fun _ ↦ c
  obtain ⟨x, hx, hsq⟩ :=
    exists_rademacherRows_sum_norm_sq_le n family
  refine ⟨x, hx, ?_⟩
  simp only [Fintype.sum_unique, family] at hsq
  nlinarith [norm_nonneg c,
    norm_nonneg (multiAffineEval c (finRowsToMultiAffineRows 1 n x))]

end BernoulliSection10
