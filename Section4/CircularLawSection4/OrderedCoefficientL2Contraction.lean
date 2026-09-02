import CircularLawSection4.OrderedBooleanBridge
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Euclidean contraction of ordered coefficient matrices

A square complex matrix with at most one nonzero entry in every row and
column, and with all entry norms at most one, is an `ℓ²` contraction.  The
ordered reset/star coefficient matrices satisfy these hypotheses because a
surviving entry determines a successful Boolean support step, and successful
steps are injective on their domains.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

section SparseMatrix

variable {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
private theorem norm_sum_sq_eq_sum_norm_sq_of_sparse
    (v : m → ℂ)
    (hsparse : ∀ i j, v i ≠ 0 → v j ≠ 0 → i = j) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  by_cases h : ∃ i, v i ≠ 0
  · obtain ⟨i, hi⟩ := h
    have hzero : ∀ j, j ≠ i → v j = 0 := by
      intro j hji
      by_contra hj
      exact hji (hsparse j i hj hi)
    have hsum : ∑ j, v j = v i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact hzero j hji
      · simp
    have hnormsum : ∑ j, ‖v j‖ ^ 2 = ‖v i‖ ^ 2 := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [hzero j hji]
        simp
      · simp
    rw [hsum, hnormsum]
  · push Not at h
    simp [h]

/-- A complex matrix supported on a partial injective matching, with weights
of norm at most one, is a contraction for the Euclidean operator norm. -/
theorem l2_opNorm_le_one_of_row_col_sparse_of_entry_norm_le_one
    (A : Matrix m m ℂ)
    (hrow : ∀ i j k, A i j ≠ 0 → A i k ≠ 0 → j = k)
    (hcol : ∀ i j k, A i k ≠ 0 → A j k ≠ 0 → i = j)
    (hentry : ∀ i j, ‖A i j‖ ≤ 1) :
    ‖A‖ ≤ 1 := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A).opNorm_le_bound
    zero_le_one ?_
  intro x
  change ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)‖ ≤ 1 * ‖x‖
  rw [one_mul]
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [PiLp.norm_sq_eq_of_L2 (fun _ : m => ℂ)
      (WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)),
    PiLp.norm_sq_eq_of_L2 (fun _ : m => ℂ) x]
  calc
    ∑ i, ‖(A *ᵥ WithLp.ofLp x) i‖ ^ 2 =
        ∑ i, ∑ j, ‖A i j * WithLp.ofLp x j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mulVec, dotProduct,
        norm_sum_sq_eq_sum_norm_sq_of_sparse]
      intro j k hj hk
      apply hrow i j k
      · intro hzero
        rw [hzero, zero_mul] at hj
        exact hj rfl
      · intro hzero
        rw [hzero, zero_mul] at hk
        exact hk rfl
    _ = ∑ j, ∑ i, ‖A i j * WithLp.ofLp x j‖ ^ 2 :=
      Finset.sum_comm
    _ ≤ ∑ j, ‖WithLp.ofLp x j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : ∃ i, A i j ≠ 0
      · obtain ⟨i, hi⟩ := h
        have hzero : ∀ k, k ≠ i → A k j = 0 := by
          intro k hki
          by_contra hk
          exact hki (hcol k i j hk hi)
        rw [Finset.sum_eq_single i]
        · rw [norm_mul, mul_pow]
          calc
            ‖A i j‖ ^ 2 * ‖WithLp.ofLp x j‖ ^ 2 ≤
                1 * ‖WithLp.ofLp x j‖ ^ 2 := by
              apply mul_le_mul_of_nonneg_right
              · exact pow_le_one₀ (norm_nonneg _) (hentry i j)
              · positivity
            _ = ‖WithLp.ofLp x j‖ ^ 2 := one_mul _
        · intro k _ hki
          rw [hzero k hki, zero_mul]
          simp
        · simp
      · push Not at h
        simp [h]

end SparseMatrix

section OrderedCoefficient

/-- A nonzero ordered coefficient determines the corresponding successful
Boolean reset/star support step.  Only this direction is needed for the norm
bound. -/
theorem orderedCoefficient_ne_zero_imp_step
    {d : ℕ} (q : ExteriorDegree (d + 1))
    (ell : ResetLabel (d + 1))
    (B A : ExteriorIndex (d + 1) q)
    (hne : orderedCoefficient d q ell B A ≠ 0) :
    ResetWord.step (supportLabel ell) (exteriorState A) =
      some (exteriorState B) := by
  cases ell with
  | none =>
      exact (rowFreeCompound_finLeftShift_ne_zero_iff_step_star q B A).mp hne
  | some j =>
      apply rowMinorCoefficient_finLeftShift_ne_zero_imp_step_reset q j B A
      simpa [orderedCoefficient] using hne

/-- Every ordered reset/star coefficient matrix is a contraction for the
complex Euclidean operator norm. -/
theorem orderedCoefficient_l2_opNorm_le_one
    (d : ℕ) (q : ExteriorDegree (d + 1))
    (ell : ResetLabel (d + 1)) :
    ‖orderedCoefficient d q ell‖ ≤ 1 := by
  apply l2_opNorm_le_one_of_row_col_sparse_of_entry_norm_le_one
  · intro B A₁ A₂ h₁ h₂
    apply exteriorState_injective
    exact ResetWord.step_some_injective
      (orderedCoefficient_ne_zero_imp_step q ell B A₁ h₁)
      (orderedCoefficient_ne_zero_imp_step q ell B A₂ h₂)
  · intro B₁ B₂ A h₁ h₂
    apply exteriorState_injective
    exact Option.some.inj
      ((orderedCoefficient_ne_zero_imp_step q ell B₁ A h₁).symm.trans
        (orderedCoefficient_ne_zero_imp_step q ell B₂ A h₂))
  · intro B A
    by_cases hne : orderedCoefficient d q ell B A ≠ 0
    · rw [norm_orderedCoefficient_eq_one_of_ne_zero d q ell B A hne]
    · have hz : orderedCoefficient d q ell B A = 0 := not_ne_iff.mp hne
      rw [hz, norm_zero]
      norm_num

end OrderedCoefficient

end CircularLawSection4
