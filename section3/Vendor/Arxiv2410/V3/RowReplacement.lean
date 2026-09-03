/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/RowReplacement.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.HermitianStieltjes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic row replacement for v3 Proposition 3.4

This file proves the finite-dimensional algebra behind proof step (3) of
arXiv:2410.16457v3.  In particular, replacing one row of `X` changes its shifted
Hermitization by rank at most two.  No probability or concentration theorem is
used in these results.
-/

namespace Arxiv2410V3

open Matrix Complex
open scoped BigOperators

/-- Two square matrices differ only in row `i`.  This is the deterministic
coordinate replacement relation used in v3 Proposition 3.4, proof step (3). -/
def DiffersOnlyOnRow {n : ℕ} (X X' : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Prop :=
  ∀ k j, k ≠ i → X k j = X' k j

/-- A basis vector in the upper half of the Hermitization index. -/
private def upperBasis {n : ℕ} (i : Fin n) : HermitizationIndex n → ℂ
  | Sum.inl k => if k = i then 1 else 0
  | Sum.inr _ => 0

/-- A row embedded into the upper-right block. -/
private def rowRight {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    HermitizationIndex n → ℂ
  | Sum.inl _ => 0
  | Sum.inr j => R i j

/-- The conjugate row embedded into the lower-left block. -/
private def conjugateRowBottom {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    HermitizationIndex n → ℂ
  | Sum.inl _ => 0
  | Sum.inr j => star (R i j)

/-- Matrix rank is subadditive.  This elementary lemma is included here because
the row-replacement step (3) decomposes the perturbation into two rank-one terms. -/
theorem matrix_rank_add_le
    {R m n : Type*} [Field R] [Fintype n]
    (A B : Matrix m n R) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- A finite-dimensional trace/rank estimate used in v3 Proposition 3.4,
proof step (3).  It is proved by taking an orthonormal basis adapted to
`ker T ⊕ (ker T)ᗮ`; only the orthogonal-complement summands contribute to
the trace. -/
theorem norm_trace_le_finrank_range_mul_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →L[ℂ] E) :
    ‖T.toLinearMap.trace ℂ E‖ ≤
      (Module.finrank ℂ T.toLinearMap.range : ℝ) * ‖T‖ := by
  classical
  let K : Submodule ℂ E := T.toLinearMap.ker
  let bK : OrthonormalBasis (Fin (Module.finrank ℂ K)) ℂ K :=
    stdOrthonormalBasis ℂ K
  let bP : OrthonormalBasis (Fin (Module.finrank ℂ Kᗮ)) ℂ Kᗮ :=
    stdOrthonormalBasis ℂ Kᗮ
  let b : OrthonormalBasis
      (Fin (Module.finrank ℂ K) ⊕ Fin (Module.finrank ℂ Kᗮ)) ℂ E :=
    (bK.prod bP).map K.orthogonalDecomposition.symm
  rw [LinearMap.trace_eq_sum_inner T.toLinearMap b, Fintype.sum_sum_type]
  have hbK (i : Fin (Module.finrank ℂ K)) : b (Sum.inl i) = (bK i : E) := by
    simp [b, bK, bP, K]
  have hbP (i : Fin (Module.finrank ℂ Kᗮ)) : b (Sum.inr i) = (bP i : E) := by
    simp [b, bK, bP, K]
  have hker (i : Fin (Module.finrank ℂ K)) : T (b (Sum.inl i)) = 0 := by
    rw [hbK]
    exact (bK i).property
  rw [Finset.sum_eq_zero (fun i _ ↦ by simp [hker i]), zero_add]
  calc
    ‖∑ i, inner ℂ (b (Sum.inr i)) (T (b (Sum.inr i)))‖ ≤
        ∑ i, ‖inner ℂ (b (Sum.inr i)) (T (b (Sum.inr i)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin (Module.finrank ℂ Kᗮ), ‖T‖ := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖inner ℂ (b (Sum.inr i)) (T (b (Sum.inr i)))‖ ≤
            ‖b (Sum.inr i)‖ * ‖T (b (Sum.inr i))‖ := norm_inner_le_norm _ _
        _ = ‖T (b (Sum.inr i))‖ := by rw [b.orthonormal.1]; simp
        _ ≤ ‖T‖ := by
          simpa [b.orthonormal.1] using T.le_opNorm (b (Sum.inr i))
    _ = (Module.finrank ℂ Kᗮ : ℝ) * ‖T‖ := by simp
    _ = (Module.finrank ℂ T.toLinearMap.range : ℝ) * ‖T‖ := by
      have hn : Module.finrank ℂ Kᗮ = Module.finrank ℂ T.toLinearMap.range := by
        have hrank := T.toLinearMap.finrank_range_add_finrank_ker
        have horth := K.finrank_add_finrank_orthogonal
        dsimp [K] at horth ⊢
        omega
      rw [hn]

section L2Operator

open scoped Matrix.Norms.L2Operator

/-- Matrix form of the preceding trace/rank estimate, with the `L²` operator
norm.  This is the deterministic trace estimate used in v3 Proposition 3.4,
proof step (3). -/
theorem norm_matrix_trace_le_rank_mul_l2OpNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    ‖Matrix.trace A‖ ≤ (A.rank : ℝ) * ‖A‖ := by
  let T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A
  have h := norm_trace_le_finrank_range_mul_norm T
  have hrank : A.rank = Module.finrank ℂ T.toLinearMap.range := by
    unfold T
    change A.rank = Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin A))
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.rank_eq_finrank_range_toLin A
      (EuclideanSpace.basisFun ι ℂ).toBasis (EuclideanSpace.basisFun ι ℂ).toBasis
  have htrace : T.toLinearMap.trace ℂ (EuclideanSpace ℂ ι) = Matrix.trace A := by
    simp [T, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
      Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [htrace, ← hrank] at h
  simpa [T, Matrix.cstar_norm_def] using h

/-- v3 Proposition 3.4, proof step (3): the `L²` operator norm of a
Hermitian resolvent in the upper half-plane is at most `1 / Im eta`. -/
theorem hermitian_resolvent_l2OpNorm_le_inv_im
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) {eta : ℂ} (heta : 0 < eta.im) :
    ‖(A - eta • (1 : Matrix ι ι ℂ))⁻¹‖ ≤ eta.im⁻¹ := by
  rw [shiftedHermitian_inv_spectral_decomposition A hA heta]
  change ‖(hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i ↦ ((hA.eigenvalues i : ℂ) - eta)⁻¹) *
      (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ‖ ≤ eta.im⁻¹
  change ‖(hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i ↦ ((hA.eigenvalues i : ℂ) - eta)⁻¹) *
      star (hA.eigenvectorUnitary : Matrix ι ι ℂ)‖ ≤ eta.im⁻¹
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr heta.le)).2
  intro i
  rw [norm_inv]
  have hdist : eta.im ≤ ‖(hA.eigenvalues i : ℂ) - eta‖ := by
    calc
      eta.im = |(((hA.eigenvalues i : ℂ) - eta).im)| := by
        simp [abs_of_pos heta]
      _ ≤ ‖(hA.eigenvalues i : ℂ) - eta‖ := Complex.abs_im_le_norm _
  have hnorm : 0 < ‖(hA.eigenvalues i : ℂ) - eta‖ := heta.trans_le hdist
  exact (inv_le_inv₀ hnorm heta).2 hdist

/-- The shifted Hermitian matrix is invertible off the real axis.  This is the
algebraic invertibility fact used in the resolvent identity of v3 proof step (3). -/
theorem shiftedHermitian_isUnit_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) {eta : ℂ} (heta : 0 < eta.im) :
    IsUnit (A - eta • (1 : Matrix ι ι ℂ)).det := by
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  let d : ι → ℂ := fun i ↦ (hA.eigenvalues i : ℂ) - eta
  let dinv : ι → ℂ := fun i ↦ (d i)⁻¹
  apply Matrix.isUnit_det_of_right_inverse (B := U * Matrix.diagonal dinv * Uᴴ)
  rw [shiftedHermitian_spectral_decomposition A hA eta]
  change (U * Matrix.diagonal d * Uᴴ) *
      (U * Matrix.diagonal dinv * Uᴴ) = 1
  have hdne (i : ι) : d i ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [d] at him
    linarith
  have hdiag : Matrix.diagonal d * Matrix.diagonal dinv =
      (1 : Matrix ι ι ℂ) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d, dinv, hdne]
    · simp [hij]
  have hstarunit : Uᴴ * U = 1 := by
    change star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1
    exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hunitstar : U * Uᴴ = 1 := by
    change (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      star (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1
    exact Unitary.coe_mul_star_self hA.eigenvectorUnitary
  calc
    (U * Matrix.diagonal d * Uᴴ) * (U * Matrix.diagonal dinv * Uᴴ) =
        U * Matrix.diagonal d * (Uᴴ * U) * Matrix.diagonal dinv * Uᴴ := by
      noncomm_ring
    _ = U * Matrix.diagonal d * Matrix.diagonal dinv * Uᴴ := by
      rw [hstarunit]
      simp
    _ = U * (Matrix.diagonal d * Matrix.diagonal dinv) * Uᴴ := by noncomm_ring
    _ = U * Uᴴ := by rw [hdiag, Matrix.mul_one]
    _ = 1 := hunitstar

/-- Resolvent identity for two Hermitian matrices, used in v3 Proposition 3.4,
proof step (3). -/
theorem hermitian_resolvent_sub_resolvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    {eta : ℂ} (heta : 0 < eta.im) :
    (A - eta • (1 : Matrix ι ι ℂ))⁻¹ -
        (B - eta • (1 : Matrix ι ι ℂ))⁻¹ =
      (A - eta • (1 : Matrix ι ι ℂ))⁻¹ * (B - A) *
        (B - eta • (1 : Matrix ι ι ℂ))⁻¹ := by
  let SA := A - eta • (1 : Matrix ι ι ℂ)
  let SB := B - eta • (1 : Matrix ι ι ℂ)
  have hunitA : IsUnit SA.det := shiftedHermitian_isUnit_det A hA heta
  have hunitB : IsUnit SB.det := shiftedHermitian_isUnit_det B hB heta
  change SA⁻¹ - SB⁻¹ = SA⁻¹ * (B - A) * SB⁻¹
  have hBA : B - A = SB - SA := by simp [SA, SB]
  rw [hBA, Matrix.mul_sub, Matrix.sub_mul]
  rw [Matrix.mul_assoc, SB.mul_nonsing_inv hunitB, Matrix.mul_one]
  rw [SA.nonsing_inv_mul hunitA, Matrix.one_mul]

/-- The resolvent difference has no larger rank than the Hermitian perturbation;
this is the low-rank part of v3 Proposition 3.4, proof step (3). -/
theorem rank_hermitian_resolvent_sub_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    {eta : ℂ} (heta : 0 < eta.im) :
    ((A - eta • (1 : Matrix ι ι ℂ))⁻¹ -
      (B - eta • (1 : Matrix ι ι ℂ))⁻¹).rank ≤ (B - A).rank := by
  rw [hermitian_resolvent_sub_resolvent A B hA hB heta]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end L2Operator

/-- v3 Proposition 3.4, proof step (3), algebraic core: the difference of two
shifted Hermitizations whose underlying matrices differ in one row is the sum
of two explicit rank-one matrices. -/
theorem hermitization_sub_eq_two_rank_one {n : ℕ}
    (X X' : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (i : Fin n)
    (hrow : DiffersOnlyOnRow X X' i) :
    hermitization X z - hermitization X' z =
      Matrix.vecMulVec (upperBasis i) (rowRight (X - X') i) +
      Matrix.vecMulVec (conjugateRowBottom (X - X') i) (upperBasis i) := by
  classical
  ext a b
  rcases a with k | k <;> rcases b with j | j
  · simp [hermitization, shiftedMatrix, upperBasis, rowRight, conjugateRowBottom,
      Matrix.vecMulVec]
  · by_cases hki : k = i
    · subst k
      simp [hermitization, shiftedMatrix, upperBasis, rowRight, conjugateRowBottom,
        Matrix.vecMulVec]
    · have h := hrow k j hki
      simp [hermitization, shiftedMatrix, upperBasis, rowRight, conjugateRowBottom,
        Matrix.vecMulVec, hki, h]
  · by_cases hji : j = i
    · subst j
      simp [hermitization, shiftedMatrix, upperBasis, rowRight, conjugateRowBottom,
        Matrix.vecMulVec]
    · have h := hrow j k hji
      simp [hermitization, shiftedMatrix, upperBasis, rowRight, conjugateRowBottom,
        Matrix.vecMulVec, hji, h]
  · simp [hermitization, shiftedMatrix, upperBasis, rowRight, conjugateRowBottom,
      Matrix.vecMulVec]

/-- v3 Proposition 3.4, proof step (3): replacing one row of `X` changes the
`2n × 2n` shifted Hermitization by rank at most two. -/
theorem rank_hermitization_sub_le_two {n : ℕ}
    (X X' : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (i : Fin n)
    (hrow : DiffersOnlyOnRow X X' i) :
    (hermitization X z - hermitization X' z).rank ≤ 2 := by
  rw [hermitization_sub_eq_two_rank_one X X' z i hrow]
  refine (matrix_rank_add_le _ _).trans ?_
  have h₁ := Matrix.rank_vecMulVec_le (upperBasis i) (rowRight (X - X') i)
  have h₂ := Matrix.rank_vecMulVec_le (conjugateRowBottom (X - X') i) (upperBasis i)
  omega

end Arxiv2410V3
