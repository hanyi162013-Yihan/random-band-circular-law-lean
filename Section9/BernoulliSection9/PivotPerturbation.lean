import BernoulliSection9.InterfaceControl
import BernoulliSection9.SingularValueMinMax

/-!
# Stability of the RRQR pivot under the packet perturbation

This module formalizes the elementary `‖K⁻¹ Delta‖ <= 1/2` argument used in
(9.18): `I + K⁻¹ Delta` has bottom singular value at least `1/2`, hence its
determinant has modulus at least `2^{-r}`.
-/

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

/-- A matrix within operator-norm `1/2` of the identity has bottom singular
value at least `1/2`. -/
theorem half_le_matrixSMin_one_add_of_norm_le_half
    {n : Nat} (hn : 0 < n) (B : Matrix (Fin n) (Fin n) Complex)
    (hB : ‖B‖ <= (2 : Real)⁻¹) :
    (2 : Real)⁻¹ <= matrixSMin (1 + B) := by
  let T := (1 + B).toEuclideanLin
  let i : Fin (Module.finrank Complex (EuclideanSpace Complex (Fin n))) :=
    ⟨n - 1, by simp; omega⟩
  have hlower : (2 : Real)⁻¹ <= T.singularValues i := by
    apply le_singularValue_of_submodule_lower_bound T i
      (⊤ : Submodule Complex (EuclideanSpace Complex (Fin n)))
      (2 : Real)⁻¹
    · calc
        Module.finrank Complex
            (⊤ : Submodule Complex (EuclideanSpace Complex (Fin n))) = n := by
          rw [finrank_top, finrank_euclideanSpace_fin]
        _ = (n - 1) + 1 := by omega
        _ = (i : Nat) + 1 := by rfl
    · intro x hx
      have hBx : ‖B.toEuclideanLin x‖ <= ‖B‖ * ‖x‖ := by
        change ‖((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := Complex)) B x)‖ <=
          ‖B‖ * ‖x‖
        exact ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := Complex)) B).le_opNorm x
      have hxsplit :
          x = T x - B.toEuclideanLin x := by
        change x = (Matrix.toEuclideanLin (1 + B)) x -
          Matrix.toEuclideanLin B x
        simp
      have hxnorm : ‖x‖ <= ‖T x‖ + ‖B.toEuclideanLin x‖ := by
        calc
          ‖x‖ = ‖T x - B.toEuclideanLin x‖ := congrArg norm hxsplit
          _ <= ‖T x‖ + ‖B.toEuclideanLin x‖ := norm_sub_le _ _
      have hBhalf : ‖B.toEuclideanLin x‖ <= (2 : Real)⁻¹ * ‖x‖ :=
        hBx.trans (mul_le_mul_of_nonneg_right hB (norm_nonneg x))
      norm_num at hBhalf ⊢
      linarith
  simpa [matrixSMin, ne_of_gt hn, matrixSingularValue, T, i] using hlower

/-- The determinant half-bound for a perturbation of the identity. -/
theorem half_pow_le_norm_det_one_add_of_norm_le_half
    {n : Nat} (hn : 0 < n) (B : Matrix (Fin n) (Fin n) Complex)
    (hB : ‖B‖ <= (2 : Real)⁻¹) :
    (2 : Real)⁻¹ ^ n <= ‖(1 + B).det‖ := by
  exact pow_le_norm_det_of_le_matrixSMin hn (1 + B) (by positivity)
    (half_le_matrixSMin_one_add_of_norm_le_half hn B hB)

/-- The corresponding inverse bound `‖(I+B)⁻¹‖ <= 2`. -/
theorem norm_inv_one_add_le_two_of_norm_le_half
    {n : Nat} (hn : 0 < n) (B : Matrix (Fin n) (Fin n) Complex)
    (hB : ‖B‖ <= (2 : Real)⁻¹) :
    ‖(1 + B)⁻¹‖ <= 2 := by
  have h := norm_nonsing_inv_le_inv_of_le_matrixSMin hn (1 + B)
    (s := (2 : Real)⁻¹) (by norm_num)
    (half_le_matrixSMin_one_add_of_norm_le_half hn B hB)
  norm_num at h ⊢
  exact h

/-- Quantitative pivot determinant stability in the exact form used in
(9.18). -/
theorem pivot_add_det_lower_of_inv_mul_norm_le_half
    {n : Nat} (hn : 0 < n)
    (K Delta : Matrix (Fin n) (Fin n) Complex)
    (hK : IsUnit K.det)
    (hsmall : ‖K⁻¹ * Delta‖ <= (2 : Real)⁻¹) :
    (2 : Real)⁻¹ ^ n * ‖K.det‖ <= ‖(K + Delta).det‖ := by
  have hfactor : K + Delta = K * (1 + K⁻¹ * Delta) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc,
      K.mul_nonsing_inv hK, Matrix.one_mul]
  rw [hfactor, Matrix.det_mul, norm_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
    (half_pow_le_norm_det_one_add_of_norm_le_half hn (K⁻¹ * Delta) hsmall)
    (norm_nonneg K.det)

/-- Stability of the pivot inverse, the other estimate used in (9.22). -/
theorem norm_pivot_add_inv_le_two_mul_of_inv_mul_norm_le_half
    {n : Nat} (hn : 0 < n)
    (K Delta : Matrix (Fin n) (Fin n) Complex)
    (hK : IsUnit K.det)
    (hsmall : ‖K⁻¹ * Delta‖ <= (2 : Real)⁻¹) :
    ‖(K + Delta)⁻¹‖ <= 2 * ‖K⁻¹‖ := by
  let A : Matrix (Fin n) (Fin n) Complex := 1 + K⁻¹ * Delta
  have hAhalf : (2 : Real)⁻¹ ^ n <= ‖A.det‖ :=
    half_pow_le_norm_det_one_add_of_norm_le_half hn (K⁻¹ * Delta) hsmall
  have hAdetNorm : 0 < ‖A.det‖ :=
    (pow_pos (by norm_num : 0 < (2 : Real)⁻¹) n).trans_le hAhalf
  have hA : IsUnit A.det :=
    isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hAdetNorm)
  have hfactor : K + Delta = K * A := by
    dsimp [A]
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc,
      K.mul_nonsing_inv hK, Matrix.one_mul]
  have hleft : (A⁻¹ * K⁻¹) * (K + Delta) = 1 := by
    rw [hfactor, Matrix.mul_assoc, ← Matrix.mul_assoc K⁻¹ K A,
      K.nonsing_inv_mul hK, Matrix.one_mul, A.nonsing_inv_mul hA]
  have hinv : (K + Delta)⁻¹ = A⁻¹ * K⁻¹ :=
    Matrix.inv_eq_left_inv hleft
  rw [hinv]
  exact (Matrix.l2_opNorm_mul A⁻¹ K⁻¹).trans
    (mul_le_mul_of_nonneg_right
      (norm_inv_one_add_le_two_of_norm_le_half hn (K⁻¹ * Delta) hsmall)
      (norm_nonneg K⁻¹))

/-- The same statement with a supplied lower bound on the unperturbed pivot
determinant. -/
theorem pivot_add_det_lower
    {n : Nat} (hn : 0 < n)
    (K Delta : Matrix (Fin n) (Fin n) Complex)
    (hK : IsUnit K.det)
    (hsmall : ‖K⁻¹ * Delta‖ <= (2 : Real)⁻¹)
    {pivotLower : Real} (hpivotLower : 0 <= pivotLower)
    (hpivot : pivotLower <= ‖K.det‖) :
    (2 : Real)⁻¹ ^ n * pivotLower <= ‖(K + Delta).det‖ := by
  exact (mul_le_mul_of_nonneg_left hpivot (by positivity)).trans
    (pivot_add_det_lower_of_inv_mul_norm_le_half hn K Delta hK hsmall)

end BernoulliSection9
