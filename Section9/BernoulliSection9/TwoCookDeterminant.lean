import BernoulliSection9.InterfaceControl
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Deterministic algebra for the two Cook squares

This is the second Schur-complement step in (9.27)--(9.35).  The results below
turn two bottom-singular-value bounds into a determinant bound for the full
residual block and give the polynomial norm estimate for the deformation in
the second Cook application.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

variable {p q : Type*}
variable [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

/-- The second Schur complement after the first Cook square has been
revealed. -/
def secondCookSchur
    (A : Matrix p p Complex) (B : Matrix p q Complex)
    (C : Matrix q p Complex) (D : Matrix q q Complex) :
    Matrix q q Complex :=
  D - C * A⁻¹ * B

/-- Termwise norm control of the second Schur deformation. -/
theorem secondCookSchur_norm_le
    (A : Matrix p p Complex) (B : Matrix p q Complex)
    (C : Matrix q p Complex) (D : Matrix q q Complex) :
    ‖secondCookSchur A B C D‖ <=
      ‖D‖ + ‖C‖ * ‖A⁻¹‖ * ‖B‖ := by
  calc
    ‖secondCookSchur A B C D‖ = ‖D - C * A⁻¹ * B‖ := rfl
    _ <= ‖D‖ + ‖C * A⁻¹ * B‖ := norm_sub_le _ _
    _ <= ‖D‖ + ‖C‖ * ‖A⁻¹‖ * ‖B‖ := by
      gcongr
      exact (Matrix.l2_opNorm_mul (C * A⁻¹) B).trans
        (mul_le_mul_of_nonneg_right
          (Matrix.l2_opNorm_mul C A⁻¹) (norm_nonneg B))

/-- Scalar substitution form used to produce a fixed power of `W` for the
second deformation. -/
theorem secondCookSchur_norm_le_of_bounds
    (A : Matrix p p Complex) (B : Matrix p q Complex)
    (C : Matrix q p Complex) (D : Matrix q q Complex)
    {aInv bNorm cNorm dNorm : Real}
    (haInv : ‖A⁻¹‖ <= aInv) (hb : ‖B‖ <= bNorm)
    (hc : ‖C‖ <= cNorm) (hd : ‖D‖ <= dNorm)
    (haInv0 : 0 <= aInv) (hb0 : 0 <= bNorm) (hc0 : 0 <= cNorm) :
    ‖secondCookSchur A B C D‖ <=
      dNorm + cNorm * aInv * bNorm := by
  refine (secondCookSchur_norm_le A B C D).trans ?_
  gcongr

/-- Literal determinant factorization through the first Cook square, using
mathlib's nonsingular inverse convention. -/
theorem det_fromBlocks_eq_first_mul_secondCookSchur
    (A : Matrix p p Complex) (B : Matrix p q Complex)
    (C : Matrix q p Complex) (D : Matrix q q Complex)
    (hA : IsUnit A.det) :
    (Matrix.fromBlocks A B C D).det =
      A.det * (secondCookSchur A B C D).det := by
  let ⟨iA⟩ := (A.isUnit_iff_isUnit_det.mpr hA).nonempty_invertible
  letI : Invertible A := iA
  simpa [secondCookSchur, Matrix.invOf_eq_nonsing_inv] using
    Matrix.det_fromBlocks₁₁ A B C D

/-- Two least-singular-value lower bounds yield the residual determinant
lower bound used in (9.35). -/
theorem twoCook_det_lower
    {n1 n2 : Nat}
    (A : Matrix (Fin n1) (Fin n1) Complex)
    (B : Matrix (Fin n1) (Fin n2) Complex)
    (C : Matrix (Fin n2) (Fin n1) Complex)
    (D : Matrix (Fin n2) (Fin n2) Complex)
    (hn1 : 0 < n1) (hn2 : 0 < n2)
    {epsilon1 epsilon2 : Real}
    (hepsilon1 : 0 < epsilon1) (hepsilon2 : 0 <= epsilon2)
    (hAmin : epsilon1 <= matrixSMin A)
    (hSchurMin : epsilon2 <= matrixSMin (secondCookSchur A B C D)) :
    epsilon1 ^ n1 * epsilon2 ^ n2 <=
      ‖(Matrix.fromBlocks A B C D).det‖ := by
  have hAdetNorm : 0 < ‖A.det‖ :=
    lt_of_lt_of_le (pow_pos hepsilon1 n1)
      (pow_le_norm_det_of_le_matrixSMin hn1 A hepsilon1.le hAmin)
  have hAunit : IsUnit A.det :=
    isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hAdetNorm)
  rw [det_fromBlocks_eq_first_mul_secondCookSchur A B C D hAunit,
    norm_mul]
  exact mul_le_mul
    (pow_le_norm_det_of_le_matrixSMin hn1 A hepsilon1.le hAmin)
    (pow_le_norm_det_of_le_matrixSMin hn2
      (secondCookSchur A B C D) hepsilon2 hSchurMin)
    (pow_nonneg hepsilon2 n2) (norm_nonneg A.det)

end BernoulliSection9
