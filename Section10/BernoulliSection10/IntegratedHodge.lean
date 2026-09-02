import BernoulliLinearAlgebra.ConcreteClearedTransfer
import BernoulliLinearAlgebra.JacobiConcrete
import Mathlib.Tactic

/-!
# Deterministic one-site Hodge identities

This file supplies the certificate-free deterministic identities used in
Lemma 10.6.  In particular, it identifies the inverse of a companion transfer,
proves that taking a compound commutes with nonsingular inversion, and then
derives the exact inverse norm of the determinant-cleared exterior operator.
The probabilistic integrability envelope is added on top of these identities.
-/

open scoped Matrix Matrix.Norms.Frobenius

noncomputable section

set_option maxHeartbeats 800000

namespace BernoulliSection10

open Matrix
open BernoulliLinearAlgebra

section CompoundInverse

variable {R : Type*} [CommRing R]
variable {i : Type*} [Fintype i] [DecidableEq i] [LinearOrder i]

/-- Exterior functoriality sends the identity matrix to the identity in every
degree, including degrees above the ambient dimension. -/
@[simp] theorem compound_one (k : ℕ) :
    compound k (1 : Matrix i i R) = 1 := by
  unfold compound
  rw [Matrix.toLin'_one, exteriorPower.map_id, LinearMap.toMatrix_id]

/-- On the nonsingular locus, taking a compound commutes with the matrix
inverse.  This is proved from functoriality, so no determinant formula for a
compound matrix is needed. -/
theorem compound_nonsing_inv (A : Matrix i i R) (hA : IsUnit A.det)
    (k : ℕ) :
    (compound k A)⁻¹ = compound k A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [← compound_mul, Matrix.nonsing_inv_mul A hA, compound_one]

end CompoundInverse

section CompanionInverse

variable {W : Type*} [Fintype W] [LinearOrder W]

local instance integratedHodgeSumLinearOrder : LinearOrder (W ⊕ W) :=
  BernoulliLinearAlgebra.clearedStepCompoundSumLinearOrder

/-- The literal inverse companion matrix. -/
def stepTransferInverse (B D C : Matrix W W ℂ) :
    Matrix (W ⊕ W) (W ⊕ W) ℂ :=
  Matrix.fromBlocks 0 1 (-(C⁻¹ * B)) (-(C⁻¹ * D))

/-- The coordinate swap on the two transfer blocks. -/
def twoBlockSwap : Matrix (W ⊕ W) (W ⊕ W) ℂ :=
  Matrix.fromBlocks 0 1 1 0

@[simp] theorem twoBlockSwap_mul_self :
    (twoBlockSwap (W := W)) * twoBlockSwap = 1 := by
  simp [twoBlockSwap, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

/-- The block swap has determinant of unit modulus.  This avoids choosing
the parity sign of its determinant. -/
theorem norm_twoBlockSwap_det :
    ‖(twoBlockSwap (W := W)).det‖ = 1 := by
  have hdet :
      (twoBlockSwap (W := W)).det * (twoBlockSwap (W := W)).det = 1 := by
    rw [← Matrix.det_mul, twoBlockSwap_mul_self, Matrix.det_one]
  have hnorm := congrArg norm hdet
  rw [norm_mul, norm_one] at hnorm
  nlinarith [norm_nonneg (twoBlockSwap (W := W)).det]

/-- The displayed inverse is a left inverse of the one-step transfer. -/
theorem stepTransferInverse_mul (B D C : Matrix W W ℂ)
    (hB : IsUnit B.det) (hC : IsUnit C.det) :
    stepTransferInverse B D C * stepTransfer B D C = 1 := by
  have hBinv : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  have hCinv : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C hC
  have hBD : (C⁻¹ * B) * (B⁻¹ * D) = C⁻¹ * D := by
    calc
      (C⁻¹ * B) * (B⁻¹ * D) = C⁻¹ * ((B * B⁻¹) * D) := by
        simp only [Matrix.mul_assoc]
      _ = C⁻¹ * D := by rw [hBinv, Matrix.one_mul]
  have hBC : (C⁻¹ * B) * (B⁻¹ * C) = 1 := by
    calc
      (C⁻¹ * B) * (B⁻¹ * C) = C⁻¹ * ((B * B⁻¹) * C) := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBinv, Matrix.one_mul, hCinv]
  rw [stepTransfer_eq_companion B D C hB]
  simp [stepTransferInverse, Matrix.fromBlocks_multiply, hBD, hBC,
    ← Matrix.fromBlocks_one]

/-- The displayed inverse is also a right inverse. -/
theorem stepTransfer_mul_stepTransferInverse (B D C : Matrix W W ℂ)
    (hB : IsUnit B.det) (hC : IsUnit C.det) :
    stepTransfer B D C * stepTransferInverse B D C = 1 := by
  have hCinv : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hC
  have hBinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hCB : (B⁻¹ * C) * (C⁻¹ * B) = 1 := by
    calc
      (B⁻¹ * C) * (C⁻¹ * B) = B⁻¹ * ((C * C⁻¹) * B) := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCinv, Matrix.one_mul, hBinv]
  have hCD : (B⁻¹ * C) * (C⁻¹ * D) = B⁻¹ * D := by
    calc
      (B⁻¹ * C) * (C⁻¹ * D) = B⁻¹ * ((C * C⁻¹) * D) := by
        simp only [Matrix.mul_assoc]
      _ = B⁻¹ * D := by rw [hCinv, Matrix.one_mul]
  rw [stepTransfer_eq_companion B D C hB]
  simp [stepTransferInverse, Matrix.fromBlocks_multiply, hCB, hCD,
    ← Matrix.fromBlocks_one]

/-- Invertibility of both extreme physical blocks is exactly what is needed
to make the transfer relation invertible. -/
theorem stepTransfer_det_isUnit (B D C : Matrix W W ℂ)
    (hB : IsUnit B.det) (hC : IsUnit C.det) :
    IsUnit (stepTransfer B D C).det :=
  Matrix.isUnit_det_of_left_inverse (stepTransferInverse_mul B D C hB hC)

/-- The nonsingular inverse of the transfer is the literal inverse companion
matrix. -/
theorem stepTransfer_nonsing_inv (B D C : Matrix W W ℂ)
    (hB : IsUnit B.det) (hC : IsUnit C.det) :
    (stepTransfer B D C)⁻¹ = stepTransferInverse B D C := by
  exact Matrix.inv_eq_left_inv (stepTransferInverse_mul B D C hB hC)

/-- Determinant modulus of the companion transfer.  The middle block `D`
drops out, and the two interface determinants appear in the exact ratio
used in the paper's Hodge identity. -/
theorem norm_stepTransfer_det_eq
    (B D C : Matrix W W ℂ) (hB : IsUnit B.det) :
    ‖(stepTransfer B D C).det‖ = ‖B.det‖⁻¹ * ‖C.det‖ := by
  let Q : Matrix W W ℂ := -(B⁻¹ * C)
  have htri :
      stepTransfer B D C * twoBlockSwap =
        Matrix.fromBlocks Q (-(B⁻¹ * D)) 0 1 := by
    rw [stepTransfer_eq_companion B D C hB]
    simp [Q, twoBlockSwap, Matrix.fromBlocks_multiply]
  have hdet := congrArg Matrix.det htri
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one] at hdet
  have hnorm := congrArg norm hdet
  rw [norm_mul, norm_twoBlockSwap_det, mul_one] at hnorm
  rw [hnorm]
  simp only [Q, Matrix.det_neg, Matrix.det_mul,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv, norm_mul]
  rw [norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv]

/-- The determinant-cleared exterior operator is invertible in every
admissible degree. -/
theorem clearedStepCompound_det_isUnit
    (k : ℕ) (hk : k ≤ Fintype.card (W ⊕ W))
    (B D C : Matrix W W ℂ)
    (hB : IsUnit B.det) (hC : IsUnit C.det) :
    IsUnit (clearedStepCompound k B D C).det := by
  have hclear :=
    clearedStepCompound_eq_det_smul_compound_stepTransfer k hk B D C hB
  have hdet := congrArg Matrix.det hclear
  rw [hdet]
  apply Matrix.isUnit_det_of_left_inverse
  let T := stepTransfer B D C
  let L : Matrix (Set.powersetCard (W ⊕ W) k)
      (Set.powersetCard (W ⊕ W) k) ℂ :=
    B.det⁻¹ • compound k T⁻¹
  change L * (B.det • compound k T) = 1
  simp only [L, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← compound_mul, Matrix.nonsing_inv_mul T
    (stepTransfer_det_isUnit B D C hB hC), compound_one]
  simp [isUnit_iff_ne_zero.mp hB]

/-- Exact inverse formula for the determinant-cleared exterior operator. -/
theorem clearedStepCompound_nonsing_inv
    (k : ℕ) (hk : k ≤ Fintype.card (W ⊕ W))
    (B D C : Matrix W W ℂ)
    (hB : IsUnit B.det) (hC : IsUnit C.det) :
    (clearedStepCompound k B D C)⁻¹ =
      B.det⁻¹ • compound k (stepTransfer B D C)⁻¹ := by
  have hclear :=
    clearedStepCompound_eq_det_smul_compound_stepTransfer k hk B D C hB
  have hinv := congrArg Inv.inv hclear
  rw [hinv]
  apply Matrix.inv_eq_left_inv
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← compound_mul, Matrix.nonsing_inv_mul (stepTransfer B D C)
    (stepTransfer_det_isUnit B D C hB hC), compound_one]
  simp [isUnit_iff_ne_zero.mp hB]

/-- Exact Hodge identity for the inverse norm of the paper's one-site
operator `A_j^(r) = det(B_j) ∧^r T_j`.  This is the deterministic core of
equation (10.69), with all complementary-minor data discharged internally. -/
theorem clearedStepCompound_inverse_norm_eq
    (k : ℕ) (hk : k ≤ Fintype.card (W ⊕ W))
    (B D C : Matrix W W ℂ)
    (hB : IsUnit B.det) (hC : IsUnit C.det) :
    ‖(clearedStepCompound k B D C)⁻¹‖ =
      ‖B.det‖⁻¹ *
        (‖(stepTransfer B D C).det‖⁻¹ *
          ‖compound (Fintype.card (W ⊕ W) - k)
            (stepTransfer B D C)‖) := by
  rw [clearedStepCompound_nonsing_inv k hk B D C hB hC,
    norm_smul, norm_inv,
    compound_inverse_norm_eq_of_isUnit
      (stepTransfer B D C) (stepTransfer_det_isUnit B D C hB hC) k hk]

/-- Exact paper form of the one-site Hodge relation (equation (10.69)):
the inverse in degree `k` is the complementary cleared exterior norm divided
by the two physical interface determinants. -/
theorem clearedStepCompound_inverse_norm_eq_complement
    (k : ℕ) (hk : k ≤ Fintype.card (W ⊕ W))
    (B D C : Matrix W W ℂ)
    (hB : IsUnit B.det) (hC : IsUnit C.det) :
    ‖(clearedStepCompound k B D C)⁻¹‖ =
      ‖clearedStepCompound (Fintype.card (W ⊕ W) - k) B D C‖ /
        ‖B.det * C.det‖ := by
  have hBn : ‖B.det‖ ≠ 0 := norm_ne_zero_iff.mpr (isUnit_iff_ne_zero.mp hB)
  have hCn : ‖C.det‖ ≠ 0 := norm_ne_zero_iff.mpr (isUnit_iff_ne_zero.mp hC)
  rw [clearedStepCompound_inverse_norm_eq k hk B D C hB hC,
    norm_stepTransfer_det_eq B D C hB,
    clearedStepCompound_eq_det_smul_compound_stepTransfer
      (Fintype.card (W ⊕ W) - k) (Nat.sub_le _ _) B D C hB,
    norm_smul, norm_mul]
  field_simp

end CompanionInverse

end BernoulliSection10
