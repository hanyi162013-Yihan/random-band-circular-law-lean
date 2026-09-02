import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.NoncommRing
import Mathlib.Data.Complex.Basic

/-!
# Literal terminal CUR/Schur factorization

This module contains the deterministic block algebra behind (9.21) of Section
9.1.2.  It is independent of RRQR, norm estimates, and probability.  The
pivot and residual index types may be arbitrary finite types; in particular,
the empty-pivot convention is obtained by taking the pivot type to be empty.

For skeleton data

`[[K, KX], [YK, YKX + E₀]]`

and perturbation blocks `Δᵢⱼ`, the definitions of `KDelta`, `G21`, `G12`, and
`F` below are literal translations of the paper.  The main theorem
`skeleton_add_eq_CUR` proves the displayed three-factor identity, and the
remaining theorems record that the two outer factors have determinant one and
that the determinant is the product of the pivot and residual determinants.
-/

open scoped Matrix

noncomputable section

namespace BernoulliSection9

open Matrix

/-- The four matrices in an exact block skeleton decomposition.

No bounds or rank-revealing hypothesis are stored here: those belong to the
upstream RRQR construction.  This structure records only the literal algebra
used by the CUR/Schur step. -/
structure BlockSkeletonData (p q : Type*) where
  Kpiv : Matrix p p ℂ
  Xskel : Matrix p q ℂ
  Yskel : Matrix q p ℂ
  E0 : Matrix q q ℂ

section Definitions

variable {p q : Type*}
variable [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

/-- The matrix represented by exact skeleton data:
`[[K, KX], [YK, YKX + E₀]]`. -/
def skeletonMatrix (S : BlockSkeletonData p q) :
    Matrix (p ⊕ q) (p ⊕ q) ℂ :=
  Matrix.fromBlocks
    S.Kpiv
    (S.Kpiv * S.Xskel)
    (S.Yskel * S.Kpiv)
    (S.Yskel * S.Kpiv * S.Xskel + S.E0)

/-- The `(1,1)` block `Δ₁₁`. -/
def delta11 (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) : Matrix p p ℂ :=
  Delta.toBlocks₁₁

/-- The `(1,2)` block `Δ₁₂`. -/
def delta12 (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) : Matrix p q ℂ :=
  Delta.toBlocks₁₂

/-- The `(2,1)` block `Δ₂₁`. -/
def delta21 (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) : Matrix q p ℂ :=
  Delta.toBlocks₂₁

/-- The `(2,2)` block `Δ₂₂`. -/
def delta22 (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) : Matrix q q ℂ :=
  Delta.toBlocks₂₂

/-- The perturbed pivot `K_Δ = K_piv + Δ₁₁`. -/
def KDelta (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) : Matrix p p ℂ :=
  S.Kpiv + delta11 Delta

/-- The lower graph error `G₂₁ = Δ₂₁ - Y_skel Δ₁₁`. -/
def G21 (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) : Matrix q p ℂ :=
  delta21 Delta - S.Yskel * delta11 Delta

/-- The upper graph error `G₁₂ = Δ₁₂ - Δ₁₁ X_skel`. -/
def G12 (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) : Matrix p q ℂ :=
  delta12 Delta - delta11 Delta * S.Xskel

/-- The cancellation-visible residual deformation from (9.20):

`E₀ - Y Δ₁₂ - Δ₂₁ X + Y Δ₁₁ X - G₂₁ K_Δ⁻¹ G₁₂`.

In particular, the unperturbed pivot `K_piv` does not occur outside
`KDelta⁻¹`. -/
def F (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) : Matrix q q ℂ :=
  S.E0 - S.Yskel * delta12 Delta - delta21 Delta * S.Xskel +
      S.Yskel * delta11 Delta * S.Xskel -
        G21 S Delta * (KDelta S Delta)⁻¹ * G12 S Delta

/-- The determinant-one lower shear in (9.21). -/
def leftCURShear (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    Matrix (p ⊕ q) (p ⊕ q) ℂ :=
  Matrix.fromBlocks 1 0
    ((S.Yskel * S.Kpiv + delta21 Delta) * (KDelta S Delta)⁻¹) 1

/-- The block diagonal middle factor in (9.21). -/
def CURDiagonal (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    Matrix (p ⊕ q) (p ⊕ q) ℂ :=
  Matrix.fromBlocks (KDelta S Delta) 0 0 (delta22 Delta + F S Delta)

/-- The determinant-one upper shear in (9.21). -/
def rightCURShear (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    Matrix (p ⊕ q) (p ⊕ q) ℂ :=
  Matrix.fromBlocks 1
    ((KDelta S Delta)⁻¹ * (S.Kpiv * S.Xskel + delta12 Delta)) 0 1

@[simp] theorem delta11_fromBlocks
    (A : Matrix p p ℂ) (B : Matrix p q ℂ)
    (C : Matrix q p ℂ) (D : Matrix q q ℂ) :
    delta11 (Matrix.fromBlocks A B C D) = A := rfl

@[simp] theorem delta12_fromBlocks
    (A : Matrix p p ℂ) (B : Matrix p q ℂ)
    (C : Matrix q p ℂ) (D : Matrix q q ℂ) :
    delta12 (Matrix.fromBlocks A B C D) = B := rfl

@[simp] theorem delta21_fromBlocks
    (A : Matrix p p ℂ) (B : Matrix p q ℂ)
    (C : Matrix q p ℂ) (D : Matrix q q ℂ) :
    delta21 (Matrix.fromBlocks A B C D) = C := rfl

@[simp] theorem delta22_fromBlocks
    (A : Matrix p p ℂ) (B : Matrix p q ℂ)
    (C : Matrix q p ℂ) (D : Matrix q q ℂ) :
    delta22 (Matrix.fromBlocks A B C D) = D := rfl

end Definitions

section Algebra

variable {p q : Type*}
variable [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

/-- The lower off-diagonal block is `Y K_Δ + G₂₁`. -/
theorem lowerBlock_eq_Y_mul_KDelta_add_G21
    (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    S.Yskel * S.Kpiv + delta21 Delta =
      S.Yskel * KDelta S Delta + G21 S Delta := by
  simp only [KDelta, G21, Matrix.mul_add, sub_eq_add_neg]
  abel

/-- The upper off-diagonal block is `K_Δ X + G₁₂`. -/
theorem upperBlock_eq_KDelta_mul_X_add_G12
    (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    S.Kpiv * S.Xskel + delta12 Delta =
      KDelta S Delta * S.Xskel + G12 S Delta := by
  simp only [KDelta, G12, Matrix.add_mul, sub_eq_add_neg]
  abel

/-- The cancellation-visible formula `F` is exactly the Schur residual.

This is the algebraic heart of (9.21).  The statement deliberately keeps
`delta22` out of the formula: the residual diagonal block is `delta22 + F`.
-/
theorem F_eq_schurResidual
    (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ)
    (hK : IsUnit (KDelta S Delta).det) :
    F S Delta =
      S.Yskel * S.Kpiv * S.Xskel + S.E0 -
        (S.Yskel * S.Kpiv + delta21 Delta) *
          (KDelta S Delta)⁻¹ *
            (S.Kpiv * S.Xskel + delta12 Delta) := by
  have hleft : (KDelta S Delta)⁻¹ * KDelta S Delta = 1 :=
    Matrix.nonsing_inv_mul (KDelta S Delta) hK
  have hright : KDelta S Delta * (KDelta S Delta)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv (KDelta S Delta) hK
  have hYA :
      (S.Yskel * KDelta S Delta) * (KDelta S Delta)⁻¹ = S.Yskel := by
    rw [Matrix.mul_assoc, hright, Matrix.mul_one]
  have hInvX :
      (KDelta S Delta)⁻¹ * (KDelta S Delta * S.Xskel) = S.Xskel := by
    rw [← Matrix.mul_assoc, hleft, Matrix.one_mul]
  have hcore :
      (S.Yskel * KDelta S Delta + G21 S Delta) *
            (KDelta S Delta)⁻¹ *
          (KDelta S Delta * S.Xskel + G12 S Delta) =
        S.Yskel * KDelta S Delta * S.Xskel +
          S.Yskel * G12 S Delta + G21 S Delta * S.Xskel +
            G21 S Delta * (KDelta S Delta)⁻¹ * G12 S Delta := by
    simp only [Matrix.add_mul, Matrix.mul_add]
    simp only [hYA, hInvX, Matrix.mul_assoc]
    abel
  have hKexpand :
      S.Yskel * KDelta S Delta * S.Xskel =
        S.Yskel * S.Kpiv * S.Xskel +
          S.Yskel * delta11 Delta * S.Xskel := by
    rw [KDelta, Matrix.mul_add, Matrix.add_mul]
  have hG12expand :
      S.Yskel * G12 S Delta =
        S.Yskel * delta12 Delta -
          S.Yskel * delta11 Delta * S.Xskel := by
    simp only [G12, Matrix.mul_sub, Matrix.mul_assoc]
  have hG21expand :
      G21 S Delta * S.Xskel =
        delta21 Delta * S.Xskel -
          S.Yskel * delta11 Delta * S.Xskel := by
    simp only [G21, Matrix.sub_mul, Matrix.mul_assoc]
  rw [lowerBlock_eq_Y_mul_KDelta_add_G21,
    upperBlock_eq_KDelta_mul_X_add_G12, hcore]
  simp only [F]
  rw [hKexpand, hG12expand, hG21expand]
  abel

/-- Block form of the perturbed skeleton, before elimination. -/
theorem skeleton_add_blockForm
    (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    skeletonMatrix S + Delta =
      Matrix.fromBlocks
        (S.Kpiv + delta11 Delta)
        (S.Kpiv * S.Xskel + delta12 Delta)
        (S.Yskel * S.Kpiv + delta21 Delta)
        (S.Yskel * S.Kpiv * S.Xskel + S.E0 + delta22 Delta) := by
  calc
    skeletonMatrix S + Delta =
        skeletonMatrix S +
          Matrix.fromBlocks (delta11 Delta) (delta12 Delta)
            (delta21 Delta) (delta22 Delta) := by
      change skeletonMatrix S + Delta =
        skeletonMatrix S +
          Matrix.fromBlocks Delta.toBlocks₁₁ Delta.toBlocks₁₂
            Delta.toBlocks₂₁ Delta.toBlocks₂₂
      rw [Matrix.fromBlocks_toBlocks]
    _ = _ := by
      rw [skeletonMatrix, Matrix.fromBlocks_add]

/-- Exact three-factor CUR/Schur identity (9.21). -/
theorem skeleton_add_eq_CUR
    (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ)
    (hK : IsUnit (KDelta S Delta).det) :
    skeletonMatrix S + Delta =
      leftCURShear S Delta * CURDiagonal S Delta * rightCURShear S Delta := by
  rw [skeleton_add_blockForm]
  simp only [leftCURShear, CURDiagonal, rightCURShear,
    Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add]
  rw [Matrix.fromBlocks_inj]
  constructor
  · rfl
  constructor
  · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv (KDelta S Delta) hK,
      Matrix.one_mul]
  constructor
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul (KDelta S Delta) hK,
      Matrix.mul_one]
  · rw [F_eq_schurResidual S Delta hK]
    have hcancel :
        (((S.Yskel * S.Kpiv + delta21 Delta) *
              (KDelta S Delta)⁻¹) * KDelta S Delta) *
            ((KDelta S Delta)⁻¹ *
              (S.Kpiv * S.Xskel + delta12 Delta)) =
          (S.Yskel * S.Kpiv + delta21 Delta) *
            (KDelta S Delta)⁻¹ *
              (S.Kpiv * S.Xskel + delta12 Delta) := by
      rw [Matrix.mul_assoc
        (S.Yskel * S.Kpiv + delta21 Delta) (KDelta S Delta)⁻¹
        (KDelta S Delta),
        Matrix.nonsing_inv_mul (KDelta S Delta) hK, Matrix.mul_one,
        ← Matrix.mul_assoc]
    rw [hcancel]
    abel

/-- The left factor in (9.21) is a determinant-one shear. -/
@[simp] theorem leftCURShear_det
    (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    (leftCURShear S Delta).det = 1 := by
  simp [leftCURShear]

/-- The right factor in (9.21) is a determinant-one shear. -/
@[simp] theorem rightCURShear_det
    (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    (rightCURShear S Delta).det = 1 := by
  simp [rightCURShear]

/-- Determinant of the middle block diagonal factor. -/
@[simp] theorem CURDiagonal_det
    (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    (CURDiagonal S Delta).det =
      (KDelta S Delta).det * (delta22 Delta + F S Delta).det := by
  simp [CURDiagonal]

/-- The determinant decomposition following (9.21). -/
theorem det_skeleton_add_eq_det_KDelta_mul_det_residual
    (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ)
    (hK : IsUnit (KDelta S Delta).det) :
    (skeletonMatrix S + Delta).det =
      (KDelta S Delta).det * (delta22 Delta + F S Delta).det := by
  rw [skeleton_add_eq_CUR S Delta hK, Matrix.det_mul, Matrix.det_mul]
  simp

end Algebra

end BernoulliSection9
