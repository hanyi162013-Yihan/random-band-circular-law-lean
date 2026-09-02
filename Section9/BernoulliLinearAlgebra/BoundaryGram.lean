import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Boundary graph Gram identities

This file formalizes the deterministic linear algebra used in the boundary-volume
argument of Section 9.5.  The first group of results is coordinate-free: Gram
matrices related by congruence have the expected determinant, and a graph written
as `S = N M⁻¹` has the same Gram determinant as its frame `(M, N)`.  The
second group gives the explicit two-by-two block frames used for a boundary
relation `Θ`.
-/

open scoped Matrix

namespace BernoulliLinearAlgebra

open Matrix

section GramCongruence

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Determinant under a complex Gram congruence. -/
theorem det_gram_congruence (M G : Matrix n n ℂ) :
    (Mᴴ * G * M).det = star M.det * G.det * M.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]

/-- The Gram congruence determinant, with the scalar factors collected as
`|det M|² = star (det M) * det M`. -/
theorem det_gram_congruence_normSq (M G : Matrix n n ℂ) :
    (Mᴴ * G * M).det = (star M.det * M.det) * G.det := by
  rw [det_gram_congruence]
  ring

/-- If `S = N M⁻¹` and `M` is nonsingular, congruence by `M` turns the
graph Gram matrix of `S` into the frame Gram matrix of `(M,N)`. -/
theorem graph_gram_congruence (M N S : Matrix n n ℂ) (hM : IsUnit M.det)
    (hS : S = N * M⁻¹) :
    Mᴴ * (1 + Sᴴ * S) * M = Mᴴ * M + Nᴴ * N := by
  subst S
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  have hright : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  have hleft : Mᴴ * Mᴴ⁻¹ = 1 := by
    rw [← Matrix.conjTranspose_nonsing_inv, ← Matrix.conjTranspose_mul, hright]
    simp
  calc
    Mᴴ * M + Mᴴ * (Mᴴ⁻¹ * Nᴴ * (N * M⁻¹)) * M =
        Mᴴ * M + ((Mᴴ * Mᴴ⁻¹) * (Nᴴ * N)) * (M⁻¹ * M) := by
          noncomm_ring
    _ = Mᴴ * M + Nᴴ * N := by rw [hleft, hright]; simp

/-- Determinant form of `graph_gram_congruence`.  This is the exact identity
used in the paper before identifying the frame Gram matrix with the boundary
relation Gram matrix. -/
theorem graph_gram_determinant (M N S : Matrix n n ℂ) (hM : IsUnit M.det)
    (hS : S = N * M⁻¹) :
    (star M.det * M.det) * (1 + Sᴴ * S).det =
      (Mᴴ * M + Nᴴ * N).det := by
  rw [← graph_gram_congruence M N S hM hS]
  exact (det_gram_congruence_normSq M (1 + Sᴴ * S)).symm

/-- The boundary graph determinant identity in the form used in Section 9.5. -/
theorem boundary_gram_determinant (M N S Θ : Matrix n n ℂ) (hM : IsUnit M.det)
    (hS : S = N * M⁻¹)
    (hGram : Mᴴ * M + Nᴴ * N = 1 + Θᴴ * Θ) :
    (star M.det * M.det) * (1 + Sᴴ * S).det =
      (1 + Θᴴ * Θ).det := by
  rw [graph_gram_determinant M N S hM hS, hGram]

/-- The same identity with the squared modulus written as `Complex.normSq`. -/
theorem boundary_gram_determinant_normSq (M N S Θ : Matrix n n ℂ)
    (hM : IsUnit M.det) (hS : S = N * M⁻¹)
    (hGram : Mᴴ * M + Nᴴ * N = 1 + Θᴴ * Θ) :
    (Complex.normSq M.det : ℂ) * (1 + Sᴴ * S).det =
      (1 + Θᴴ * Θ).det := by
  rw [Complex.normSq_eq_conj_mul_self]
  exact boundary_gram_determinant M N S Θ hM hS hGram

end GramCongruence

section ExplicitBoundaryFrames

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A boundary relation written in its four `W × W` blocks. -/
def boundaryRelation (Θ11 Θ12 Θ21 Θ22 : Matrix W W ℂ) :
    Matrix (W ⊕ W) (W ⊕ W) ℂ :=
  Matrix.fromBlocks Θ11 Θ12 Θ21 Θ22

/-- The upper graph frame `M(Θ)` from Section 9.5. -/
def boundaryFrameM (Θ11 Θ12 : Matrix W W ℂ) :
    Matrix (W ⊕ W) (W ⊕ W) ℂ :=
  Matrix.fromBlocks Θ11 Θ12 0 1

/-- The lower graph frame `N(Θ)` from Section 9.5. -/
def boundaryFrameN (Θ21 Θ22 : Matrix W W ℂ) :
    Matrix (W ⊕ W) (W ⊕ W) ℂ :=
  Matrix.fromBlocks Θ21 Θ22 1 0

/-- The explicit graph map `S(Θ) = N(Θ) M(Θ)⁻¹`, defined when the
upper-left block is nonsingular.  The formula itself is meaningful for every
matrix because mathlib's matrix inverse is total. -/
noncomputable def boundaryGraphS (Θ11 Θ12 Θ21 Θ22 : Matrix W W ℂ) :
    Matrix (W ⊕ W) (W ⊕ W) ℂ :=
  Matrix.fromBlocks
    (Θ21 * Θ11⁻¹)
    (Θ22 - Θ21 * Θ11⁻¹ * Θ12)
    Θ11⁻¹
    (-(Θ11⁻¹ * Θ12))

/-- The determinant of the triangular frame `M(Θ)` is `det Θ₁₁`. -/
@[simp]
theorem boundaryFrameM_det (Θ11 Θ12 : Matrix W W ℂ) :
    (boundaryFrameM Θ11 Θ12).det = Θ11.det := by
  simp [boundaryFrameM]

/-- Explicit inverse of the triangular frame `M(Θ)`. -/
theorem boundaryFrameM_inv (Θ11 Θ12 : Matrix W W ℂ) (h11 : IsUnit Θ11.det) :
    (boundaryFrameM Θ11 Θ12)⁻¹ =
      Matrix.fromBlocks Θ11⁻¹ (- (Θ11⁻¹ * Θ12)) 0 1 := by
  unfold boundaryFrameM
  rw [Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff Θ11 Θ12 1]
  · simp
  · constructor
    · intro _
      exact isUnit_one
    · intro _
      exact (Matrix.isUnit_iff_isUnit_det Θ11).mpr h11

/-- Direct multiplication of the explicit frames gives the graph map in the
paper. -/
theorem boundaryGraphS_eq_mul_inv (Θ11 Θ12 Θ21 Θ22 : Matrix W W ℂ)
    (h11 : IsUnit Θ11.det) :
    boundaryGraphS Θ11 Θ12 Θ21 Θ22 =
      boundaryFrameN Θ21 Θ22 * (boundaryFrameM Θ11 Θ12)⁻¹ := by
  rw [boundaryFrameM_inv Θ11 Θ12 h11]
  simp only [boundaryGraphS, boundaryFrameN, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul, add_zero, sub_eq_add_neg]
  rw [Matrix.fromBlocks_inj]
  constructor
  · rfl
  constructor
  · noncomm_ring
  constructor <;> rfl

/-- The two explicit frames have the same Gram matrix as the original boundary
relation. -/
theorem boundaryFrames_gram (Θ11 Θ12 Θ21 Θ22 : Matrix W W ℂ) :
    (boundaryFrameM Θ11 Θ12)ᴴ * boundaryFrameM Θ11 Θ12 +
        (boundaryFrameN Θ21 Θ22)ᴴ * boundaryFrameN Θ21 Θ22 =
      1 + (boundaryRelation Θ11 Θ12 Θ21 Θ22)ᴴ *
        boundaryRelation Θ11 Θ12 Θ21 Θ22 := by
  conv_rhs =>
    lhs
    rw [← Matrix.fromBlocks_one]
  simp only [boundaryFrameM, boundaryFrameN, boundaryRelation,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_add, Matrix.conjTranspose_zero, Matrix.conjTranspose_one,
    Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero]
  rw [Matrix.fromBlocks_inj]
  constructor
  · abel
  constructor
  · noncomm_ring
  constructor
  · noncomm_ring
  · abel

/-- Fully explicit form of the Section 9.5 boundary Gram determinant identity. -/
theorem explicit_boundary_gram_determinant
    (Θ11 Θ12 Θ21 Θ22 : Matrix W W ℂ) (h11 : IsUnit Θ11.det) :
    (star Θ11.det * Θ11.det) *
        (1 + (boundaryGraphS Θ11 Θ12 Θ21 Θ22)ᴴ *
          boundaryGraphS Θ11 Θ12 Θ21 Θ22).det =
      (1 + (boundaryRelation Θ11 Θ12 Θ21 Θ22)ᴴ *
        boundaryRelation Θ11 Θ12 Θ21 Θ22).det := by
  simpa using boundary_gram_determinant
    (boundaryFrameM Θ11 Θ12) (boundaryFrameN Θ21 Θ22)
    (boundaryGraphS Θ11 Θ12 Θ21 Θ22)
    (boundaryRelation Θ11 Θ12 Θ21 Θ22)
    (by simpa using h11)
    (boundaryGraphS_eq_mul_inv Θ11 Θ12 Θ21 Θ22 h11)
    (boundaryFrames_gram Θ11 Θ12 Θ21 Θ22)

/-- The fully explicit formula with `|det Θ₁₁|²` represented by
`Complex.normSq (det Θ₁₁)`. -/
theorem explicit_boundary_gram_determinant_normSq
    (Θ11 Θ12 Θ21 Θ22 : Matrix W W ℂ) (h11 : IsUnit Θ11.det) :
    (Complex.normSq Θ11.det : ℂ) *
        (1 + (boundaryGraphS Θ11 Θ12 Θ21 Θ22)ᴴ *
          boundaryGraphS Θ11 Θ12 Θ21 Θ22).det =
      (1 + (boundaryRelation Θ11 Θ12 Θ21 Θ22)ᴴ *
        boundaryRelation Θ11 Θ12 Θ21 Θ22).det := by
  rw [Complex.normSq_eq_conj_mul_self]
  exact explicit_boundary_gram_determinant Θ11 Θ12 Θ21 Θ22 h11

end ExplicitBoundaryFrames

end BernoulliLinearAlgebra
