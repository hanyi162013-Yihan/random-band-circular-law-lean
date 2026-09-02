import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.NoncommRing

/-!
# Transfer coordinates and double elimination

This file formalizes the deterministic linear algebra in Section 9.4.  An
auxiliary matrix can be eliminated in two orders: a first elimination identifies
its determinant with a boundary polynomial, while elimination of an invertible
endpoint block gives a Schur complement.  The resulting equality is recorded in
`schurComplement_doubleElimination` and specialized to the endpoint pivot used
in the paper.

The final section gives the determinant scaling caused by multiplying a chosen
leading family of rows by one scalar.  The statement uses arbitrary finite
index types, so the paper's first `3W` rows are obtained by taking an index type
of cardinality `3W`.
-/

open scoped Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix

section DoubleElimination

variable {R : Type*} [CommRing R]
variable {p q : Type*}
variable [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

/-- The Schur complement of the bottom-right block, written with mathlib's
total nonsingular inverse.  The determinant theorem below assumes that the
bottom-right determinant is a unit. -/
def schurComplement₂₂ (A : Matrix p p R) (B : Matrix p q R)
    (C : Matrix q p R) (G : Matrix q q R) : Matrix p p R :=
  A - B * G⁻¹ * C

/-- Determinant of a block matrix obtained by eliminating an invertible
bottom-right block.  This is a proposition-valued version of
`Matrix.det_fromBlocks₂₂`: the public statement asks for `IsUnit G.det` rather
than carrying an `Invertible G` instance. -/
theorem det_fromBlocks_eq_det_mul_det_schurComplement₂₂
    (A : Matrix p p R) (B : Matrix p q R) (C : Matrix q p R)
    (G : Matrix q q R) (hG : IsUnit G.det) :
    (Matrix.fromBlocks A B C G).det =
      G.det * (schurComplement₂₂ A B C G).det := by
  let _ : Invertible G := G.invertibleOfIsUnitDet hG
  simpa [schurComplement₂₂] using Matrix.det_fromBlocks₂₂ A B C G

/-- Abstract double elimination.  `hFirst` is the exact result of the first
elimination, and `hSchur` identifies the second elimination with `H`. -/
theorem schurComplement_doubleElimination
    (K : Matrix (p ⊕ q) (p ⊕ q) R)
    (A : Matrix p p R) (B : Matrix p q R) (C : Matrix q p R)
    (G : Matrix q q R) (H : Matrix p p R) (D : R)
    (hG : IsUnit G.det)
    (hBlocks : K = Matrix.fromBlocks A B C G)
    (hFirst : K.det = D)
    (hSchur : schurComplement₂₂ A B C G = H) :
    D = G.det * H.det := by
  calc
    D = K.det := hFirst.symm
    _ = (Matrix.fromBlocks A B C G).det := by rw [hBlocks]
    _ = G.det * (schurComplement₂₂ A B C G).det :=
      det_fromBlocks_eq_det_mul_det_schurComplement₂₂ A B C G hG
    _ = G.det * H.det := by rw [hSchur]

end DoubleElimination

section EndpointPivot

variable {R : Type*} [CommRing R]
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The block quarter-turn.  Its three-shear factorization below avoids any
parity bookkeeping for the permutation exchanging the two block columns. -/
def blockQuarterTurn : Matrix (W ⊕ W) (W ⊕ W) R :=
  Matrix.fromBlocks 0 (-1) 1 0

/-- A quarter-turn is a product of three block shears. -/
theorem blockQuarterTurn_eq_threeShears :
    (blockQuarterTurn : Matrix (W ⊕ W) (W ⊕ W) R) =
      Matrix.fromBlocks 1 0 1 1 *
        Matrix.fromBlocks 1 (-1) 0 1 *
          Matrix.fromBlocks 1 0 1 1 := by
  simp [blockQuarterTurn, Matrix.fromBlocks_multiply]

/-- The determinant of the block quarter-turn is one, in every finite
dimension and over every commutative ring. -/
@[simp]
theorem blockQuarterTurn_det :
    (blockQuarterTurn : Matrix (W ⊕ W) (W ⊕ W) R).det = 1 := by
  rw [blockQuarterTurn_eq_threeShears, Matrix.det_mul, Matrix.det_mul]
  simp

/-- The endpoint pivot appearing in the second elimination of Section 9.4:
`G_Θ = [[0, -Θ₁₁], [I, -Θ₂₁]]`. -/
def endpointPivot (Θ11 Θ21 : Matrix W W R) :
    Matrix (W ⊕ W) (W ⊕ W) R :=
  Matrix.fromBlocks 0 (-Θ11) 1 (-Θ21)

/-- Factorization of the endpoint pivot into a quarter-turn and a block
upper-triangular matrix. -/
theorem endpointPivot_eq_mul (Θ11 Θ21 : Matrix W W R) :
    endpointPivot Θ11 Θ21 =
      blockQuarterTurn * Matrix.fromBlocks 1 (-Θ21) 0 Θ11 := by
  simp [endpointPivot, blockQuarterTurn, Matrix.fromBlocks_multiply]

/-- The endpoint pivot has determinant `det Θ₁₁`.  Notice that this identity
itself does not require `Θ₁₁` to be invertible. -/
@[simp]
theorem endpointPivot_det (Θ11 Θ21 : Matrix W W R) :
    (endpointPivot Θ11 Θ21).det = Θ11.det := by
  rw [endpointPivot_eq_mul, Matrix.det_mul, blockQuarterTurn_det]
  simp

variable {p : Type*} [Fintype p] [DecidableEq p]

/-- Section 9.4's exact transfer-coordinate identity, isolated from the
model-specific construction of `K`, `D`, and `H`.  The hypotheses say exactly
that the auxiliary matrix has the displayed endpoint block, that the first
elimination gives `D`, and that its endpoint Schur complement is `H`. -/
theorem exact_transferCoordinate_of_doubleElimination
    (K : Matrix (p ⊕ (W ⊕ W)) (p ⊕ (W ⊕ W)) R)
    (A : Matrix p p R) (B : Matrix p (W ⊕ W) R)
    (C : Matrix (W ⊕ W) p R)
    (Θ11 Θ21 : Matrix W W R) (H : Matrix p p R) (D : R)
    (h11 : IsUnit Θ11.det)
    (hBlocks : K = Matrix.fromBlocks A B C (endpointPivot Θ11 Θ21))
    (hFirst : K.det = D)
    (hSchur : schurComplement₂₂ A B C (endpointPivot Θ11 Θ21) = H) :
    D = Θ11.det * H.det := by
  have hG : IsUnit (endpointPivot Θ11 Θ21).det := by
    simpa using h11
  simpa using schurComplement_doubleElimination K A B C
    (endpointPivot Θ11 Θ21) H D hG hBlocks hFirst hSchur

end EndpointPivot

section CoordinateFormula

variable {R : Type*} [CommRing R]
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The graph-coordinate map obtained by solving the boundary equations for
`(ψ₋, ψ₊)` in terms of `(ψ_L, ψ_R)`. -/
def transferCoordinateMap
    (Θ11 Θ12 Θ21 Θ22 : Matrix W W R) :
    Matrix (W ⊕ W) (W ⊕ W) R :=
  Matrix.fromBlocks
    (Θ21 * Θ11⁻¹)
    (Θ22 - Θ21 * Θ11⁻¹ * Θ12)
    Θ11⁻¹
    (-(Θ11⁻¹ * Θ12))

/-- Block-coordinate form of solving
`ψ_L = Θ₁₁ ψ₊ + Θ₁₂ ψ_R` and
`ψ₋ = Θ₂₁ ψ₊ + Θ₂₂ ψ_R`. -/
theorem transferCoordinateMap_mul_frame
    (Θ11 Θ12 Θ21 Θ22 : Matrix W W R) (h11 : IsUnit Θ11.det) :
    transferCoordinateMap Θ11 Θ12 Θ21 Θ22 *
        Matrix.fromBlocks Θ11 Θ12 0 1 =
      Matrix.fromBlocks Θ21 Θ22 1 0 := by
  have hinv : Θ11⁻¹ * Θ11 = 1 := Matrix.nonsing_inv_mul Θ11 h11
  simp only [transferCoordinateMap, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.mul_one, add_zero, sub_eq_add_neg]
  rw [Matrix.fromBlocks_inj]
  constructor
  · rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  constructor
  · noncomm_ring
  constructor
  · exact hinv
  · simp

end CoordinateFormula

section LeadingRowScaling

variable {R : Type*} [CommRing R]
variable {p q : Type*}
variable [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

/-- Multiply precisely the rows indexed by the leading summand `p` by `σ`.
The rows indexed by the trailing summand `q` are unchanged. -/
def scaleLeadingRows (σ : R) (K : Matrix (p ⊕ q) (p ⊕ q) R) :
    Matrix (p ⊕ q) (p ⊕ q) R :=
  Matrix.fromBlocks (σ • (1 : Matrix p p R)) 0 0 1 * K

/-- Temporary row scaling (Corollary 9.4), in arbitrary finite dimension.
Scaling the leading rows contributes one factor of `σ` for each such row. -/
theorem scaleLeadingRows_det (σ : R) (K : Matrix (p ⊕ q) (p ⊕ q) R) :
    (scaleLeadingRows σ K).det =
      σ ^ Fintype.card p * K.det := by
  simp [scaleLeadingRows, Matrix.det_mul]

end LeadingRowScaling

section LeadingRowScalingField

variable {F : Type*} [Field F]
variable {p q : Type*}
variable [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

/-- Inverse form of temporary row scaling, matching the normalization in the
paper.  For `card p = 3W`, the scalar is `σ⁻¹` to the power `3W`. -/
theorem det_eq_inv_pow_mul_scaleLeadingRows_det
    (σ : F) (hσ : σ ≠ 0) (K : Matrix (p ⊕ q) (p ⊕ q) F) :
    K.det = σ⁻¹ ^ Fintype.card p * (scaleLeadingRows σ K).det := by
  rw [scaleLeadingRows_det, ← mul_assoc, ← mul_pow]
  simp [hσ]

end LeadingRowScalingField

end BernoulliLinearAlgebra
