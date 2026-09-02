import BernoulliLinearAlgebra.TransferCoordinate
import BernoulliLinearAlgebra.BoundaryGram
import Mathlib.Tactic

/-!
# The concrete five-block double elimination

This file encodes the displayed `5W × 5W` matrix `K_Theta` from Section 9.4,
equation (9.78), and the double elimination of Proposition 9.3.
The first three block coordinates are `(L,C,R)` and the last two are the
endpoint variables `(-,+)`.  Eliminating the endpoint pivot produces the
literal three-block terminal matrix with the outer correction
`Emb_O (diag(C_L,B_R) * S(Theta))`.
-/

open scoped Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix

/-- Index type for the three retained packet sites `(L,C,R)`. -/
abbrev Packet3 (W : Type*) := W ⊕ (W ⊕ W)

section Definitions

variable {R : Type*} [CommRing R]
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The tridiagonal three-packet core before the endpoint correction. -/
def packetCore
    (DL BL CC DC BC CR DR : Matrix W W R) :
    Matrix (Packet3 W) (Packet3 W) R := fun i j =>
  match i, j with
  | Sum.inl a, Sum.inl b => DL a b
  | Sum.inl a, Sum.inr (Sum.inl b) => BL a b
  | Sum.inl _, Sum.inr (Sum.inr _) => 0
  | Sum.inr (Sum.inl a), Sum.inl b => CC a b
  | Sum.inr (Sum.inl a), Sum.inr (Sum.inl b) => DC a b
  | Sum.inr (Sum.inl a), Sum.inr (Sum.inr b) => BC a b
  | Sum.inr (Sum.inr _), Sum.inl _ => 0
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inl b) => CR a b
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inr b) => DR a b

/-- Inclusion of the outer coordinates `(L,R)` into `(L,C,R)`. -/
def packetOuterInjection : Matrix (Packet3 W) (W ⊕ W) R := fun i j =>
  match i, j with
  | Sum.inl a, Sum.inl b => (1 : Matrix W W R) a b
  | Sum.inr (Sum.inr a), Sum.inr b => (1 : Matrix W W R) a b
  | _, _ => 0

/-- Projection from `(L,C,R)` onto the outer coordinates `(L,R)`. -/
def packetOuterProjection : Matrix (W ⊕ W) (Packet3 W) R := fun i j =>
  match i, j with
  | Sum.inl a, Sum.inl b => (1 : Matrix W W R) a b
  | Sum.inr a, Sum.inr (Sum.inr b) => (1 : Matrix W W R) a b
  | _, _ => 0

/-- `E = diag(C_L,B_R)`. -/
def endpointFactor (CL BR : Matrix W W R) :
    Matrix (W ⊕ W) (W ⊕ W) R :=
  Matrix.fromBlocks CL 0 0 BR

/-- Coupling of the packet equations to endpoint variables `(-,+)`. -/
def packetEndpointCoupling (CL BR : Matrix W W R) :
    Matrix (Packet3 W) (W ⊕ W) R :=
  packetOuterInjection * endpointFactor CL BR

/-- The two boundary equations restricted to the outer physical variables. -/
def boundaryOuterCoupling (Theta12 Theta22 : Matrix W W R) :
    Matrix (W ⊕ W) (W ⊕ W) R :=
  Matrix.fromBlocks 1 (-Theta12) 0 (-Theta22)

/-- Coefficients of the physical variables in the two boundary equations. -/
def boundaryPhysicalCoupling (Theta12 Theta22 : Matrix W W R) :
    Matrix (W ⊕ W) (Packet3 W) R :=
  boundaryOuterCoupling Theta12 Theta22 * packetOuterProjection

/-- Embed a matrix on the outer coordinates `(L,R)` into `(L,C,R)`. -/
def packetOuterEmbedding (Q : Matrix (W ⊕ W) (W ⊕ W) R) :
    Matrix (Packet3 W) (Packet3 W) R :=
  packetOuterInjection * Q * packetOuterProjection

/-- The displayed auxiliary matrix `K_Theta`, in `3W | 2W` block form. -/
def concreteKTheta
    (DL BL CC DC BC CR DR CL BR : Matrix W W R)
    (Theta11 Theta12 Theta21 Theta22 : Matrix W W R) :
    Matrix (Packet3 W ⊕ (W ⊕ W)) (Packet3 W ⊕ (W ⊕ W)) R :=
  Matrix.fromBlocks
    (packetCore DL BL CC DC BC CR DR)
    (packetEndpointCoupling CL BR)
    (boundaryPhysicalCoupling Theta12 Theta22)
    (endpointPivot Theta11 Theta21)

/-- The concrete terminal matrix after eliminating the endpoint variables. -/
def concreteHTheta
    (DL BL CC DC BC CR DR CL BR : Matrix W W R)
    (Theta11 Theta12 Theta21 Theta22 : Matrix W W R) :
    Matrix (Packet3 W) (Packet3 W) R :=
  packetCore DL BL CC DC BC CR DR +
    packetOuterEmbedding
      (endpointFactor CL BR *
        transferCoordinateMap Theta11 Theta12 Theta21 Theta22)

end Definitions

section EndpointInverse

variable {R : Type*} [CommRing R]
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Explicit inverse of the endpoint pivot. -/
def endpointPivotInverse (Theta11 Theta21 : Matrix W W R) :
    Matrix (W ⊕ W) (W ⊕ W) R :=
  Matrix.fromBlocks (-(Theta21 * Theta11⁻¹)) 1 (-Theta11⁻¹) 0

theorem endpointPivot_inv
    (Theta11 Theta21 : Matrix W W R) (h11 : IsUnit Theta11.det) :
    (endpointPivot Theta11 Theta21)⁻¹ =
      endpointPivotInverse Theta11 Theta21 := by
  apply Matrix.inv_eq_right_inv
  simp only [endpointPivot, endpointPivotInverse,
    Matrix.fromBlocks_multiply]
  rw [← Matrix.fromBlocks_one]
  rw [Matrix.fromBlocks_inj]
  constructor
  · simpa using Matrix.mul_nonsing_inv Theta11 h11
  constructor
  · simp
  constructor
  · noncomm_ring
  · simp

end EndpointInverse

section SchurCalculation

variable {R : Type*} [CommRing R]
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Solving the endpoint equations gives the displayed transfer-coordinate
map before the deterministic endpoint factor is applied. -/
theorem neg_endpointPivotInverse_mul_boundaryOuterCoupling
    (Theta11 Theta12 Theta21 Theta22 : Matrix W W R) :
    -(endpointPivotInverse Theta11 Theta21 *
        boundaryOuterCoupling Theta12 Theta22) =
      transferCoordinateMap Theta11 Theta12 Theta21 Theta22 := by
  simp only [endpointPivotInverse, boundaryOuterCoupling,
    transferCoordinateMap, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_neg]
  rw [Matrix.fromBlocks_inj]
  constructor
  · noncomm_ring
  constructor
  · noncomm_ring
  constructor <;> noncomm_ring

/-- The endpoint Schur correction is exactly the embedded graph correction. -/
theorem endpoint_schur_correction
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix W W R)
    (h11 : IsUnit Theta11.det) :
    -(packetEndpointCoupling CL BR *
        (endpointPivot Theta11 Theta21)⁻¹ *
          boundaryPhysicalCoupling Theta12 Theta22) =
      packetOuterEmbedding
        (endpointFactor CL BR *
          transferCoordinateMap Theta11 Theta12 Theta21 Theta22) := by
  rw [endpointPivot_inv Theta11 Theta21 h11]
  unfold packetEndpointCoupling boundaryPhysicalCoupling packetOuterEmbedding
  let inclusion : Matrix (Packet3 W) (W ⊕ W) R := packetOuterInjection
  let projection : Matrix (W ⊕ W) (Packet3 W) R := packetOuterProjection
  change
    -(inclusion * endpointFactor CL BR *
        endpointPivotInverse Theta11 Theta21 *
          (boundaryOuterCoupling Theta12 Theta22 * projection)) =
      inclusion *
        (endpointFactor CL BR *
          transferCoordinateMap Theta11 Theta12 Theta21 Theta22) * projection
  calc
    -(inclusion * endpointFactor CL BR *
          endpointPivotInverse Theta11 Theta21 *
            (boundaryOuterCoupling Theta12 Theta22 * projection)) =
        -(inclusion *
          (endpointFactor CL BR *
            (endpointPivotInverse Theta11 Theta21 *
              boundaryOuterCoupling Theta12 Theta22)) * projection) := by
          congr 1
          simp only [Matrix.mul_assoc]
    _ = (-(inclusion *
          (endpointFactor CL BR *
            (endpointPivotInverse Theta11 Theta21 *
              boundaryOuterCoupling Theta12 Theta22)))) * projection := by
          exact (Matrix.neg_mul
            (inclusion *
              (endpointFactor CL BR *
                (endpointPivotInverse Theta11 Theta21 *
                  boundaryOuterCoupling Theta12 Theta22))) projection).symm
    _ = inclusion *
          (-(endpointFactor CL BR *
            (endpointPivotInverse Theta11 Theta21 *
              boundaryOuterCoupling Theta12 Theta22))) * projection := by
          exact congrArg
            (fun Z : Matrix (Packet3 W) (W ⊕ W) R => Z * projection)
            (Matrix.mul_neg inclusion
              (endpointFactor CL BR *
                (endpointPivotInverse Theta11 Theta21 *
                  boundaryOuterCoupling Theta12 Theta22))).symm
    _ =
        inclusion *
          (endpointFactor CL BR *
            (-(endpointPivotInverse Theta11 Theta21 *
              boundaryOuterCoupling Theta12 Theta22))) *
              projection := by
          exact congrArg
            (fun Z : Matrix (W ⊕ W) (W ⊕ W) R =>
              (inclusion * Z) * projection)
            (Matrix.mul_neg (endpointFactor CL BR)
              (endpointPivotInverse Theta11 Theta21 *
                boundaryOuterCoupling Theta12 Theta22)).symm
    _ = inclusion *
          (endpointFactor CL BR *
            transferCoordinateMap Theta11 Theta12 Theta21 Theta22) *
              projection := by
        rw [neg_endpointPivotInverse_mul_boundaryOuterCoupling]

/-- Literal identification of the Schur complement with `H_Theta`. -/
theorem concrete_schurComplement_eq_HTheta
    (DL BL CC DC BC CR DR CL BR : Matrix W W R)
    (Theta11 Theta12 Theta21 Theta22 : Matrix W W R)
    (h11 : IsUnit Theta11.det) :
    schurComplement₂₂
        (packetCore DL BL CC DC BC CR DR)
        (packetEndpointCoupling CL BR)
        (boundaryPhysicalCoupling Theta12 Theta22)
        (endpointPivot Theta11 Theta21) =
      concreteHTheta DL BL CC DC BC CR DR CL BR
        Theta11 Theta12 Theta21 Theta22 := by
  unfold schurComplement₂₂ concreteHTheta
  rw [← endpoint_schur_correction CL BR Theta11 Theta12 Theta21 Theta22 h11]
  abel

/-- Concrete second-elimination identity for the displayed `K_Theta`. -/
theorem concreteKTheta_det_eq
    (DL BL CC DC BC CR DR CL BR : Matrix W W R)
    (Theta11 Theta12 Theta21 Theta22 : Matrix W W R)
    (h11 : IsUnit Theta11.det) :
    (concreteKTheta DL BL CC DC BC CR DR CL BR
        Theta11 Theta12 Theta21 Theta22).det =
      Theta11.det *
        (concreteHTheta DL BL CC DC BC CR DR CL BR
          Theta11 Theta12 Theta21 Theta22).det := by
  apply exact_transferCoordinate_of_doubleElimination
    (K := concreteKTheta DL BL CC DC BC CR DR CL BR
      Theta11 Theta12 Theta21 Theta22)
    (A := packetCore DL BL CC DC BC CR DR)
    (B := packetEndpointCoupling CL BR)
    (C := boundaryPhysicalCoupling Theta12 Theta22)
    (Θ11 := Theta11) (Θ21 := Theta21)
    (H := concreteHTheta DL BL CC DC BC CR DR CL BR
      Theta11 Theta12 Theta21 Theta22)
    (D := (concreteKTheta DL BL CC DC BC CR DR CL BR
      Theta11 Theta12 Theta21 Theta22).det)
    (h11 := h11)
  · rfl
  · rfl
  · exact concrete_schurComplement_eq_HTheta
      DL BL CC DC BC CR DR CL BR
      Theta11 Theta12 Theta21 Theta22 h11

end SchurCalculation

end BernoulliLinearAlgebra
