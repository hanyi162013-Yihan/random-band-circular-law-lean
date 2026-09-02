import BernoulliSection10.PacketBoundary
import BernoulliSection10.PhysicalRows

/-!
# Physical-row multiaffinity of the seven-block packet

This file supplies the deterministic multiaffinity input used in Proposition
10.9.  The formal variables are the literal seven-block mask already encoded
by `ThreeBlockVariable`: `A_L,B_L,C_C,A_C,B_C,C_R,A_R`.  Fixing a row of
`ThreeBlockIndex W` groups exactly the variables in one physical packet row.
Thus the rows split as left, centre, and right, with respectively two, three,
and two `W`-entry blocks.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliSection10

open Matrix MvPolynomial
open BernoulliLinearAlgebra

section RowGroups

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The scalar variables occurring in the physical packet row `i`.  Since a
formal variable is an allowed row--column pair, fixing its row is precisely
the grouping used in the proof of Proposition 10.9. -/
abbrev PacketPhysicalRow (i : ThreeBlockIndex W) :=
  {e : ThreeBlockVariable W // e.1.1 = i}

/-- Left, centre, and right row indices in paper order. -/
def packetLeftRow (a : W) : ThreeBlockIndex W := Sum.inl (false, a)
def packetCenterRow (a : W) : ThreeBlockIndex W := Sum.inr a
def packetRightRow (a : W) : ThreeBlockIndex W := Sum.inl (true, a)

/-- The `3W` physical rows are exactly the `W` left rows, `W` centre rows,
and `W` right rows. -/
theorem packetPhysicalRow_index_cases (i : ThreeBlockIndex W) :
    (∃ a, i = packetLeftRow a) ∨
      (∃ a, i = packetCenterRow a) ∨
        (∃ a, i = packetRightRow a) := by
  rcases i with ⟨b, a⟩ | a
  · cases b
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inr ⟨a, rfl⟩)
  · exact Or.inr (Or.inl ⟨a, rfl⟩)

/-- There are exactly `3 * card W` physical-row groups. -/
@[simp] theorem card_threeBlockIndex :
    Fintype.card (ThreeBlockIndex W) = 3 * Fintype.card W := by
  simp [ThreeBlockIndex, ThreeBlockOuter]
  omega

/-- A scalar in a fixed physical row is determined by its column. -/
def packetPhysicalRowColumnEmbedding (i : ThreeBlockIndex W) :
    PacketPhysicalRow i ↪ ThreeBlockIndex W where
  toFun e := e.1.1.2
  inj' := by
    intro e f h
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (e.2.trans f.2.symm) h

/-- Every physical row contains at most `3W` scalar variables.  The sharper
counts are `2W,3W,2W` for left, centre, and right; Proposition 10.9 only uses
this uniform bound. -/
theorem card_packetPhysicalRow_le_three_mul (i : ThreeBlockIndex W) :
    Fintype.card (PacketPhysicalRow i) ≤ 3 * Fintype.card W := by
  calc
    Fintype.card (PacketPhysicalRow i) ≤
        Fintype.card (ThreeBlockIndex W) :=
      Fintype.card_le_of_injective _
        (packetPhysicalRowColumnEmbedding i).injective
    _ = 3 * Fintype.card W := card_threeBlockIndex

/-- Replace exactly one physical-row group in a scalar assignment. -/
def replacePacketPhysicalRow (x : ThreeBlockVariable W → ℂ)
    (i : ThreeBlockIndex W) (r : PacketPhysicalRow i → ℂ) :
    ThreeBlockVariable W → ℂ := fun e =>
  if h : e.1.1 = i then r ⟨e, h⟩ else x e

/-- Affine interpolation of two candidate physical rows. -/
def interpolatePacketPhysicalRow {i : ThreeBlockIndex W} (t : ℂ)
    (r s : PacketPhysicalRow i → ℂ) : PacketPhysicalRow i → ℂ :=
  fun e => (1 - t) * r e + t * s e

/-- Separate affinity of a concrete formal polynomial in one physical-row
group. -/
def IsAffineInPacketPhysicalRow (i : ThreeBlockIndex W)
    (P : MvPolynomial (ThreeBlockVariable W) ℂ) : Prop :=
  ∀ (x : ThreeBlockVariable W → ℂ)
    (r s : PacketPhysicalRow i → ℂ) (t : ℂ),
    eval (replacePacketPhysicalRow x i
        (interpolatePacketPhysicalRow t r s)) P =
      (1 - t) * eval (replacePacketPhysicalRow x i r) P +
        t * eval (replacePacketPhysicalRow x i s) P

end RowGroups

section LiteralPacketMatrix

variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

local instance packetMultiaffineSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W => (toLex x : W ⊕ₗ W)) toLex.injective

/-- Numerical evaluation of the literal five-block matrix `K_Theta`.  The
first block is written through `threeBlockDelta`; the base theorem below
identifies it entry-for-entry with `concreteKTheta`. -/
def packetLiteralK
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (x : ThreeBlockVariable W → ℂ) :
    Matrix (Packet3 W ⊕ (W ⊕ W)) (Packet3 W ⊕ (W ⊕ W)) ℂ :=
  Matrix.fromBlocks
    ((threeBlockDelta x - z • 1).submatrix
      (threeBlockIndexEquiv W).symm (threeBlockIndexEquiv W).symm)
    (packetEndpointCoupling CL BR)
    (boundaryPhysicalCoupling Theta.toBlocks₁₂ Theta.toBlocks₂₂)
    (endpointPivot Theta.toBlocks₁₁ Theta.toBlocks₂₁)

/-- The displayed matrix above is exactly the stable base's numerical
`concreteKTheta`, with the spectral shift in the three diagonal blocks. -/
theorem packetLiteralK_eq_concreteKTheta
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (x : ThreeBlockVariable W → ℂ) :
    packetLiteralK z CL BR Theta x =
      concreteKTheta
        (threeBlockAL x - z • 1) (threeBlockBL x) (threeBlockCC x)
        (threeBlockAC x - z • 1) (threeBlockBC x) (threeBlockCR x)
        (threeBlockAR x - z • 1) CL BR
        Theta.toBlocks₁₁ Theta.toBlocks₁₂
        Theta.toBlocks₂₁ Theta.toBlocks₂₂ := by
  unfold packetLiteralK concreteKTheta
  congr 1
  have hsub :
      (threeBlockDelta x - z •
          (1 : Matrix (ThreeBlockIndex W) (ThreeBlockIndex W) ℂ)).submatrix
          (threeBlockIndexEquiv W).symm (threeBlockIndexEquiv W).symm =
        (threeBlockDelta x).submatrix
            (threeBlockIndexEquiv W).symm (threeBlockIndexEquiv W).symm -
          z • (1 : Matrix (Packet3 W) (Packet3 W) ℂ) := by
    ext p q
    simp [Matrix.one_apply]
  rw [hsub, threeBlockDelta_reindex_eq_packetCore]
  exact (packetCore_diagonalShift z
    (threeBlockAL x) (threeBlockBL x) (threeBlockCC x)
    (threeBlockAC x) (threeBlockBC x) (threeBlockCR x)
    (threeBlockAR x)).symm

/-- Evaluating the actual `globalBoundaryDetPolynomial` is the determinant
of the literal numerical `K_Theta`; no chart or invertibility assumption is
used. -/
theorem eval_packetBoundaryPolynomial_eq_packetLiteralK_det
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (x : ThreeBlockVariable W → ℂ) :
    eval x (packetBoundaryPolynomial z CL BR Theta) =
      (packetLiteralK z CL BR Theta x).det := by
  change eval x (globalBoundaryDetPolynomial z CL BR Theta) = _
  rw [packetLiteralK_eq_concreteKTheta]
  rw [globalBoundaryDetPolynomial, globalConcreteKPolynomial,
    (eval x).map_det]
  change
    ((threeBlockConcreteKPolynomialShifted z CL BR
      Theta.toBlocks₁₁ Theta.toBlocks₁₂ Theta.toBlocks₂₁
        Theta.toBlocks₂₂).map (eval x)).det =
      (concreteKTheta
        (threeBlockAL x - z • 1) (threeBlockBL x) (threeBlockCC x)
        (threeBlockAC x - z • 1) (threeBlockBC x) (threeBlockCR x)
        (threeBlockAR x - z • 1) CL BR
        Theta.toBlocks₁₁ Theta.toBlocks₁₂
        Theta.toBlocks₂₁ Theta.toBlocks₂₂).det
  congr 1
  ext i j
  rcases i with ((i | (i | i)) | (i | i)) <;>
    rcases j with ((j | (j | j)) | (j | j)) <;>
    simp [threeBlockConcreteKPolynomialShifted, concreteKTheta,
      packetCore, packetEndpointCoupling, boundaryPhysicalCoupling,
      boundaryOuterCoupling, packetOuterInjection, packetOuterProjection,
      endpointFactor, endpointPivot, threeBlockCMatrix,
      threeBlockALPolynomial, threeBlockBLPolynomial,
      threeBlockCCPolynomial, threeBlockACPolynomial,
      threeBlockBCPolynomial, threeBlockCRPolynomial,
      threeBlockARPolynomial, threeBlockAL, threeBlockBL,
      threeBlockCC, threeBlockAC, threeBlockBC, threeBlockCR,
      threeBlockAR, Matrix.mul_apply, Matrix.one_apply]
  all_goals split_ifs <;> simp_all

/-- Location of a physical packet row inside the `5W × 5W` literal
boundary matrix. -/
def packetKRowIndex (i : ThreeBlockIndex W) : Packet3 W ⊕ (W ⊕ W) :=
  Sum.inl (threeBlockIndexEquiv W i)

@[simp] theorem replacePacketPhysicalRow_same
    (x : ThreeBlockVariable W → ℂ) (i : ThreeBlockIndex W)
    (r : PacketPhysicalRow i → ℂ) (e : ThreeBlockVariable W)
    (h : e.1.1 = i) :
    replacePacketPhysicalRow x i r e = r ⟨e, h⟩ := by
  simp [replacePacketPhysicalRow, h]

@[simp] theorem replacePacketPhysicalRow_other
    (x : ThreeBlockVariable W → ℂ) (i : ThreeBlockIndex W)
    (r : PacketPhysicalRow i → ℂ) (e : ThreeBlockVariable W)
    (h : e.1.1 ≠ i) :
    replacePacketPhysicalRow x i r e = x e := by
  simp [replacePacketPhysicalRow, h]

/-- Replacing a physical row leaves every other row of the literal `K`
matrix unchanged. -/
theorem packetLiteralK_replace_other_row
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (x : ThreeBlockVariable W → ℂ) (i : ThreeBlockIndex W)
    (r : PacketPhysicalRow i → ℂ)
    (p q : Packet3 W ⊕ (W ⊕ W))
    (hp : p ≠ packetKRowIndex i) :
    packetLiteralK z CL BR Theta (replacePacketPhysicalRow x i r) p q =
      packetLiteralK z CL BR Theta x p q := by
  rcases p with p | p
  · have hpi : (threeBlockIndexEquiv W).symm p ≠ i := by
      intro h
      have hp' : p = threeBlockIndexEquiv W i := by
        simpa using congrArg (threeBlockIndexEquiv W) h
      exact hp (congrArg Sum.inl hp')
    rcases q with q | q
    · simp [packetLiteralK, threeBlockDelta, replacePacketPhysicalRow,
        hpi]
    · rfl
  · rcases q with q | q <;> rfl

/-- The changed row of the literal `K` matrix is affine in all scalar
variables belonging to that physical row, varied simultaneously. -/
theorem packetLiteralK_changed_row_interpolate
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (x : ThreeBlockVariable W → ℂ) (i : ThreeBlockIndex W)
    (r s : PacketPhysicalRow i → ℂ) (t : ℂ)
    (q : Packet3 W ⊕ (W ⊕ W)) :
    packetLiteralK z CL BR Theta
        (replacePacketPhysicalRow x i
          (interpolatePacketPhysicalRow t r s))
        (packetKRowIndex i) q =
      (1 - t) *
          packetLiteralK z CL BR Theta
            (replacePacketPhysicalRow x i r) (packetKRowIndex i) q +
        t * packetLiteralK z CL BR Theta
          (replacePacketPhysicalRow x i s) (packetKRowIndex i) q := by
  rcases q with q | q
  · by_cases h : threeBlockFresh i ((threeBlockIndexEquiv W).symm q)
    · simp [packetLiteralK, packetKRowIndex, threeBlockDelta,
        replacePacketPhysicalRow, interpolatePacketPhysicalRow, h]
      ring
    · simp [packetLiteralK, packetKRowIndex, threeBlockDelta,
        replacePacketPhysicalRow, interpolatePacketPhysicalRow, h]
      ring
  · simp [packetLiteralK, packetKRowIndex]
    ring

/-- Literal matrix replacement form: varying one physical row changes only
the corresponding scalar row of `K_Theta`. -/
theorem packetLiteralK_replace_eq_updateRow
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (x : ThreeBlockVariable W → ℂ) (i : ThreeBlockIndex W)
    (r : PacketPhysicalRow i → ℂ) :
    packetLiteralK z CL BR Theta (replacePacketPhysicalRow x i r) =
      (packetLiteralK z CL BR Theta x).updateRow (packetKRowIndex i)
        (fun q => packetLiteralK z CL BR Theta
          (replacePacketPhysicalRow x i r) (packetKRowIndex i) q) := by
  ext p q
  by_cases hp : p = packetKRowIndex i
  · subst p
    simp [Matrix.updateRow_apply]
  · rw [Matrix.updateRow_ne hp]
    exact packetLiteralK_replace_other_row z CL BR Theta x i r p q hp

/-- Determinant interpolation for one of the `3W` physical packet rows. -/
theorem packetLiteralK_det_physicalRow_interpolate
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (x : ThreeBlockVariable W → ℂ) (i : ThreeBlockIndex W)
    (r s : PacketPhysicalRow i → ℂ) (t : ℂ) :
    (packetLiteralK z CL BR Theta
      (replacePacketPhysicalRow x i
        (interpolatePacketPhysicalRow t r s))).det =
      (1 - t) *
          (packetLiteralK z CL BR Theta
            (replacePacketPhysicalRow x i r)).det +
        t * (packetLiteralK z CL BR Theta
          (replacePacketPhysicalRow x i s)).det := by
  let A := packetLiteralK z CL BR Theta x
  let rr := fun q => packetLiteralK z CL BR Theta
    (replacePacketPhysicalRow x i r) (packetKRowIndex i) q
  let ss := fun q => packetLiteralK z CL BR Theta
    (replacePacketPhysicalRow x i s) (packetKRowIndex i) q
  have hinterp :
      packetLiteralK z CL BR Theta
          (replacePacketPhysicalRow x i
            (interpolatePacketPhysicalRow t r s)) =
        A.updateRow (packetKRowIndex i)
          (fun q => (1 - t) * rr q + t * ss q) := by
    ext p q
    by_cases hp : p = packetKRowIndex i
    · subst p
      simp only [Matrix.updateRow_self]
      exact packetLiteralK_changed_row_interpolate
        z CL BR Theta x i r s t q
    · rw [Matrix.updateRow_ne hp]
      exact packetLiteralK_replace_other_row z CL BR Theta x i
        (interpolatePacketPhysicalRow t r s) p q hp
  have hr := packetLiteralK_replace_eq_updateRow
    z CL BR Theta x i r
  have hs := packetLiteralK_replace_eq_updateRow
    z CL BR Theta x i s
  rw [hinterp, det_updateRow_interpolate]
  simpa [A, rr, ss] using congrArg Matrix.det hr ▸
    congrArg Matrix.det hs ▸ rfl

end LiteralPacketMatrix

section CallerFacing

variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

local instance packetMultiaffineCallerSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W => (toLex x : W ⊕ₗ W)) toLex.injective

/-- Caller-facing deterministic multiaffinity statement from Proposition
10.9: the concrete packet polynomial is affine separately in every one of its
`3W` physical packet rows. -/
theorem packetBoundaryPolynomial_isAffineInPhysicalRow
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (i : ThreeBlockIndex W) :
    IsAffineInPacketPhysicalRow i
      (packetBoundaryPolynomial z CL BR Theta) := by
  intro x r s t
  rw [eval_packetBoundaryPolynomial_eq_packetLiteralK_det,
    eval_packetBoundaryPolynomial_eq_packetLiteralK_det,
    eval_packetBoundaryPolynomial_eq_packetLiteralK_det]
  exact packetLiteralK_det_physicalRow_interpolate
    z CL BR Theta x i r s t

/-- Fully instantiated deterministic data used before the probabilistic
coefficient-evaluation step in Proposition 10.9.  The nonzero conclusion is
constructed from the concrete packet objects; the caller supplies only the
paper's invertibility assumptions. -/
theorem packetBoundaryPolynomial_multiaffine_and_ne_zero
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (hTheta : IsUnit Theta.det) :
    (∀ i : ThreeBlockIndex W,
      IsAffineInPacketPhysicalRow i
        (packetBoundaryPolynomial z CL BR Theta)) ∧
      packetBoundaryPolynomial z CL BR Theta ≠ 0 := by
  constructor
  · exact fun i =>
      packetBoundaryPolynomial_isAffineInPhysicalRow z CL BR Theta i
  · exact packetBoundaryPolynomial_ne_zero
      z CL BR hCL hBR Theta hTheta

end CallerFacing

end BernoulliSection10
