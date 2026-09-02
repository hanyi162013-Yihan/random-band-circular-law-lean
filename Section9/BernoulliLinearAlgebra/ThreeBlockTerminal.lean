import BernoulliLinearAlgebra.TerminalCoefficient
import BernoulliLinearAlgebra.DoubleEliminationConcrete
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.Tactic

/-!
# The concrete three-block terminal determinant

This file encodes the seven-block path mask (7.11)--(7.12), used in
Section 9.1.3, with raw unit-entry-weight variables. The full packet is
written as `O ⊕ C`, where `O = L ⊕ R`; this is the same set of rows and
columns as the paper's `L ⊕ C ⊕ R`, with a harmless rebracketing.

The two absent fresh rectangles are exactly `L_row × R_col` and
`R_row × L_col`.  The deterministic deformation is supported on `O × O`.
The multivariate polynomial below is literally the determinant of the
polynomial-valued terminal matrix, not an abstract coefficient family.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix MvPolynomial

/-- Outer coordinates: `false` is the left block and `true` is the right
block. -/
abbrev ThreeBlockOuter (w : Type*) := Bool × w

/-- Full packet coordinates, represented as `(L ⊕ R) ⊕ C`. -/
abbrev ThreeBlockIndex (w : Type*) := Sum (ThreeBlockOuter w) w

/-- Rebracketing of the outer coordinate used here with `W ⊕ W`. -/
def threeBlockOuterEquiv (w : Type*) : ThreeBlockOuter w ≃ (w ⊕ w) where
  toFun
    | (false, i) => Sum.inl i
    | (true, i) => Sum.inr i
  invFun
    | Sum.inl i => (false, i)
    | Sum.inr i => (true, i)
  left_inv := by intro i; rcases i with ⟨b, i⟩; cases b <;> rfl
  right_inv := by intro i; cases i <;> rfl

/-- Rebracketing `(L ⊕ R) ⊕ C ≃ L ⊕ (C ⊕ R)` used to connect the
terminal determinant to `concreteHTheta`. -/
def threeBlockIndexEquiv (w : Type*) : ThreeBlockIndex w ≃ Packet3 w where
  toFun
    | Sum.inl (false, i) => Sum.inl i
    | Sum.inr i => Sum.inr (Sum.inl i)
    | Sum.inl (true, i) => Sum.inr (Sum.inr i)
  invFun
    | Sum.inl i => Sum.inl (false, i)
    | Sum.inr (Sum.inl i) => Sum.inr i
    | Sum.inr (Sum.inr i) => Sum.inl (true, i)
  left_inv := by
    intro i
    rcases i with i | i
    · rcases i with ⟨b, i⟩
      cases b <;> rfl
    · rfl
  right_inv := by
    intro i
    rcases i with i | i
    · rfl
    · cases i <;> rfl

/-- The seven-block path mask.  Only the two off-diagonal outer rectangles
are absent. -/
def threeBlockFresh {w : Type*} :
    ThreeBlockIndex w → ThreeBlockIndex w → Prop
  | Sum.inl i, Sum.inl j => i.1 = j.1
  | _, _ => True

instance {w : Type*} [DecidableEq w] :
    DecidableRel (@threeBlockFresh w) := by
  intro i j
  cases i <;> cases j <;> simp only [threeBlockFresh] <;> infer_instance

@[simp] theorem threeBlockFresh_refl {w : Type*}
    (i : ThreeBlockIndex w) : threeBlockFresh i i := by
  cases i with
  | inl i => simp [threeBlockFresh]
  | inr i => simp [threeBlockFresh]

/-- One formal scalar variable for every fresh entry of the seven blocks. -/
abbrev ThreeBlockVariable (w : Type*) :=
  {p : ThreeBlockIndex w × ThreeBlockIndex w //
    threeBlockFresh p.1 p.2}

@[simp] theorem threeBlockFresh_center_row {w : Type*}
    (i : w) (j : ThreeBlockIndex w) :
    threeBlockFresh (Sum.inr i) j := by
  cases j <;> simp [threeBlockFresh]

@[simp] theorem threeBlockFresh_center_col {w : Type*}
    (i : ThreeBlockIndex w) (j : w) :
    threeBlockFresh i (Sum.inr j) := by
  cases i <;> simp [threeBlockFresh]

@[simp] theorem threeBlockFresh_left_left {w : Type*} (i j : w) :
    threeBlockFresh (Sum.inl (false, i)) (Sum.inl (false, j)) := by
  simp [threeBlockFresh]

@[simp] theorem threeBlockFresh_right_right {w : Type*} (i j : w) :
    threeBlockFresh (Sum.inl (true, i)) (Sum.inl (true, j)) := by
  simp [threeBlockFresh]

@[simp] theorem not_threeBlockFresh_left_right {w : Type*} (i j : w) :
    ¬threeBlockFresh (Sum.inl (false, i)) (Sum.inl (true, j)) := by
  simp [threeBlockFresh]

@[simp] theorem not_threeBlockFresh_right_left {w : Type*} (i j : w) :
    ¬threeBlockFresh (Sum.inl (true, i)) (Sum.inl (false, j)) := by
  simp [threeBlockFresh]

/-- The paper's `Emb_O(Q)`: it agrees with `Q` on outer rows and columns
and vanishes whenever a central coordinate is involved. -/
def threeBlockEmb {w : Type*} (Q : Matrix (ThreeBlockOuter w)
    (ThreeBlockOuter w) ℂ) :
    Matrix (ThreeBlockIndex w) (ThreeBlockIndex w) ℂ
  | Sum.inl i, Sum.inl j => Q i j
  | _, _ => 0

@[simp] theorem threeBlockEmb_outer {w : Type*}
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (i j : ThreeBlockOuter w) :
    threeBlockEmb Q (Sum.inl i) (Sum.inl j) = Q i j := rfl

@[simp] theorem threeBlockEmb_center_row {w : Type*}
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (i : w) (j : ThreeBlockIndex w) :
    threeBlockEmb Q (Sum.inr i) j = 0 := by
  cases j <;> rfl

@[simp] theorem threeBlockEmb_center_col {w : Type*}
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (i : ThreeBlockIndex w) (j : w) :
    threeBlockEmb Q i (Sum.inr j) = 0 := by
  cases i <;> rfl

/-- `Emb_O` agrees exactly with the outer embedding used in the concrete
double-elimination module. -/
theorem threeBlockEmb_reindex_eq_packetOuterEmbedding {w : Type*}
    [Fintype w] [DecidableEq w]
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) :
    (threeBlockEmb Q).submatrix (threeBlockIndexEquiv w).symm
        (threeBlockIndexEquiv w).symm =
      packetOuterEmbedding
        (Q.submatrix (threeBlockOuterEquiv w).symm
          (threeBlockOuterEquiv w).symm) := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [threeBlockEmb, threeBlockIndexEquiv,
        threeBlockOuterEquiv, packetOuterEmbedding,
        packetOuterInjection, packetOuterProjection, Matrix.mul_apply,
        Matrix.one_apply]
    · rcases j with j | j <;>
        simp [threeBlockEmb, threeBlockIndexEquiv,
          threeBlockOuterEquiv, packetOuterEmbedding,
          packetOuterInjection, packetOuterProjection, Matrix.mul_apply,
          Matrix.one_apply]
  · rcases i with i | i
    · rcases j with j | j
      · simp [threeBlockEmb, threeBlockIndexEquiv,
          threeBlockOuterEquiv, packetOuterEmbedding,
          packetOuterInjection, packetOuterProjection, Matrix.mul_apply,
          Matrix.one_apply]
      · rcases j with j | j <;>
          simp [threeBlockEmb, threeBlockIndexEquiv,
            threeBlockOuterEquiv, packetOuterEmbedding,
            packetOuterInjection, packetOuterProjection, Matrix.mul_apply,
            Matrix.one_apply]
    · rcases j with j | j
      · simp [threeBlockEmb, threeBlockIndexEquiv,
          threeBlockOuterEquiv, packetOuterEmbedding,
          packetOuterInjection, packetOuterProjection, Matrix.mul_apply,
          Matrix.one_apply]
      · rcases j with j | j
        · simp [threeBlockEmb, threeBlockIndexEquiv,
            threeBlockOuterEquiv, packetOuterEmbedding,
            packetOuterInjection, packetOuterProjection, Matrix.mul_apply,
            Matrix.one_apply]
        · simp [threeBlockEmb, threeBlockIndexEquiv,
            threeBlockOuterEquiv, packetOuterEmbedding,
            packetOuterInjection, packetOuterProjection, Matrix.mul_apply,
            Matrix.one_apply]

/-- The fresh matrix `Delta(x)`. -/
def threeBlockDelta {w : Type*} [DecidableEq w]
    (x : ThreeBlockVariable w → ℂ) :
    Matrix (ThreeBlockIndex w) (ThreeBlockIndex w) ℂ :=
  fun i j => if h : threeBlockFresh i j then x ⟨(i, j), h⟩ else 0

@[simp] theorem threeBlockDelta_apply_of_fresh {w : Type*} [DecidableEq w]
    (x : ThreeBlockVariable w → ℂ) (i j : ThreeBlockIndex w)
    (h : threeBlockFresh i j) :
    threeBlockDelta x i j = x ⟨(i, j), h⟩ := by
  simp [threeBlockDelta, h]

@[simp] theorem threeBlockDelta_apply_of_not_fresh {w : Type*} [DecidableEq w]
    (x : ThreeBlockVariable w → ℂ) (i j : ThreeBlockIndex w)
    (h : ¬threeBlockFresh i j) :
    threeBlockDelta x i j = 0 := by
  simp [threeBlockDelta, h]

/-- The seven literal `W × W` blocks of `Delta(x)`, in paper order
`A_L,B_L,C_C,A_C,B_C,C_R,A_R`. -/
def threeBlockAL {w : Type*} (x : ThreeBlockVariable w → ℂ) : Matrix w w ℂ :=
  fun i j => x ⟨(Sum.inl (false, i), Sum.inl (false, j)), by simp⟩

def threeBlockBL {w : Type*} (x : ThreeBlockVariable w → ℂ) : Matrix w w ℂ :=
  fun i j => x ⟨(Sum.inl (false, i), Sum.inr j), by simp⟩

def threeBlockCC {w : Type*} (x : ThreeBlockVariable w → ℂ) : Matrix w w ℂ :=
  fun i j => x ⟨(Sum.inr i, Sum.inl (false, j)), by simp⟩

def threeBlockAC {w : Type*} (x : ThreeBlockVariable w → ℂ) : Matrix w w ℂ :=
  fun i j => x ⟨(Sum.inr i, Sum.inr j), by simp⟩

def threeBlockBC {w : Type*} (x : ThreeBlockVariable w → ℂ) : Matrix w w ℂ :=
  fun i j => x ⟨(Sum.inr i, Sum.inl (true, j)), by simp⟩

def threeBlockCR {w : Type*} (x : ThreeBlockVariable w → ℂ) : Matrix w w ℂ :=
  fun i j => x ⟨(Sum.inl (true, i), Sum.inr j), by simp⟩

def threeBlockAR {w : Type*} (x : ThreeBlockVariable w → ℂ) : Matrix w w ℂ :=
  fun i j => x ⟨(Sum.inl (true, i), Sum.inl (true, j)), by simp⟩

/-- Under the explicit rebracketing, `Delta(x)` is exactly the concrete
seven-block packet core used by the double elimination. -/
theorem threeBlockDelta_reindex_eq_packetCore {w : Type*}
    [Fintype w] [DecidableEq w] (x : ThreeBlockVariable w → ℂ) :
    (threeBlockDelta x).submatrix (threeBlockIndexEquiv w).symm
        (threeBlockIndexEquiv w).symm =
      packetCore (threeBlockAL x) (threeBlockBL x) (threeBlockCC x)
        (threeBlockAC x) (threeBlockBC x) (threeBlockCR x)
        (threeBlockAR x) := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [threeBlockDelta, threeBlockIndexEquiv, packetCore,
        threeBlockAL]
    · rcases j with j | j
      · simp [threeBlockDelta, threeBlockIndexEquiv, packetCore,
          threeBlockBL]
      · simp [threeBlockDelta, threeBlockIndexEquiv, packetCore,
          threeBlockFresh]
  · rcases i with i | i
    · rcases j with j | j
      · simp [threeBlockDelta, threeBlockIndexEquiv, packetCore,
          threeBlockCC]
      · rcases j with j | j
        · simp [threeBlockDelta, threeBlockIndexEquiv, packetCore,
            threeBlockAC]
        · simp [threeBlockDelta, threeBlockIndexEquiv, packetCore,
            threeBlockBC]
    · rcases j with j | j
      · simp [threeBlockDelta, threeBlockIndexEquiv, packetCore,
          threeBlockFresh]
      · rcases j with j | j
        · simp [threeBlockDelta, threeBlockIndexEquiv, packetCore,
            threeBlockCR]
        · simp [threeBlockDelta, threeBlockIndexEquiv, packetCore,
            threeBlockAR]

/-- The concrete terminal matrix
`H(Q;x) = Delta(x) - z I + Emb_O(Q)`. -/
def threeBlockH {w : Type*} [Fintype w] [DecidableEq w]
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (z : ℂ) (x : ThreeBlockVariable w → ℂ) :
    Matrix (ThreeBlockIndex w) (ThreeBlockIndex w) ℂ :=
  threeBlockDelta x - z • (1 : Matrix (ThreeBlockIndex w)
    (ThreeBlockIndex w) ℂ) + threeBlockEmb Q

/-- Express an outer matrix written on `W ⊕ W` in the Boolean outer
coordinates used by the terminal determinant. -/
def threeBlockOuterOfPacket {w : Type*}
    (Q : Matrix (w ⊕ w) (w ⊕ w) ℂ) :
    Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ :=
  Q.submatrix (threeBlockOuterEquiv w) (threeBlockOuterEquiv w)

@[simp] theorem threeBlockOuterOfPacket_reindex {w : Type*}
    (Q : Matrix (w ⊕ w) (w ⊕ w) ℂ) :
    (threeBlockOuterOfPacket Q).submatrix
        (threeBlockOuterEquiv w).symm (threeBlockOuterEquiv w).symm = Q := by
  ext i j
  simp [threeBlockOuterOfPacket]

/-- At zero spectral shift, the reindexed terminal matrix is exactly a
seven-block packet core plus the concrete outer embedding. -/
theorem threeBlockH_zero_reindex {w : Type*}
    [Fintype w] [DecidableEq w]
    (Q : Matrix (w ⊕ w) (w ⊕ w) ℂ)
    (x : ThreeBlockVariable w → ℂ) :
    (threeBlockH (threeBlockOuterOfPacket Q) 0 x).submatrix
        (threeBlockIndexEquiv w).symm (threeBlockIndexEquiv w).symm =
      packetCore (threeBlockAL x) (threeBlockBL x) (threeBlockCC x)
          (threeBlockAC x) (threeBlockBC x) (threeBlockCR x)
          (threeBlockAR x) +
        packetOuterEmbedding Q := by
  rw [show threeBlockH (threeBlockOuterOfPacket Q) 0 x =
      threeBlockDelta x + threeBlockEmb (threeBlockOuterOfPacket Q) by
    simp [threeBlockH]]
  ext i j
  have hDelta := congrFun (congrFun
    (threeBlockDelta_reindex_eq_packetCore x) i) j
  have hEmb := congrFun (congrFun
    (threeBlockEmb_reindex_eq_packetOuterEmbedding
      (threeBlockOuterOfPacket Q)) i) j
  change threeBlockDelta x ((threeBlockIndexEquiv w).symm i)
      ((threeBlockIndexEquiv w).symm j) = _ at hDelta
  change threeBlockEmb (threeBlockOuterOfPacket Q)
      ((threeBlockIndexEquiv w).symm i)
      ((threeBlockIndexEquiv w).symm j) = _ at hEmb
  simp only [Matrix.submatrix_apply, Matrix.add_apply]
  rw [hDelta, hEmb, threeBlockOuterOfPacket_reindex]

/-- Direct bridge to the `concreteHTheta` produced by the five-block Schur
elimination. -/
theorem threeBlockH_zero_reindex_eq_concreteHTheta {w : Type*}
    [Fintype w] [DecidableEq w]
    (x : ThreeBlockVariable w → ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ) :
    (threeBlockH
        (threeBlockOuterOfPacket
          (endpointFactor CL BR *
            transferCoordinateMap Theta11 Theta12 Theta21 Theta22))
        0 x).submatrix
          (threeBlockIndexEquiv w).symm (threeBlockIndexEquiv w).symm =
      concreteHTheta
        (threeBlockAL x) (threeBlockBL x) (threeBlockCC x)
        (threeBlockAC x) (threeBlockBC x) (threeBlockCR x)
        (threeBlockAR x) CL BR Theta11 Theta12 Theta21 Theta22 := by
  simpa [concreteHTheta] using
    threeBlockH_zero_reindex
      (endpointFactor CL BR *
        transferCoordinateMap Theta11 Theta12 Theta21 Theta22) x

/-- Determinant form of the bridge.  Rebracketing contributes no sign
because rows and columns are reindexed by the same equivalence. -/
theorem threeBlockH_zero_det_eq_concreteHTheta_det {w : Type*}
    [Fintype w] [DecidableEq w]
    (x : ThreeBlockVariable w → ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ) :
    (threeBlockH
        (threeBlockOuterOfPacket
          (endpointFactor CL BR *
            transferCoordinateMap Theta11 Theta12 Theta21 Theta22))
        0 x).det =
      (concreteHTheta
        (threeBlockAL x) (threeBlockBL x) (threeBlockCC x)
        (threeBlockAC x) (threeBlockBC x) (threeBlockCR x)
        (threeBlockAR x) CL BR Theta11 Theta12 Theta21 Theta22).det := by
  calc
    _ = ((threeBlockH
          (threeBlockOuterOfPacket
            (endpointFactor CL BR *
              transferCoordinateMap Theta11 Theta12 Theta21 Theta22))
          0 x).submatrix
            (threeBlockIndexEquiv w).symm
            (threeBlockIndexEquiv w).symm).det :=
      (Matrix.det_submatrix_equiv_self
        (threeBlockIndexEquiv w).symm _).symm
    _ = _ := congrArg Matrix.det
      (threeBlockH_zero_reindex_eq_concreteHTheta x CL BR
        Theta11 Theta12 Theta21 Theta22)

/-- Polynomial-valued `Delta`. -/
def threeBlockDeltaPolynomial {w : Type*} [DecidableEq w] :
    Matrix (ThreeBlockIndex w) (ThreeBlockIndex w)
      (MvPolynomial (ThreeBlockVariable w) ℂ) :=
  fun i j => if h : threeBlockFresh i j then X ⟨(i, j), h⟩ else 0

/-- The polynomial-valued terminal matrix. -/
def threeBlockHPolynomial {w : Type*} [Fintype w] [DecidableEq w]
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (z : ℂ) :
    Matrix (ThreeBlockIndex w) (ThreeBlockIndex w)
      (MvPolynomial (ThreeBlockVariable w) ℂ) :=
  threeBlockDeltaPolynomial -
      (C z : MvPolynomial (ThreeBlockVariable w) ℂ) •
      (1 : Matrix (ThreeBlockIndex w) (ThreeBlockIndex w)
        (MvPolynomial (ThreeBlockVariable w) ℂ)) +
    (threeBlockEmb Q).map C

/-- The paper's determinant polynomial `p_Q(x) = det H(Q;x)`. -/
def threeBlockDetPolynomial {w : Type*} [Fintype w] [DecidableEq w]
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (z : ℂ) : MvPolynomial (ThreeBlockVariable w) ℂ :=
  (threeBlockHPolynomial Q z).det

@[simp] theorem eval_threeBlockDeltaPolynomial {w : Type*}
    [Fintype w] [DecidableEq w] (x : ThreeBlockVariable w → ℂ) :
    (threeBlockDeltaPolynomial (w := w)).map (eval x) =
      threeBlockDelta x := by
  ext i j
  by_cases h : threeBlockFresh i j
  · simp [threeBlockDeltaPolynomial, threeBlockDelta, h]
  · simp [threeBlockDeltaPolynomial, threeBlockDelta, h]

/-- Evaluating the formal terminal matrix gives the concrete terminal
matrix entry-for-entry. -/
@[simp] theorem eval_threeBlockHPolynomial {w : Type*}
    [Fintype w] [DecidableEq w]
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (z : ℂ) (x : ThreeBlockVariable w → ℂ) :
    (threeBlockHPolynomial Q z).map (eval x) = threeBlockH Q z x := by
  ext i j
  by_cases hfresh : threeBlockFresh i j <;>
    by_cases hij : i = j <;>
    simp [threeBlockHPolynomial, threeBlockH,
      threeBlockDeltaPolynomial, threeBlockDelta, hfresh,
      hij]

/-- Hence the formal polynomial is literally the determinant polynomial
specified in the paper. -/
theorem eval_threeBlockDetPolynomial {w : Type*}
    [Fintype w] [DecidableEq w]
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (z : ℂ) (x : ThreeBlockVariable w → ℂ) :
    eval x (threeBlockDetPolynomial Q z) = (threeBlockH Q z x).det := by
  rw [threeBlockDetPolynomial, (eval x).map_det,
    show (eval x).mapMatrix (threeBlockHPolynomial Q z) =
      threeBlockH Q z x from eval_threeBlockHPolynomial Q z x]

/-- Evaluation of the formal terminal polynomial is therefore the concrete
three-packet determinant produced by double elimination. -/
theorem eval_threeBlockDetPolynomial_zero_eq_concreteHTheta_det {w : Type*}
    [Fintype w] [DecidableEq w]
    (x : ThreeBlockVariable w → ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ) :
    eval x
      (threeBlockDetPolynomial
        (threeBlockOuterOfPacket
          (endpointFactor CL BR *
            transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) 0) =
      (concreteHTheta
        (threeBlockAL x) (threeBlockBL x) (threeBlockCC x)
        (threeBlockAC x) (threeBlockBC x) (threeBlockCR x)
        (threeBlockAR x) CL BR Theta11 Theta12 Theta21 Theta22).det := by
  rw [eval_threeBlockDetPolynomial,
    threeBlockH_zero_det_eq_concreteHTheta_det]

/-- Simultaneous translation of precisely the diagonal fresh variables.
This is the concrete substitution `x_e ↦ x_e - z` on diagonal entries. -/
def threeBlockDiagonalShift {w : Type*} [DecidableEq w]
    (z : ℂ) (x : ThreeBlockVariable w → ℂ) :
    ThreeBlockVariable w → ℂ := fun e =>
  if e.1.1 = e.1.2 then x e - z else x e

/-- The spectral shift is exactly a translation of the diagonal fresh
variables; it is not an additional deterministic deformation. -/
theorem threeBlockH_eq_zeroShift_diagonalTranslation {w : Type*}
    [Fintype w] [DecidableEq w]
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (z : ℂ) (x : ThreeBlockVariable w → ℂ) :
    threeBlockH Q z x =
      threeBlockH Q 0 (threeBlockDiagonalShift z x) := by
  ext i j
  by_cases hfresh : threeBlockFresh i j <;>
    by_cases hij : i = j
  · subst j
    simp [threeBlockH, threeBlockDelta, threeBlockDiagonalShift]
  · simp [threeBlockH, threeBlockDelta, threeBlockDiagonalShift,
      hfresh, hij]
  · exact (hfresh (hij ▸ threeBlockFresh_refl j)).elim
  · simp [threeBlockH, threeBlockDelta, hfresh, hij]

/-- Determinant-polynomial version of the diagonal translation identity. -/
theorem eval_threeBlockDetPolynomial_shift {w : Type*}
    [Fintype w] [DecidableEq w]
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (z : ℂ) (x : ThreeBlockVariable w → ℂ) :
    eval x (threeBlockDetPolynomial Q z) =
      eval (threeBlockDiagonalShift z x)
        (threeBlockDetPolynomial Q 0) := by
  rw [eval_threeBlockDetPolynomial, eval_threeBlockDetPolynomial,
    threeBlockH_eq_zeroShift_diagonalTranslation]

section PolynomialBoundaryBridge

variable {w : Type*} [Fintype w] [DecidableEq w]

/-- The seven formal blocks, now as polynomial-valued matrices. -/
def threeBlockALPolynomial :
    Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ) :=
  fun i j => X ⟨(Sum.inl (false, i), Sum.inl (false, j)), by simp⟩

def threeBlockBLPolynomial :
    Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ) :=
  fun i j => X ⟨(Sum.inl (false, i), Sum.inr j), by simp⟩

def threeBlockCCPolynomial :
    Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ) :=
  fun i j => X ⟨(Sum.inr i, Sum.inl (false, j)), by simp⟩

def threeBlockACPolynomial :
    Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ) :=
  fun i j => X ⟨(Sum.inr i, Sum.inr j), by simp⟩

def threeBlockBCPolynomial :
    Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ) :=
  fun i j => X ⟨(Sum.inr i, Sum.inl (true, j)), by simp⟩

def threeBlockCRPolynomial :
    Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ) :=
  fun i j => X ⟨(Sum.inl (true, i), Sum.inr j), by simp⟩

def threeBlockARPolynomial :
    Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ) :=
  fun i j => X ⟨(Sum.inl (true, i), Sum.inl (true, j)), by simp⟩

/-- Map a complex matrix to a constant polynomial matrix. -/
def threeBlockCMatrix {m n : Type*} (A : Matrix m n ℂ) :
    Matrix m n (MvPolynomial (ThreeBlockVariable w) ℂ) :=
  A.map C

/-- The polynomial-valued boundary matrix before the second elimination. -/
def threeBlockConcreteKPolynomial
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ) :
    Matrix (Packet3 w ⊕ (w ⊕ w)) (Packet3 w ⊕ (w ⊕ w))
      (MvPolynomial (ThreeBlockVariable w) ℂ) :=
  concreteKTheta
    threeBlockALPolynomial threeBlockBLPolynomial
    threeBlockCCPolynomial threeBlockACPolynomial
    threeBlockBCPolynomial threeBlockCRPolynomial
    threeBlockARPolynomial
    (threeBlockCMatrix CL) (threeBlockCMatrix BR)
    (threeBlockCMatrix Theta11) (threeBlockCMatrix Theta12)
    (threeBlockCMatrix Theta21) (threeBlockCMatrix Theta22)

/-- Its polynomial-valued Schur complement. -/
def threeBlockConcreteHPolynomial
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ) :
    Matrix (Packet3 w) (Packet3 w)
      (MvPolynomial (ThreeBlockVariable w) ℂ) :=
  concreteHTheta
    threeBlockALPolynomial threeBlockBLPolynomial
    threeBlockCCPolynomial threeBlockACPolynomial
    threeBlockBCPolynomial threeBlockCRPolynomial
    threeBlockARPolynomial
    (threeBlockCMatrix CL) (threeBlockCMatrix BR)
    (threeBlockCMatrix Theta11) (threeBlockCMatrix Theta12)
    (threeBlockCMatrix Theta21) (threeBlockCMatrix Theta22)

/-- The same boundary matrix with the spectral shift inserted in the three
physical diagonal blocks. -/
def threeBlockConcreteKPolynomialShifted
    (z : ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ) :
    Matrix (Packet3 w ⊕ (w ⊕ w)) (Packet3 w ⊕ (w ⊕ w))
      (MvPolynomial (ThreeBlockVariable w) ℂ) :=
  concreteKTheta
    (threeBlockALPolynomial -
      (C z : MvPolynomial (ThreeBlockVariable w) ℂ) •
        (1 : Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ)))
    threeBlockBLPolynomial threeBlockCCPolynomial
    (threeBlockACPolynomial -
      (C z : MvPolynomial (ThreeBlockVariable w) ℂ) •
        (1 : Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ)))
    threeBlockBCPolynomial threeBlockCRPolynomial
    (threeBlockARPolynomial -
      (C z : MvPolynomial (ThreeBlockVariable w) ℂ) •
        (1 : Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ)))
    (threeBlockCMatrix CL) (threeBlockCMatrix BR)
    (threeBlockCMatrix Theta11) (threeBlockCMatrix Theta12)
    (threeBlockCMatrix Theta21) (threeBlockCMatrix Theta22)

/-- The corresponding shifted polynomial Schur complement. -/
def threeBlockConcreteHPolynomialShifted
    (z : ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ) :
    Matrix (Packet3 w) (Packet3 w)
      (MvPolynomial (ThreeBlockVariable w) ℂ) :=
  concreteHTheta
    (threeBlockALPolynomial -
      (C z : MvPolynomial (ThreeBlockVariable w) ℂ) •
        (1 : Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ)))
    threeBlockBLPolynomial threeBlockCCPolynomial
    (threeBlockACPolynomial -
      (C z : MvPolynomial (ThreeBlockVariable w) ℂ) •
        (1 : Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ)))
    threeBlockBCPolynomial threeBlockCRPolynomial
    (threeBlockARPolynomial -
      (C z : MvPolynomial (ThreeBlockVariable w) ℂ) •
        (1 : Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ)))
    (threeBlockCMatrix CL) (threeBlockCMatrix BR)
    (threeBlockCMatrix Theta11) (threeBlockCMatrix Theta12)
    (threeBlockCMatrix Theta21) (threeBlockCMatrix Theta22)

omit [Fintype w] in
/-- Shifting all three diagonal blocks of a packet core is the same as
subtracting a scalar identity from the assembled packet. -/
theorem packetCore_diagonalShift {R : Type*} [CommRing R]
    (z : R) (DL BL CC DC BC CR DR : Matrix w w R) :
    packetCore (DL - z • 1) BL CC (DC - z • 1) BC CR (DR - z • 1) =
      packetCore DL BL CC DC BC CR DR - z • 1 := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [packetCore, Matrix.one_apply]
    · cases j <;> simp [packetCore]
  · rcases i with i | i
    · rcases j with j | j
      · simp [packetCore]
      · cases j <;> simp [packetCore, Matrix.one_apply]
    · rcases j with j | j
      · simp [packetCore]
      · cases j <;> simp [packetCore, Matrix.one_apply]

/-- The shifted Schur complement differs from the zero-shift one by the
scalar packet identity. -/
theorem threeBlockConcreteHPolynomialShifted_eq
    (z : ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ) :
    threeBlockConcreteHPolynomialShifted z CL BR Theta11 Theta12
        Theta21 Theta22 =
      threeBlockConcreteHPolynomial CL BR Theta11 Theta12 Theta21 Theta22 -
        (C z : MvPolynomial (ThreeBlockVariable w) ℂ) •
          (1 : Matrix (Packet3 w) (Packet3 w)
            (MvPolynomial (ThreeBlockVariable w) ℂ)) := by
  unfold threeBlockConcreteHPolynomialShifted
    threeBlockConcreteHPolynomial concreteHTheta
  rw [packetCore_diagonalShift]
  abel

/-- Pointwise matrix bridge at an arbitrary spectral shift. -/
theorem threeBlockH_reindex_eq_concreteHTheta_shifted
    (z : ℂ) (x : ThreeBlockVariable w → ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ) :
    (threeBlockH
        (threeBlockOuterOfPacket
          (endpointFactor CL BR *
            transferCoordinateMap Theta11 Theta12 Theta21 Theta22))
        z x).submatrix
          (threeBlockIndexEquiv w).symm (threeBlockIndexEquiv w).symm =
      concreteHTheta
        (threeBlockAL x - z • 1) (threeBlockBL x) (threeBlockCC x)
        (threeBlockAC x - z • 1) (threeBlockBC x) (threeBlockCR x)
        (threeBlockAR x - z • 1)
        CL BR Theta11 Theta12 Theta21 Theta22 := by
  have hshift :
      threeBlockH
          (threeBlockOuterOfPacket
            (endpointFactor CL BR *
              transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) z x =
        threeBlockH
          (threeBlockOuterOfPacket
            (endpointFactor CL BR *
              transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) 0 x -
            z • 1 := by
    ext i j
    simp [threeBlockH]
    ring
  have hconcrete :
      concreteHTheta
          (threeBlockAL x - z • 1) (threeBlockBL x) (threeBlockCC x)
          (threeBlockAC x - z • 1) (threeBlockBC x) (threeBlockCR x)
          (threeBlockAR x - z • 1)
          CL BR Theta11 Theta12 Theta21 Theta22 =
        concreteHTheta
          (threeBlockAL x) (threeBlockBL x) (threeBlockCC x)
          (threeBlockAC x) (threeBlockBC x) (threeBlockCR x)
          (threeBlockAR x) CL BR Theta11 Theta12 Theta21 Theta22 - z • 1 := by
    unfold concreteHTheta
    rw [packetCore_diagonalShift]
    abel
  rw [hshift, hconcrete]
  ext i j
  have hzero := congrFun (congrFun
    (threeBlockH_zero_reindex_eq_concreteHTheta x CL BR Theta11
      Theta12 Theta21 Theta22) i) j
  change
    threeBlockH
        (threeBlockOuterOfPacket
          (endpointFactor CL BR *
            transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) 0 x
        ((threeBlockIndexEquiv w).symm i)
        ((threeBlockIndexEquiv w).symm j) -
      z * (1 : Matrix (ThreeBlockIndex w) (ThreeBlockIndex w) ℂ)
        ((threeBlockIndexEquiv w).symm i)
        ((threeBlockIndexEquiv w).symm j) = _
  change threeBlockH _ 0 x _ _ = _ at hzero
  rw [hzero]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- Determinant version of the arbitrary-shift matrix bridge. -/
theorem threeBlockH_det_eq_concreteHTheta_shifted_det
    (z : ℂ) (x : ThreeBlockVariable w → ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ) :
    (threeBlockH
        (threeBlockOuterOfPacket
          (endpointFactor CL BR *
            transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) z x).det =
      (concreteHTheta
        (threeBlockAL x - z • 1) (threeBlockBL x) (threeBlockCC x)
        (threeBlockAC x - z • 1) (threeBlockBC x) (threeBlockCR x)
        (threeBlockAR x - z • 1)
        CL BR Theta11 Theta12 Theta21 Theta22).det := by
  calc
    _ = ((threeBlockH
        (threeBlockOuterOfPacket
          (endpointFactor CL BR *
            transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) z x).submatrix
          (threeBlockIndexEquiv w).symm
          (threeBlockIndexEquiv w).symm).det :=
      (Matrix.det_submatrix_equiv_self
        (threeBlockIndexEquiv w).symm _).symm
    _ = _ := congrArg Matrix.det
      (threeBlockH_reindex_eq_concreteHTheta_shifted z x CL BR
        Theta11 Theta12 Theta21 Theta22)

omit [Fintype w] [DecidableEq w] in
@[simp] theorem eval_threeBlockCMatrix {m n : Type*}
    (A : Matrix m n ℂ) (x : ThreeBlockVariable w → ℂ) :
    (threeBlockCMatrix (w := w) A).map (eval x) = A := by
  ext i j
  simp [threeBlockCMatrix]

/-- Constant-polynomial matrices preserve the nonsingular inverse. -/
theorem threeBlockCMatrix_inv
    (A : Matrix w w ℂ) (hA : IsUnit A.det) :
    (threeBlockCMatrix (w := w) A)⁻¹ =
      threeBlockCMatrix (w := w) A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  change A.map C * A⁻¹.map C = 1
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv A hA]
  ext i j
  simp [Matrix.one_apply]

@[simp] theorem eval_threeBlockConcreteHPolynomial
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ)
    (h11 : IsUnit Theta11.det)
    (x : ThreeBlockVariable w → ℂ) :
    (threeBlockConcreteHPolynomial CL BR Theta11 Theta12 Theta21 Theta22).map
        (eval x) =
      concreteHTheta
        (threeBlockAL x) (threeBlockBL x) (threeBlockCC x)
        (threeBlockAC x) (threeBlockBC x) (threeBlockCR x)
        (threeBlockAR x) CL BR Theta11 Theta12 Theta21 Theta22 := by
  simp only [threeBlockConcreteHPolynomial, concreteHTheta,
    transferCoordinateMap]
  rw [threeBlockCMatrix_inv Theta11 h11]
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [packetCore, packetOuterEmbedding, endpointFactor,
        packetOuterInjection, packetOuterProjection, threeBlockCMatrix,
        threeBlockALPolynomial, threeBlockAL, Matrix.mul_apply,
        Matrix.one_apply]
    · rcases j with j | j <;>
        simp [packetCore, packetOuterEmbedding, endpointFactor,
          packetOuterInjection, packetOuterProjection, threeBlockCMatrix,
          threeBlockBLPolynomial, threeBlockBL, Matrix.mul_apply,
          Matrix.one_apply]
  · rcases i with i | i
    · rcases j with j | j
      · simp [packetCore, packetOuterEmbedding, endpointFactor,
          packetOuterInjection, packetOuterProjection, threeBlockCMatrix,
          threeBlockCCPolynomial, threeBlockCC, Matrix.mul_apply,
          Matrix.one_apply]
      · rcases j with j | j
        · simp [packetCore, packetOuterEmbedding, endpointFactor,
            packetOuterInjection, packetOuterProjection, threeBlockCMatrix,
            threeBlockACPolynomial, threeBlockAC, Matrix.mul_apply]
        · simp [packetCore, packetOuterEmbedding, endpointFactor,
            packetOuterInjection, packetOuterProjection, threeBlockCMatrix,
            threeBlockBCPolynomial, threeBlockBC, Matrix.mul_apply]
    · rcases j with j | j
      · simp [packetCore, packetOuterEmbedding, endpointFactor,
          packetOuterInjection, packetOuterProjection, threeBlockCMatrix,
          Matrix.mul_apply, Matrix.one_apply]
      · rcases j with j | j
        · simp [packetCore, packetOuterEmbedding, endpointFactor,
            packetOuterInjection, packetOuterProjection, threeBlockCMatrix,
            threeBlockCRPolynomial, threeBlockCR, Matrix.mul_apply,
            Matrix.one_apply]
        · simp [packetCore, packetOuterEmbedding, endpointFactor,
            packetOuterInjection, packetOuterProjection, threeBlockCMatrix,
            threeBlockARPolynomial, threeBlockAR, Matrix.mul_apply,
            Matrix.one_apply]

@[simp] theorem eval_threeBlockConcreteHPolynomialShifted
    (z : ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ)
    (h11 : IsUnit Theta11.det)
    (x : ThreeBlockVariable w → ℂ) :
    (threeBlockConcreteHPolynomialShifted z CL BR Theta11 Theta12
        Theta21 Theta22).map (eval x) =
      concreteHTheta
        (threeBlockAL x - z • 1) (threeBlockBL x) (threeBlockCC x)
        (threeBlockAC x - z • 1) (threeBlockBC x) (threeBlockCR x)
        (threeBlockAR x - z • 1)
        CL BR Theta11 Theta12 Theta21 Theta22 := by
  rw [threeBlockConcreteHPolynomialShifted_eq]
  have hzero := eval_threeBlockConcreteHPolynomial
    CL BR Theta11 Theta12 Theta21 Theta22 h11 x
  have hmap :
      (threeBlockConcreteHPolynomial CL BR Theta11 Theta12 Theta21 Theta22 -
          (C z : MvPolynomial (ThreeBlockVariable w) ℂ) •
            (1 : Matrix (Packet3 w) (Packet3 w)
              (MvPolynomial (ThreeBlockVariable w) ℂ))).map (eval x) =
        (threeBlockConcreteHPolynomial CL BR Theta11 Theta12 Theta21 Theta22).map
            (eval x) - z • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hmap, hzero]
  symm
  unfold concreteHTheta
  rw [packetCore_diagonalShift]
  abel

/-- The determinant of the polynomial Schur complement is exactly the
terminal determinant polynomial at zero shift. -/
theorem threeBlockConcreteHPolynomial_det_eq
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ)
    (h11 : IsUnit Theta11.det) :
    (threeBlockConcreteHPolynomial CL BR Theta11 Theta12 Theta21 Theta22).det =
      threeBlockDetPolynomial
        (threeBlockOuterOfPacket
          (endpointFactor CL BR *
            transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) 0 := by
  apply MvPolynomial.funext
  intro x
  rw [(eval x).map_det,
    show (eval x).mapMatrix
        (threeBlockConcreteHPolynomial CL BR Theta11 Theta12 Theta21 Theta22) =
      concreteHTheta
        (threeBlockAL x) (threeBlockBL x) (threeBlockCC x)
        (threeBlockAC x) (threeBlockBC x) (threeBlockCR x)
        (threeBlockAR x) CL BR Theta11 Theta12 Theta21 Theta22 from
      eval_threeBlockConcreteHPolynomial _ _ _ _ _ _ h11 x,
    eval_threeBlockDetPolynomial,
    threeBlockH_zero_det_eq_concreteHTheta_det]

/-- Polynomial form of the exact determinant scaling from the concrete
five-block double elimination. -/
theorem threeBlockConcreteKPolynomial_det_eq
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ)
    (h11 : IsUnit Theta11.det) :
    (threeBlockConcreteKPolynomial CL BR Theta11 Theta12 Theta21 Theta22).det =
      C Theta11.det *
        threeBlockDetPolynomial
          (threeBlockOuterOfPacket
            (endpointFactor CL BR *
              transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) 0 := by
  have h11C : IsUnit (threeBlockCMatrix (w := w) Theta11).det := by
    rw [show (threeBlockCMatrix (w := w) Theta11).det =
        C Theta11.det by
      exact ((C : ℂ →+* MvPolynomial (ThreeBlockVariable w) ℂ).map_det
        Theta11).symm]
    exact h11.map C
  have h := concreteKTheta_det_eq
    (threeBlockALPolynomial (w := w)) threeBlockBLPolynomial
    threeBlockCCPolynomial threeBlockACPolynomial
    threeBlockBCPolynomial threeBlockCRPolynomial
    threeBlockARPolynomial
    (threeBlockCMatrix CL) (threeBlockCMatrix BR)
    (threeBlockCMatrix Theta11) (threeBlockCMatrix Theta12)
    (threeBlockCMatrix Theta21) (threeBlockCMatrix Theta22) h11C
  change
    (threeBlockConcreteKPolynomial CL BR Theta11 Theta12 Theta21 Theta22).det =
      (threeBlockCMatrix (w := w) Theta11).det *
        (threeBlockConcreteHPolynomial CL BR Theta11 Theta12
          Theta21 Theta22).det at h
  rw [show (threeBlockCMatrix (w := w) Theta11).det =
      C Theta11.det by
    exact ((C : ℂ →+* MvPolynomial (ThreeBlockVariable w) ℂ).map_det
      Theta11).symm,
    threeBlockConcreteHPolynomial_det_eq _ _ _ _ _ _ h11] at h
  exact h

/-- Shifted polynomial Schur complement equals the literal terminal
determinant polynomial at the same spectral parameter. -/
theorem threeBlockConcreteHPolynomialShifted_det_eq
    (z : ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ)
    (h11 : IsUnit Theta11.det) :
    (threeBlockConcreteHPolynomialShifted z CL BR Theta11 Theta12
      Theta21 Theta22).det =
      threeBlockDetPolynomial
        (threeBlockOuterOfPacket
          (endpointFactor CL BR *
            transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) z := by
  apply MvPolynomial.funext
  intro x
  rw [(eval x).map_det,
    show (eval x).mapMatrix
        (threeBlockConcreteHPolynomialShifted z CL BR Theta11 Theta12
          Theta21 Theta22) =
      concreteHTheta
        (threeBlockAL x - z • 1) (threeBlockBL x) (threeBlockCC x)
        (threeBlockAC x - z • 1) (threeBlockBC x) (threeBlockCR x)
        (threeBlockAR x - z • 1)
        CL BR Theta11 Theta12 Theta21 Theta22 from
      eval_threeBlockConcreteHPolynomialShifted z CL BR Theta11 Theta12
        Theta21 Theta22 h11 x,
    eval_threeBlockDetPolynomial,
    threeBlockH_det_eq_concreteHTheta_shifted_det]

/-- Arbitrary-shift polynomial form of the exact determinant scaling. -/
theorem threeBlockConcreteKPolynomialShifted_det_eq
    (z : ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ)
    (h11 : IsUnit Theta11.det) :
    (threeBlockConcreteKPolynomialShifted z CL BR Theta11 Theta12
      Theta21 Theta22).det =
      C Theta11.det *
        threeBlockDetPolynomial
          (threeBlockOuterOfPacket
            (endpointFactor CL BR *
              transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) z := by
  have h11C : IsUnit (threeBlockCMatrix (w := w) Theta11).det := by
    rw [show (threeBlockCMatrix (w := w) Theta11).det =
        C Theta11.det by
      exact ((C : ℂ →+* MvPolynomial (ThreeBlockVariable w) ℂ).map_det
        Theta11).symm]
    exact h11.map C
  have h := concreteKTheta_det_eq
    (threeBlockALPolynomial (w := w) -
      (C z : MvPolynomial (ThreeBlockVariable w) ℂ) •
        (1 : Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ)))
    threeBlockBLPolynomial threeBlockCCPolynomial
    (threeBlockACPolynomial -
      (C z : MvPolynomial (ThreeBlockVariable w) ℂ) •
        (1 : Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ)))
    threeBlockBCPolynomial threeBlockCRPolynomial
    (threeBlockARPolynomial -
      (C z : MvPolynomial (ThreeBlockVariable w) ℂ) •
        (1 : Matrix w w (MvPolynomial (ThreeBlockVariable w) ℂ)))
    (threeBlockCMatrix CL) (threeBlockCMatrix BR)
    (threeBlockCMatrix Theta11) (threeBlockCMatrix Theta12)
    (threeBlockCMatrix Theta21) (threeBlockCMatrix Theta22) h11C
  change
    (threeBlockConcreteKPolynomialShifted z CL BR Theta11 Theta12
      Theta21 Theta22).det =
      (threeBlockCMatrix (w := w) Theta11).det *
        (threeBlockConcreteHPolynomialShifted z CL BR Theta11 Theta12
          Theta21 Theta22).det at h
  rw [show (threeBlockCMatrix (w := w) Theta11).det =
      C Theta11.det by
    exact ((C : ℂ →+* MvPolynomial (ThreeBlockVariable w) ℂ).map_det
      Theta11).symm,
    threeBlockConcreteHPolynomialShifted_det_eq z _ _ _ _ _ _ h11] at h
  exact h

end PolynomialBoundaryBridge

/-- The squarefree exponent associated with a monomial mask. -/
def squarefreeExponent {v : Type*} [DecidableEq v]
    (S : Finset v) : v →₀ ℕ :=
  Finsupp.indicator S (fun _ _ => 1)

/-- The actual coefficient of the determinant polynomial at a squarefree
monomial. -/
def threeBlockDetCoefficient {w : Type*} [Fintype w] [DecidableEq w]
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (z : ℂ) (S : Finset (ThreeBlockVariable w)) : ℂ :=
  (threeBlockDetPolynomial Q z).coeff (squarefreeExponent S)

/-- The complete squarefree coefficient vector of `det H(Q;x)`. -/
def threeBlockDetCoeffVector {w : Type*} [Fintype w] [DecidableEq w]
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (z : ℂ) : CoeffSpace (ThreeBlockVariable w) :=
  WithLp.toLp 2 (threeBlockDetCoefficient Q z)

/-- The coefficient norm `mathfrak C(Q)` of Section 9.1.3. -/
def threeBlockDetCoefficientNorm {w : Type*} [Fintype w] [DecidableEq w]
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (z : ℂ) : ℝ :=
  ‖threeBlockDetCoeffVector Q z‖

@[simp] theorem threeBlockDetCoeffVector_apply {w : Type*}
    [Fintype w] [DecidableEq w]
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (z : ℂ) (S : Finset (ThreeBlockVariable w)) :
    threeBlockDetCoeffVector Q z S = threeBlockDetCoefficient Q z S := rfl

theorem threeBlockDetCoefficientNorm_sq {w : Type*}
    [Fintype w] [DecidableEq w]
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (z : ℂ) :
    threeBlockDetCoefficientNorm Q z ^ 2 =
      ∑ S : Finset (ThreeBlockVariable w),
        ‖threeBlockDetCoefficient Q z S‖ ^ 2 := by
  rw [threeBlockDetCoefficientNorm, ← coeffEnergy_eq_norm_sq]
  rfl

section BoundaryCoefficientScaling

variable {w : Type*} [Fintype w] [DecidableEq w]

/-- The actual squarefree coefficient vector of the concrete five-block
boundary determinant. -/
def threeBlockBoundaryKCoeffVector
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ) :
    CoeffSpace (ThreeBlockVariable w) :=
  WithLp.toLp 2 (fun S =>
    (threeBlockConcreteKPolynomial CL BR Theta11 Theta12 Theta21 Theta22).det.coeff
      (squarefreeExponent S))

/-- Its Euclidean coefficient norm. -/
def threeBlockBoundaryKCoefficientNorm
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ) : ℝ :=
  ‖threeBlockBoundaryKCoeffVector CL BR Theta11 Theta12 Theta21 Theta22‖

/-- Coefficient-by-coefficient form of the exact `det Theta11` scaling. -/
theorem threeBlockBoundaryKCoeffVector_eq_smul
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ)
    (h11 : IsUnit Theta11.det) :
    threeBlockBoundaryKCoeffVector CL BR Theta11 Theta12 Theta21 Theta22 =
      Theta11.det •
        threeBlockDetCoeffVector
          (threeBlockOuterOfPacket
            (endpointFactor CL BR *
              transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) 0 := by
  ext S
  change
    (threeBlockConcreteKPolynomial CL BR Theta11 Theta12 Theta21 Theta22).det.coeff
        (squarefreeExponent S) =
      Theta11.det *
        threeBlockDetCoefficient
          (threeBlockOuterOfPacket
            (endpointFactor CL BR *
              transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) 0 S
  rw [show
    (threeBlockConcreteKPolynomial CL BR Theta11 Theta12 Theta21 Theta22).det =
      C Theta11.det *
        threeBlockDetPolynomial
          (threeBlockOuterOfPacket
            (endpointFactor CL BR *
              transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) 0 from
      threeBlockConcreteKPolynomial_det_eq CL BR Theta11 Theta12
        Theta21 Theta22 h11]
  simp [threeBlockDetCoefficient, MvPolynomial.coeff_C_mul]

/-- Norm form used by the boundary-volume argument.  This closes the
coefficient-scaling hypothesis with the literal determinant coefficients. -/
theorem threeBlockBoundaryKCoefficientNorm_eq
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ)
    (h11 : IsUnit Theta11.det) :
    threeBlockBoundaryKCoefficientNorm CL BR Theta11 Theta12 Theta21 Theta22 =
      ‖Theta11.det‖ *
        threeBlockDetCoefficientNorm
          (threeBlockOuterOfPacket
            (endpointFactor CL BR *
              transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) 0 := by
  rw [threeBlockBoundaryKCoefficientNorm,
    threeBlockBoundaryKCoeffVector_eq_smul _ _ _ _ _ _ h11,
    norm_smul]
  rfl

/-- Squared-energy version of the same exact scaling. -/
theorem threeBlockBoundaryKCoeffEnergy_eq
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ)
    (h11 : IsUnit Theta11.det) :
    coeffEnergy
        (threeBlockBoundaryKCoeffVector CL BR Theta11 Theta12 Theta21 Theta22) =
      ‖Theta11.det‖ ^ 2 *
        coeffEnergy
          (threeBlockDetCoeffVector
            (threeBlockOuterOfPacket
              (endpointFactor CL BR *
                transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) 0) := by
  rw [threeBlockBoundaryKCoeffVector_eq_smul _ _ _ _ _ _ h11,
    coeffEnergy_smul]

/-- Coefficient vector of the boundary determinant with the spectral shift
present in all three physical diagonal blocks. -/
def threeBlockBoundaryKCoeffVectorShifted
    (z : ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ) :
    CoeffSpace (ThreeBlockVariable w) :=
  WithLp.toLp 2 (fun S =>
    (threeBlockConcreteKPolynomialShifted z CL BR Theta11 Theta12
      Theta21 Theta22).det.coeff (squarefreeExponent S))

def threeBlockBoundaryKCoefficientNormShifted
    (z : ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ) : ℝ :=
  ‖threeBlockBoundaryKCoeffVectorShifted z CL BR Theta11 Theta12
      Theta21 Theta22‖

theorem threeBlockBoundaryKCoeffVectorShifted_eq_smul
    (z : ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ)
    (h11 : IsUnit Theta11.det) :
    threeBlockBoundaryKCoeffVectorShifted z CL BR Theta11 Theta12
        Theta21 Theta22 =
      Theta11.det •
        threeBlockDetCoeffVector
          (threeBlockOuterOfPacket
            (endpointFactor CL BR *
              transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) z := by
  ext S
  change
    (threeBlockConcreteKPolynomialShifted z CL BR Theta11 Theta12
      Theta21 Theta22).det.coeff (squarefreeExponent S) =
      Theta11.det *
        threeBlockDetCoefficient
          (threeBlockOuterOfPacket
            (endpointFactor CL BR *
              transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) z S
  rw [show
    (threeBlockConcreteKPolynomialShifted z CL BR Theta11 Theta12
      Theta21 Theta22).det =
      C Theta11.det *
        threeBlockDetPolynomial
          (threeBlockOuterOfPacket
            (endpointFactor CL BR *
              transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) z from
      threeBlockConcreteKPolynomialShifted_det_eq z CL BR Theta11 Theta12
        Theta21 Theta22 h11]
  simp [threeBlockDetCoefficient, MvPolynomial.coeff_C_mul]

/-- The exact arbitrary-shift coefficient scaling required in Section 9.5. -/
theorem threeBlockBoundaryKCoefficientNormShifted_eq
    (z : ℂ)
    (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix w w ℂ)
    (h11 : IsUnit Theta11.det) :
    threeBlockBoundaryKCoefficientNormShifted z CL BR Theta11 Theta12
        Theta21 Theta22 =
      ‖Theta11.det‖ *
        threeBlockDetCoefficientNorm
          (threeBlockOuterOfPacket
            (endpointFactor CL BR *
              transferCoordinateMap Theta11 Theta12 Theta21 Theta22)) z := by
  rw [threeBlockBoundaryKCoefficientNormShifted,
    threeBlockBoundaryKCoeffVectorShifted_eq_smul z _ _ _ _ _ _ h11,
    norm_smul]
  rfl

/-- The terminal coefficient function on the paper's `W ⊕ W` outer
coordinates, with no reindexing exposed to downstream statements. -/
def threeBlockTerminalCoefficientOnPacket (z : ℂ) :
    Matrix (w ⊕ w) (w ⊕ w) ℂ → ℝ :=
  fun Q => threeBlockDetCoefficientNorm (threeBlockOuterOfPacket Q) z

end BoundaryCoefficientScaling

end BernoulliLinearAlgebra
