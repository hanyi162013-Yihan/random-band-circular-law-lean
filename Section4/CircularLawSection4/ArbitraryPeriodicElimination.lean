import CircularLawSection4.PeriodicMatrixCertificate
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Arbitrary-length cyclic transfer elimination

This module constructs the open-chain data required by
`unitPivotCyclicEliminationCertificate` for every finite list of square
transfer matrices.  The indexing type is recursive: the empty chain contains
one dummy copy of the state space, and prepending a transfer appends one more
copy.  The dummy block makes the construction cover the empty list as well as
all positive lengths without a separate determinant argument.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

section RecursiveOpenChain

universe u v

variable {R : Type u} {n : Type v} [CommRing R]
variable [Fintype n] [DecidableEq n]

/-- Recursive index of the open-chain variables.  There is one dummy state
for the empty word and one additional state for every prepended transfer. -/
@[reducible] def RecursiveOpenIndex : List (Matrix n n R) → Type v
  | [] => n
  | _ :: Ts => RecursiveOpenIndex Ts ⊕ n

instance recursiveOpenIndexFintype :
    (Ts : List (Matrix n n R)) → Fintype (RecursiveOpenIndex Ts)
  | [] => by
      change Fintype n
      infer_instance
  | _ :: Ts => by
      change Fintype (RecursiveOpenIndex Ts ⊕ n)
      letI := recursiveOpenIndexFintype Ts
      exact inferInstance

instance recursiveOpenIndexDecidableEq :
    (Ts : List (Matrix n n R)) → DecidableEq (RecursiveOpenIndex Ts)
  | [] => by
      change DecidableEq n
      infer_instance
  | _ :: Ts => by
      change DecidableEq (RecursiveOpenIndex Ts ⊕ n)
      letI := recursiveOpenIndexDecidableEq Ts
      exact inferInstance

/-- Right-hand side coupling the distinguished cyclic state to the open
variables. -/
def recursiveForwardRhs :
    (Ts : List (Matrix n n R)) → Matrix (RecursiveOpenIndex Ts) n R
  | [] => -(1 : Matrix n n R)
  | T :: _Ts => Matrix.fromRows 0 (-T)

/-- Unit block-triangular pivot for the open chain. -/
def recursiveOpenPivot :
    (Ts : List (Matrix n n R)) →
      Matrix (RecursiveOpenIndex Ts) (RecursiveOpenIndex Ts) R
  | [] => 1
  | _ :: Ts =>
      Matrix.fromBlocks (recursiveOpenPivot Ts) (recursiveForwardRhs Ts) 0 1

/-- Forward-substitution solution.  It is written with the sign convention
`A * X = B` used by `unitPivotCyclicEliminationCertificate`. -/
def recursiveForwardSolution :
    (Ts : List (Matrix n n R)) → Matrix (RecursiveOpenIndex Ts) n R
  | [] => -(1 : Matrix n n R)
  | T :: Ts =>
      Matrix.fromRows (recursiveForwardSolution Ts * T) (-T)

/-- Closure row selecting the terminal open-chain state. -/
def recursiveClosure :
    (Ts : List (Matrix n n R)) → Matrix n (RecursiveOpenIndex Ts) R
  | [] => -(1 : Matrix n n R)
  | _ :: Ts => Matrix.fromCols (recursiveClosure Ts) 0

@[simp] theorem recursiveOpenPivot_det
    (Ts : List (Matrix n n R)) : (recursiveOpenPivot Ts).det = 1 := by
  induction Ts with
  | nil => simp [recursiveOpenPivot]
  | cons T Ts ih =>
      rw [recursiveOpenPivot, Matrix.det_fromBlocks_zero₂₁, ih]
      simp

theorem recursiveOpenPivot_mul_forwardSolution
    (Ts : List (Matrix n n R)) :
    recursiveOpenPivot Ts * recursiveForwardSolution Ts =
      recursiveForwardRhs Ts := by
  induction Ts with
  | nil =>
      simp only [recursiveOpenPivot, recursiveForwardSolution,
        recursiveForwardRhs, Matrix.one_mul]
  | cons T Ts ih =>
      rw [recursiveOpenPivot, recursiveForwardSolution, recursiveForwardRhs,
        Matrix.fromBlocks_mul_fromRows]
      rw [Matrix.fromRows_ext_iff]
      constructor
      · rw [← Matrix.mul_assoc, ih]
        simp
      · simp

theorem recursiveClosure_mul_forwardSolution
    (Ts : List (Matrix n n R)) :
    recursiveClosure Ts * recursiveForwardSolution Ts =
      chronologicalProduct Ts := by
  induction Ts with
  | nil =>
      simp only [recursiveClosure, recursiveForwardSolution,
        neg_mul_neg, Matrix.one_mul, chronologicalProduct_nil]
  | cons T Ts ih =>
      rw [recursiveClosure, recursiveForwardSolution,
        Matrix.fromCols_mul_fromRows]
      rw [← Matrix.mul_assoc, ih, chronologicalProduct_cons]
      simp

/-- The concrete cyclic coefficient matrix attached to an arbitrary transfer
list.  Its open block is the recursive unit pivot and its last equation closes
the terminal state back to the distinguished state. -/
def recursivePeriodicSystem (Ts : List (Matrix n n R)) :
    Matrix (RecursiveOpenIndex Ts ⊕ n) (RecursiveOpenIndex Ts ⊕ n) R :=
  unitPivotCyclicSystem (recursiveOpenPivot Ts)
    (recursiveForwardRhs Ts) (recursiveClosure Ts)

/-- Matrix-level periodic elimination certificate for every finite transfer
list, including the empty list. -/
def arbitraryLengthPeriodicEliminationCertificate
    (Ts : List (Matrix n n R)) :
    PeriodicEliminationCertificate (recursivePeriodicSystem Ts)
      (chronologicalProduct Ts) := by
  exact unitPivotCyclicEliminationCertificate
    (recursiveOpenPivot Ts) (recursiveForwardRhs Ts) (recursiveClosure Ts)
    (recursiveForwardSolution Ts) (chronologicalProduct Ts)
    (recursiveOpenPivot_det Ts)
    (recursiveOpenPivot_mul_forwardSolution Ts)
    (recursiveClosure_mul_forwardSolution Ts)

/-- Determinant formula obtained from the arbitrary-length concrete matrix
certificate. -/
theorem recursivePeriodicSystem_det (Ts : List (Matrix n n R)) :
    (recursivePeriodicSystem Ts).det =
      (1 - chronologicalProduct Ts).det := by
  simpa [arbitraryLengthPeriodicEliminationCertificate,
      unitPivotCyclicEliminationCertificate] using
    periodicTransfer_det (recursivePeriodicSystem Ts)
      (chronologicalProduct Ts)
      (arbitraryLengthPeriodicEliminationCertificate Ts)

end RecursiveOpenChain

end CircularLawSection4
