import CircularLawSection4.Exterior

/-!
# Periodic transfer determinant and denominator clearing

This file formalizes the algebraic conclusion of Lemma `lem:periodic-det`
from two explicit interfaces.  The cyclic state-system elimination is a
checkable matrix certificate with left/right operations and reduction to
`diag(I, I-P)`.  The physical-to-state denominator-clearing step is currently
recorded only as a determinant equality.  The desired alternating-trace
identity is then proved from these visible inputs.

The certificate boundary is useful here because the paper suppresses the
ordering of the `N(2W)` state coordinates and consequently suppresses the
deterministic sign.  A concrete ordering can discharge the certificate by
finite matrix calculation without changing the theorem below.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

section Products

variable {R : Type*} [CommRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The manuscript's chronological convention: `[T₁,...,Tₘ]` is multiplied
as `Tₘ ... T₁`. -/
def chronologicalProduct : List (Matrix n n R) → Matrix n n R
  | [] => 1
  | T :: Ts => chronologicalProduct Ts * T

@[simp] theorem chronologicalProduct_nil :
    chronologicalProduct ([] : List (Matrix n n R)) = 1 := rfl

@[simp] theorem chronologicalProduct_cons (T : Matrix n n R)
    (Ts : List (Matrix n n R)) :
    chronologicalProduct (T :: Ts) = chronologicalProduct Ts * T := rfl

theorem chronologicalProduct_append (Ts Us : List (Matrix n n R)) :
    chronologicalProduct (Ts ++ Us) =
      chronologicalProduct Us * chronologicalProduct Ts := by
  induction Ts with
  | nil => simp
  | cons T Ts ih =>
      simp only [List.cons_append, chronologicalProduct_cons, ih]
      rw [Matrix.mul_assoc]

end Products

section ClearedCompounds

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- One denominator-cleared exterior step, `β ⋅ wedge^k T`. -/
def clearedCompound (k : ℕ) (β : ℂ) (T : Matrix n n ℂ) :
    Matrix (powersetCard n k) (powersetCard n k) ℂ :=
  β • compound k T

/-- Chronological product of the cleared exterior steps. -/
def clearedCompoundProduct (k : ℕ) :
    List (ℂ × Matrix n n ℂ) →
      Matrix (powersetCard n k) (powersetCard n k) ℂ
  | [] => compound k 1
  | (β, T) :: xs =>
      clearedCompoundProduct k xs * clearedCompound k β T

/-- The product of all row denominators. -/
def clearingFactor (xs : List (ℂ × Matrix n n ℂ)) : ℂ :=
  (xs.map Prod.fst).prod

def transferList (xs : List (ℂ × Matrix n n ℂ)) :
    List (Matrix n n ℂ) :=
  xs.map Prod.snd

/-- Functoriality after all denominators are cleared.  Crucially, every
exterior degree receives one copy of every `β`, not `β^k`. -/
theorem clearedCompoundProduct_eq (k : ℕ)
    (xs : List (ℂ × Matrix n n ℂ)) :
    clearedCompoundProduct k xs =
      clearingFactor xs •
        compound k (chronologicalProduct (transferList xs)) := by
  induction xs with
  | nil =>
      simp [clearedCompoundProduct, clearingFactor, transferList]
  | cons x xs ih =>
      rcases x with ⟨β, T⟩
      simp only [clearedCompoundProduct, clearingFactor, transferList,
        List.map_cons, List.prod_cons, chronologicalProduct_cons]
      rw [ih, compound_mul]
      ext s t
      simp only [clearedCompound, Matrix.mul_apply, Matrix.smul_apply,
        smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [clearingFactor, transferList]
      ring

/-- Alternating full-exterior trace of the cleared transfer product. -/
def clearedSignedCompoundTrace
    (xs : List (ℂ × Matrix n n ℂ)) : ℂ :=
  ∑ s : Finset n, (-1 : ℂ) ^ s.card *
    clearedCompoundProduct s.card xs (ofCard rfl) (ofCard rfl)

/-- The exact algebraic denominator-cleared Floquet identity. -/
theorem cleared_floquet_exterior_identity
    (xs : List (ℂ × Matrix n n ℂ)) :
    clearedSignedCompoundTrace xs =
      clearingFactor xs *
        (1 - chronologicalProduct (transferList xs)).det := by
  rw [det_one_sub_eq_signedCompoundTrace]
  unfold clearedSignedCompoundTrace signedCompoundTrace
  simp_rw [clearedCompoundProduct_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp [mul_left_comm]

end ClearedCompounds

section Elimination

variable {R : Type*} [CommRing R]
variable {e n : Type*}
variable [Fintype e] [DecidableEq e] [Fintype n] [DecidableEq n]

/-- A checkable Gaussian-elimination certificate for the cyclic state
equations.  It records reduction to `diag(I, I-P)` and the determinant signs
of the row/column operations; it does not contain the desired conclusion. -/
structure PeriodicEliminationCertificate
    (system : Matrix (e ⊕ n) (e ⊕ n) R)
    (monodromy : Matrix n n R) where
  left : Matrix (e ⊕ n) (e ⊕ n) R
  right : Matrix (e ⊕ n) (e ⊕ n) R
  leftSign : R
  rightSign : R
  leftSign_spec : leftSign = 1 ∨ leftSign = -1
  rightSign_spec : rightSign = 1 ∨ rightSign = -1
  det_left : left.det = leftSign
  det_right : right.det = rightSign
  reduction :
    left * system * right =
      Matrix.fromBlocks (1 : Matrix e e R) 0 0 (1 - monodromy)

/-- First evaluation of the cyclic state determinant. -/
theorem periodicTransfer_det
    (system : Matrix (e ⊕ n) (e ⊕ n) R)
    (M : Matrix n n R)
    (c : PeriodicEliminationCertificate system M) :
    system.det = (c.leftSign * c.rightSign) * (1 - M).det := by
  have h := congrArg Matrix.det c.reduction
  rw [Matrix.det_mul, Matrix.det_mul, c.det_left, c.det_right,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul] at h
  have hsquare :
      (c.leftSign * c.rightSign) * (c.leftSign * c.rightSign) = 1 := by
    rcases c.leftSign_spec with hleft | hleft <;>
      rcases c.rightSign_spec with hright | hright <;>
      simp [hleft, hright]
  calc
    system.det = 1 * system.det := by rw [one_mul]
    _ = ((c.leftSign * c.rightSign) *
          (c.leftSign * c.rightSign)) * system.det := by rw [hsquare]
    _ = (c.leftSign * c.rightSign) *
          (c.leftSign * system.det * c.rightSign) := by ring
    _ = (c.leftSign * c.rightSign) * (1 - M).det := by rw [h]

theorem periodicTransfer_sign
    (system : Matrix (e ⊕ n) (e ⊕ n) R)
    (M : Matrix n n R)
    (c : PeriodicEliminationCertificate system M) :
    c.leftSign * c.rightSign = 1 ∨
      c.leftSign * c.rightSign = -1 := by
  rcases c.leftSign_spec with hleft | hleft <;>
    rcases c.rightSign_spec with hright | hright <;>
    simp [hleft, hright]

end Elimination

section PeriodicDeterminant

variable {p e n : Type*}
variable [Fintype p] [DecidableEq p]
variable [Fintype e] [DecidableEq e]
variable [Fintype n] [DecidableEq n] [LinearOrder n]

/-- The two interfaces used in Lemma `lem:periodic-det`.

`stateReduction` is elimination of `s₂,...,s_N`, while
`physicalElimination` records the determinant-level result of eliminating the
coordinate-identification equations.  Unlike `stateReduction`, the latter is
not yet constructed here from explicit elimination matrices. -/
structure PeriodicDeterminantCertificate where
  physical : Matrix p p ℂ
  state : Matrix (e ⊕ n) (e ⊕ n) ℂ
  steps : List (ℂ × Matrix n n ℂ)
  physicalSign : ℂ
  physicalSign_spec : physicalSign = 1 ∨ physicalSign = -1
  physicalElimination :
    physical.det = physicalSign * clearingFactor steps * state.det
  stateReduction : PeriodicEliminationCertificate state
    (chronologicalProduct (transferList steps))

/-- The deterministic sign produced by the two eliminations. -/
def PeriodicDeterminantCertificate.sign
    (d : PeriodicDeterminantCertificate (p := p) (e := e) (n := n)) : ℂ :=
  d.physicalSign * (d.stateReduction.leftSign * d.stateReduction.rightSign)

omit [LinearOrder n] in
theorem PeriodicDeterminantCertificate.sign_spec
    (d : PeriodicDeterminantCertificate (p := p) (e := e) (n := n)) :
    d.sign = 1 ∨ d.sign = -1 := by
  rcases d.physicalSign_spec with hp | hp <;>
    rcases d.stateReduction.leftSign_spec with hl | hl <;>
    rcases d.stateReduction.rightSign_spec with hr | hr <;>
    simp [PeriodicDeterminantCertificate.sign, hp, hl, hr]

/-- **Periodic determinant identity (Lemma 4.2).**  The physical cyclic
determinant is the deterministic sign times the alternating trace of all
denominator-cleared exterior transfer products. -/
theorem periodic_determinant_identity
    (d : PeriodicDeterminantCertificate (p := p) (e := e) (n := n)) :
    d.physical.det = d.sign * clearedSignedCompoundTrace d.steps := by
  have hstate := periodicTransfer_det d.state
    (chronologicalProduct (transferList d.steps)) d.stateReduction
  have hclear := cleared_floquet_exterior_identity d.steps
  rw [d.physicalElimination, hstate, hclear]
  unfold PeriodicDeterminantCertificate.sign
  ring

/-- Existential-sign version matching the statement in the manuscript. -/
theorem exists_sign_periodic_determinant_identity
    (d : PeriodicDeterminantCertificate (p := p) (e := e) (n := n)) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      d.physical.det = σ * clearedSignedCompoundTrace d.steps :=
  ⟨d.sign, d.sign_spec, periodic_determinant_identity d⟩

end PeriodicDeterminant

end CircularLawSection4
