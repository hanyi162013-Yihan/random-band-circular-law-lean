import CircularLawSection4.Periodic

/-!
# Matrix-level certificates for the two eliminations in the periodic determinant

This scratch module strengthens the physical-to-state boundary in
`CircularLawSection4.Periodic`: the determinant equality is derived from an
explicit row scaling, a reindexing, and left/right elimination matrices.

It also gives a concrete, generic two-step cyclic state system and constructs
its `PeriodicEliminationCertificate` without assuming any determinant identity.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

section PhysicalElimination

variable {R : Type*} [CommRing R]
variable {p e n a : Type*}
variable [Fintype p] [DecidableEq p]
variable [Fintype e] [DecidableEq e]
variable [Fintype n] [DecidableEq n]
variable [Fintype a] [DecidableEq a]

/-- A matrix-level certificate for the manuscript's first evaluation of the
cyclic state system.

`rowScaling` records all denominator-clearing row factors.  After applying it,
`order` exposes the physical variables as the second block, and the two
unimodular elimination matrices reduce the result to `diag(I, physical)`.
Consequently the physical determinant equality is a theorem, rather than a
field of the interface. -/
structure PhysicalEliminationCertificate
    (physical : Matrix p p R)
    (state : Matrix (e ⊕ n) (e ⊕ n) R)
    (clearing : R) where
  order : (e ⊕ n) ≃ (a ⊕ p)
  rowScaling : Matrix (e ⊕ n) (e ⊕ n) R
  left : Matrix (a ⊕ p) (a ⊕ p) R
  right : Matrix (a ⊕ p) (a ⊕ p) R
  leftSign : R
  rightSign : R
  leftSign_spec : leftSign = 1 ∨ leftSign = -1
  rightSign_spec : rightSign = 1 ∨ rightSign = -1
  det_rowScaling : rowScaling.det = clearing
  det_left : left.det = leftSign
  det_right : right.det = rightSign
  reduction :
    left * Matrix.reindex order order (rowScaling * state) * right =
      Matrix.fromBlocks (1 : Matrix a a R) 0 0 physical

/-- The total sign of the physical-coordinate elimination. -/
def PhysicalEliminationCertificate.sign
    {physical : Matrix p p R}
    {state : Matrix (e ⊕ n) (e ⊕ n) R} {clearing : R}
    (c : PhysicalEliminationCertificate (a := a) physical state clearing) : R :=
  c.leftSign * c.rightSign

theorem PhysicalEliminationCertificate.sign_spec
    {physical : Matrix p p R}
    {state : Matrix (e ⊕ n) (e ⊕ n) R} {clearing : R}
    (c : PhysicalEliminationCertificate (a := a) physical state clearing) :
    c.sign = 1 ∨ c.sign = -1 := by
  rcases c.leftSign_spec with hl | hl <;>
    rcases c.rightSign_spec with hr | hr <;>
    simp [PhysicalEliminationCertificate.sign, hl, hr]

/-- The determinant-level first evaluation, derived solely from the explicit
matrix reduction in `PhysicalEliminationCertificate`. -/
theorem physicalElimination_det
    (physical : Matrix p p R)
    (state : Matrix (e ⊕ n) (e ⊕ n) R) (clearing : R)
    (c : PhysicalEliminationCertificate (a := a) physical state clearing) :
    physical.det = c.sign * clearing * state.det := by
  have h := congrArg Matrix.det c.reduction
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self,
    Matrix.det_mul, c.det_left, c.det_right, c.det_rowScaling,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul] at h
  rw [← h]
  simp only [PhysicalEliminationCertificate.sign]
  ring

end PhysicalElimination

section StrengthenedPeriodicCertificate

variable {p e n a : Type*}
variable [Fintype p] [DecidableEq p]
variable [Fintype e] [DecidableEq e]
variable [Fintype n] [DecidableEq n] [LinearOrder n]
variable [Fintype a] [DecidableEq a]

/-- A strengthened version of `PeriodicDeterminantCertificate`.  Both
eliminations are now matrix-level certificates; neither stores the target
determinant identity as an assumption. -/
structure MatrixPeriodicDeterminantCertificate where
  physical : Matrix p p ℂ
  state : Matrix (e ⊕ n) (e ⊕ n) ℂ
  steps : List (ℂ × Matrix n n ℂ)
  physicalReduction : PhysicalEliminationCertificate (a := a) physical state
    (clearingFactor steps)
  stateReduction : PeriodicEliminationCertificate state
    (chronologicalProduct (transferList steps))

/-- The sign contributed by the two explicit reductions. -/
def MatrixPeriodicDeterminantCertificate.sign
    (d : MatrixPeriodicDeterminantCertificate
      (p := p) (e := e) (n := n) (a := a)) : ℂ :=
  d.physicalReduction.sign *
    (d.stateReduction.leftSign * d.stateReduction.rightSign)

omit [LinearOrder n] in
theorem MatrixPeriodicDeterminantCertificate.sign_spec
    (d : MatrixPeriodicDeterminantCertificate
      (p := p) (e := e) (n := n) (a := a)) :
    d.sign = 1 ∨ d.sign = -1 := by
  rcases d.physicalReduction.sign_spec with hp | hp <;>
    rcases d.stateReduction.leftSign_spec with hl | hl <;>
    rcases d.stateReduction.rightSign_spec with hr | hr <;>
    simp [MatrixPeriodicDeterminantCertificate.sign, hp, hl, hr]

/-- A matrix-certified version of Lemma 4.2. -/
theorem periodic_determinant_identity_of_matrix_cert
    (d : MatrixPeriodicDeterminantCertificate
      (p := p) (e := e) (n := n) (a := a)) :
    d.physical.det = d.sign * clearedSignedCompoundTrace d.steps := by
  have hphysical := physicalElimination_det d.physical d.state
    (clearingFactor d.steps) d.physicalReduction
  have hstate := periodicTransfer_det d.state
    (chronologicalProduct (transferList d.steps)) d.stateReduction
  have hclear := cleared_floquet_exterior_identity d.steps
  rw [hphysical, hstate, hclear]
  unfold MatrixPeriodicDeterminantCertificate.sign
  ring

/-- Forget the explicit physical reduction and recover the older determinant-
level interface.  This is intentionally one-way. -/
def MatrixPeriodicDeterminantCertificate.toPeriodicDeterminantCertificate
    (d : MatrixPeriodicDeterminantCertificate
      (p := p) (e := e) (n := n) (a := a)) :
    PeriodicDeterminantCertificate (p := p) (e := e) (n := n) where
  physical := d.physical
  state := d.state
  steps := d.steps
  physicalSign := d.physicalReduction.sign
  physicalSign_spec := d.physicalReduction.sign_spec
  physicalElimination := physicalElimination_det d.physical d.state
    (clearingFactor d.steps) d.physicalReduction
  stateReduction := d.stateReduction

end StrengthenedPeriodicCertificate

section GenericBlockCyclicSystem

variable {R : Type*} [CommRing R]
variable {e n : Type*}
variable [Fintype e] [DecidableEq e]
variable [Fintype n] [DecidableEq n]

omit [DecidableEq e] [DecidableEq n] in
/-- Multiplication of two `2 × 2` block matrices. -/
theorem fromBlocks_mul_fromBlocks
    {A E : Matrix e e R} {B F : Matrix e n R}
    {C G : Matrix n e R} {D H : Matrix n n R} :
    Matrix.fromBlocks A B C D * Matrix.fromBlocks E F G H =
      Matrix.fromBlocks (A * E + B * G) (A * F + B * H)
        (C * E + D * G) (C * F + D * H) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type]

/-- A block cyclic system with a unit-determinant open-chain pivot `A`.
The last block equation closes the chain through `C`. -/
def unitPivotCyclicSystem
    (A : Matrix e e R) (B : Matrix e n R) (C : Matrix n e R) :
    Matrix (e ⊕ n) (e ⊕ n) R :=
  Matrix.fromBlocks A B C 1

/-- Explicit left eliminator for a unit-pivot system. -/
def unitPivotCyclicLeft
    (A : Matrix e e R) (C : Matrix n e R) :
    Matrix (e ⊕ n) (e ⊕ n) R :=
  Matrix.fromBlocks A⁻¹ 0 (-C * A⁻¹) 1

/-- Explicit column cleanup for a supplied open-chain solution `X = A⁻¹B`. -/
def unitPivotCyclicRight (X : Matrix e n R) :
    Matrix (e ⊕ n) (e ⊕ n) R :=
  Matrix.fromBlocks 1 (-X) 0 1

@[simp] theorem unitPivotCyclicLeft_det
    (A : Matrix e e R) (C : Matrix n e R) (hA : A.det = 1) :
    (unitPivotCyclicLeft A C).det = 1 := by
  rw [unitPivotCyclicLeft, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_nonsing_inv, hA]
  simp

@[simp] theorem unitPivotCyclicRight_det (X : Matrix e n R) :
    (unitPivotCyclicRight X).det = 1 := by
  rw [unitPivotCyclicRight, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- Generic matrix-level Schur elimination with a supplied forward solution.

The hypotheses `A * X = B` and `C * X = M` are local matrix equalities.  In an
arbitrary-length transfer chain, `A` is the unit lower-bidiagonal open pivot,
`X` is obtained by forward substitution, and `M` is the monodromy. -/
theorem unitPivotCyclic_reduction
    (A : Matrix e e R) (B : Matrix e n R) (C : Matrix n e R)
    (X : Matrix e n R) (M : Matrix n n R)
    (hA : A.det = 1) (hAX : A * X = B) (hCX : C * X = M) :
    unitPivotCyclicLeft A C * unitPivotCyclicSystem A B C *
        unitPivotCyclicRight X =
      Matrix.fromBlocks (1 : Matrix e e R) 0 0 (1 - M) := by
  have hunit : IsUnit A.det := by simp [hA]
  have hinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hunit
  have hinvB : A⁻¹ * B = X := by
    rw [← hAX, ← Matrix.mul_assoc, hinvA, Matrix.one_mul]
  rw [unitPivotCyclicLeft, unitPivotCyclicSystem, unitPivotCyclicRight,
    fromBlocks_mul_fromBlocks, fromBlocks_mul_fromBlocks]
  simp [hinvA, hinvB, hCX, Matrix.mul_assoc, sub_eq_add_neg, add_comm]

/-- A reusable constructor for cyclic state elimination.  It replaces a
determinant-level premise by three directly checkable open-chain facts. -/
def unitPivotCyclicEliminationCertificate
    (A : Matrix e e R) (B : Matrix e n R) (C : Matrix n e R)
    (X : Matrix e n R) (M : Matrix n n R)
    (hA : A.det = 1) (hAX : A * X = B) (hCX : C * X = M) :
    PeriodicEliminationCertificate (unitPivotCyclicSystem A B C) M where
  left := unitPivotCyclicLeft A C
  right := unitPivotCyclicRight X
  leftSign := 1
  rightSign := 1
  leftSign_spec := Or.inl rfl
  rightSign_spec := Or.inl rfl
  det_left := unitPivotCyclicLeft_det A C hA
  det_right := unitPivotCyclicRight_det X
  reduction := unitPivotCyclic_reduction A B C X M hA hAX hCX

end GenericBlockCyclicSystem

section TwoStepCyclicSystem

variable {R : Type*} [CommRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The coefficient matrix of the two cyclic equations
`s₁ - T₀ s₀ = 0` and `s₀ - T₁ s₁ = 0`, with state columns
ordered as `(s₁, s₀)`. -/
def twoStepPeriodicSystem (T₀ T₁ : Matrix n n R) :
    Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks 1 (-T₀) (-T₁) 1

/-- The concrete forward-elimination row matrix for the two-step system. -/
def twoStepPeriodicLeft (T₁ : Matrix n n R) :
    Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks 1 0 T₁ 1

/-- The concrete column cleanup matrix for the two-step system. -/
def twoStepPeriodicRight (T₀ : Matrix n n R) :
    Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks 1 T₀ 0 1

@[simp] theorem twoStepPeriodicLeft_det (T₁ : Matrix n n R) :
    (twoStepPeriodicLeft T₁).det = 1 := by
  rw [twoStepPeriodicLeft, Matrix.det_fromBlocks_zero₁₂]
  simp

@[simp] theorem twoStepPeriodicRight_det (T₀ : Matrix n n R) :
    (twoStepPeriodicRight T₀).det = 1 := by
  rw [twoStepPeriodicRight, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- The displayed two-step eliminators reduce the cyclic system to
`diag(I, I - T₁T₀)` at matrix level. -/
theorem twoStepPeriodic_reduction (T₀ T₁ : Matrix n n R) :
    twoStepPeriodicLeft T₁ * twoStepPeriodicSystem T₀ T₁ *
        twoStepPeriodicRight T₀ =
      Matrix.fromBlocks (1 : Matrix n n R) 0 0 (1 - T₁ * T₀) := by
  rw [twoStepPeriodicLeft, twoStepPeriodicSystem, twoStepPeriodicRight,
    fromBlocks_mul_fromBlocks, fromBlocks_mul_fromBlocks]
  simp [mul_neg, sub_eq_add_neg, add_comm]

/-- A generic constructor for the cyclic state-elimination certificate.  The
only inputs are the two transfer matrices. -/
def twoStepPeriodicEliminationCertificate (T₀ T₁ : Matrix n n R) :
    PeriodicEliminationCertificate
      (twoStepPeriodicSystem T₀ T₁) (T₁ * T₀) where
  left := twoStepPeriodicLeft T₁
  right := twoStepPeriodicRight T₀
  leftSign := 1
  rightSign := 1
  leftSign_spec := Or.inl rfl
  rightSign_spec := Or.inl rfl
  det_left := twoStepPeriodicLeft_det T₁
  det_right := twoStepPeriodicRight_det T₀
  reduction := twoStepPeriodic_reduction T₀ T₁

/-- Determinant formula obtained from the concrete two-step constructor. -/
theorem twoStepPeriodic_det (T₀ T₁ : Matrix n n R) :
    (twoStepPeriodicSystem T₀ T₁).det = (1 - T₁ * T₀).det := by
  simpa [twoStepPeriodicEliminationCertificate] using
    periodicTransfer_det (twoStepPeriodicSystem T₀ T₁)
    (T₁ * T₀) (twoStepPeriodicEliminationCertificate T₀ T₁)

end TwoStepCyclicSystem

end CircularLawSection4
