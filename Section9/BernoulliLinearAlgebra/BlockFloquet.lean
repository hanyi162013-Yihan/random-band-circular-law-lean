import BernoulliLinearAlgebra.AllMinors
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Block Floquet determinants and cleared exterior powers

This file formalizes the algebraic part of Section 9.3.  There are three
layers.

* `stepK`, `stepL`, and `stepTransfer` are the two-by-two block matrices in
  the first-order form of a block three-term recurrence.  The theorem
  `step_factorization` is the identity
  `K s + L s' = L (s' - T s)` with `T = -L⁻¹K`.
* `PeriodicEliminationCertificate` records a determinant-preserving block
  elimination of a periodic transfer system down to `I - M`.  Its fields are
  deliberately matrix equalities and signs, rather than the desired
  determinant formula.  `periodicTransfer_det` proves that formula.
* `FloquetEliminationData` records the other elimination of the augmented
  system to the physical cyclic matrix, together with row factorization by
  the interface blocks.  `block_floquet_identity` combines the two
  eliminations.

The final section proves the denominator-cleared exterior-power expansion
used in (9.70).  The proof uses `compound_mul` at every step and
`det_one_sub_eq_signedCompoundTrace` at the end.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard

section OneStep

variable {R : Type*} [CommRing R]
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The `K` block in the augmented one-step equation `K s + L s' = 0`. -/
def stepK (D C : Matrix W W R) : Matrix (W ⊕ W) (W ⊕ W) R :=
  Matrix.fromBlocks D C (-(1 : Matrix W W R)) 0

/-- The `L` block in the augmented one-step equation `K s + L s' = 0`. -/
def stepL (B : Matrix W W R) : Matrix (W ⊕ W) (W ⊕ W) R :=
  Matrix.fromBlocks B 0 0 1

/-- The augmented interface block has exactly the determinant of the
physical right-interface block. -/
@[simp] theorem stepL_det (B : Matrix W W R) :
    (stepL B).det = B.det := by
  rw [stepL, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/-- The one-step transfer, intrinsically defined as `-L⁻¹K`. -/
def stepTransfer (B D C : Matrix W W R) : Matrix (W ⊕ W) (W ⊕ W) R :=
  -(stepL B)⁻¹ * stepK D C

theorem stepTransfer_def (B D C : Matrix W W R) :
    stepTransfer B D C = -(stepL B)⁻¹ * stepK D C := rfl

/-- On the invertible-interface locus, `-L⁻¹K` is the standard block
companion transfer from the paper. -/
theorem stepTransfer_eq_companion (B D C : Matrix W W R)
    (hB : IsUnit B.det) :
    stepTransfer B D C =
      Matrix.fromBlocks (-(B⁻¹ * D)) (-(B⁻¹ * C)) 1 0 := by
  let _ : Invertible B := Matrix.invertibleOfIsUnitDet B hB
  let _ : Invertible (1 : Matrix W W R) := invertibleOne
  let _ : Invertible (Matrix.fromBlocks B 0 0 (1 : Matrix W W R)) :=
    Matrix.fromBlocksZero₂₁Invertible B 0 (1 : Matrix W W R)
  have hInv : (stepL B)⁻¹ = Matrix.fromBlocks B⁻¹ 0 0 1 := by
    unfold stepL
    rw [← Matrix.invOf_eq_nonsing_inv]
    rw [Matrix.invOf_fromBlocks_zero₂₁_eq]
    simp
  rw [stepTransfer, hInv]
  simp [stepK, Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp

/-- Factoring the one-step equation by its right-interface block. -/
theorem step_factorization (B D C : Matrix W W R)
    (hL : IsUnit (stepL B).det) :
    stepK D C + stepL B * stepTransfer B D C = 0 := by
  rw [stepTransfer, ← Matrix.mul_assoc, Matrix.mul_neg,
    Matrix.mul_nonsing_inv _ hL]
  simp

/-- The one-step factorization with the paper's natural hypothesis
`det B` invertible. -/
theorem step_factorization_of_isUnit_det (B D C : Matrix W W R)
    (hB : IsUnit B.det) :
    stepK D C + stepL B * stepTransfer B D C = 0 :=
  step_factorization B D C (by simpa using hB)

/-- Vector form of `step_factorization`: the original augmented equation is
literally `L (s' - T s)`. -/
theorem step_equation_factorization (B D C : Matrix W W R)
    (hL : IsUnit (stepL B).det) (s s' : (W ⊕ W) → R) :
    stepK D C *ᵥ s + stepL B *ᵥ s' =
      stepL B *ᵥ (s' - stepTransfer B D C *ᵥ s) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  have hmat : stepK D C = -(stepL B * stepTransfer B D C) :=
    eq_neg_of_add_eq_zero_left (step_factorization B D C hL)
  rw [hmat, Matrix.neg_mulVec]
  abel

end OneStep

section Products

variable {R : Type*} [CommRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Chronological product of `[T₁, ..., Tₘ]`, namely `Tₘ ⋯ T₁`. -/
def chronologicalProduct : List (Matrix n n R) → Matrix n n R
  | [] => 1
  | T :: Ts => chronologicalProduct Ts * T

@[simp] theorem chronologicalProduct_nil :
    chronologicalProduct ([] : List (Matrix n n R)) = 1 := rfl

@[simp] theorem chronologicalProduct_cons (T : Matrix n n R)
    (Ts : List (Matrix n n R)) :
    chronologicalProduct (T :: Ts) = chronologicalProduct Ts * T := rfl

/-- Cutting a chronological sequence into an inner and an outer arc reverses
the order of the two arc products, exactly as in `R_out R_partial`. -/
theorem chronologicalProduct_append (Ts Us : List (Matrix n n R)) :
    chronologicalProduct (Ts ++ Us) =
      chronologicalProduct Us * chronologicalProduct Ts := by
  induction Ts with
  | nil => simp
  | cons T Ts ih =>
      simp only [List.cons_append, chronologicalProduct_cons, ih]
      rw [Matrix.mul_assoc]

/-- Sylvester's determinant identity in the sign convention used for the
boundary polynomial: the packet and boundary transfers may be exchanged
inside `det (I - ·)`. -/
theorem det_one_sub_transfer_comm (A B : Matrix n n R) :
    (1 - A * B).det = (1 - B * A).det :=
  Matrix.det_one_sub_mul_comm A B

end Products

section PeriodicElimination

variable {R : Type*} [CommRing R]
variable {e n : Type*}
variable [Fintype e] [DecidableEq e] [Fintype n] [DecidableEq n]

/-- A checkable certificate for Gaussian elimination of a periodic transfer
system.  `left` and `right` are the row and column operations.  The fields
say precisely that they have determinant `±1` and reduce the system to an
identity pivot block plus `I - monodromy`; the Floquet determinant is *not*
a field of the structure.

Here `e` indexes all states eliminated using the identity coefficients in
the first `m-1` transfer equations, while `n` indexes the surviving state.
-/
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

/-- The determinant of a certified periodic transfer system is a fixed sign
times `det (I - M)`.  This is the formal periodic-transfer half of the
Floquet calculation. -/
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

/-- The sign produced by a periodic elimination certificate is genuinely
one of `1,-1`. -/
theorem periodicTransfer_sign
    (system : Matrix (e ⊕ n) (e ⊕ n) R)
    (M : Matrix n n R)
    (c : PeriodicEliminationCertificate system M) :
    c.leftSign * c.rightSign = 1 ∨ c.leftSign * c.rightSign = -1 := by
  rcases c.leftSign_spec with hleft | hleft <;>
    rcases c.rightSign_spec with hright | hright <;>
    simp [hleft, hright]

end PeriodicElimination

section BlockFloquet

variable {p e n w : Type*}
variable [Fintype p] [DecidableEq p]
variable [Fintype e] [DecidableEq e]
variable [Fintype n] [DecidableEq n]
variable [Fintype w] [DecidableEq w]

/-- Data supplied by the two eliminations of the paper's augmented system.

The fields make explicit the facts which depend on a concrete ordering of
block rows and columns:

* `firstElimination` is elimination of the auxiliary `y` variables;
* `rowFactorization` factors all one-step `L` blocks;
* `rowFactor_det` identifies their determinant with the product of interface
  determinants;
* `periodic` is the second, transfer-order elimination certificate.

The final Block Floquet identity is proved below and is not assumed here.
-/
structure FloquetEliminationData
    (p e n w : Type*)
    [Fintype p] [DecidableEq p]
    [Fintype e] [DecidableEq e]
    [Fintype n] [DecidableEq n]
    [Fintype w] [DecidableEq w] where
  physical : Matrix p p ℂ
  augmented : Matrix (e ⊕ n) (e ⊕ n) ℂ
  transferSystem : Matrix (e ⊕ n) (e ⊕ n) ℂ
  rowFactor : Matrix (e ⊕ n) (e ⊕ n) ℂ
  interfaceBlocks : List (Matrix w w ℂ)
  transfers : List (Matrix n n ℂ)
  firstSign : ℂ
  firstSign_spec : firstSign = 1 ∨ firstSign = -1
  firstElimination : augmented.det = firstSign * physical.det
  rowFactorization : augmented = rowFactor * transferSystem
  rowFactor_det : rowFactor.det =
    (interfaceBlocks.map Matrix.det).prod
  periodic : PeriodicEliminationCertificate transferSystem
    (chronologicalProduct transfers)

/-- Product of the determinants of all right-interface blocks. -/
def FloquetEliminationData.interfaceFactor
    (d : FloquetEliminationData p e n w) : ℂ :=
  (d.interfaceBlocks.map Matrix.det).prod

/-- The deterministic ordering sign in the combined Block Floquet identity
is still a sign. -/
theorem FloquetEliminationData.combinedSign_spec
    (d : FloquetEliminationData p e n w) :
    d.firstSign * (d.periodic.leftSign * d.periodic.rightSign) = 1 ∨
      d.firstSign * (d.periodic.leftSign * d.periodic.rightSign) = -1 := by
  rcases d.firstSign_spec with hfirst | hfirst <;>
    rcases d.periodic.leftSign_spec with hleft | hleft <;>
    rcases d.periodic.rightSign_spec with hright | hright <;>
    simp [hfirst, hleft, hright]

/-- The two eliminations combine to give the Block Floquet determinant
identity.  This is the algebraic content of the boxed formula in Section
9.3, with the ordering sign displayed rather than hidden in `±`. -/
theorem block_floquet_identity (d : FloquetEliminationData p e n w) :
    d.physical.det =
      (d.firstSign * (d.periodic.leftSign * d.periodic.rightSign)) *
        d.interfaceFactor *
          (1 - chronologicalProduct d.transfers).det := by
  have hperiodic := periodicTransfer_det d.transferSystem
    (chronologicalProduct d.transfers) d.periodic
  have hrow :
      d.augmented.det = d.rowFactor.det * d.transferSystem.det := by
    rw [d.rowFactorization, Matrix.det_mul]
  have haug :
      d.augmented.det = d.interfaceFactor *
        ((d.periodic.leftSign * d.periodic.rightSign) *
          (1 - chronologicalProduct d.transfers).det) := by
    calc
      d.augmented.det = d.rowFactor.det * d.transferSystem.det := hrow
      _ = d.interfaceFactor * d.transferSystem.det := by
        rw [FloquetEliminationData.interfaceFactor, d.rowFactor_det]
      _ = d.interfaceFactor *
          ((d.periodic.leftSign * d.periodic.rightSign) *
            (1 - chronologicalProduct d.transfers).det) := by rw [hperiodic]
  have hfirstSquare : d.firstSign * d.firstSign = 1 := by
    rcases d.firstSign_spec with hfirst | hfirst <;> simp [hfirst]
  have hfirst : d.physical.det = d.firstSign * d.augmented.det := by
    calc
      d.physical.det = 1 * d.physical.det := by rw [one_mul]
      _ = (d.firstSign * d.firstSign) * d.physical.det := by
        rw [hfirstSquare]
      _ = d.firstSign * (d.firstSign * d.physical.det) := by ring
      _ = d.firstSign * d.augmented.det := by rw [d.firstElimination]
  rw [hfirst, haug]
  ring

/-- Packet-split form: if the transfer list is presented as the packet arc
followed by the outside arc, its monodromy is `R_out R_partial`. -/
theorem block_floquet_packet_split (d : FloquetEliminationData p e n w)
    (packet outside : List (Matrix n n ℂ))
    (htransfers : d.transfers = packet ++ outside) :
    d.physical.det =
      (d.firstSign * (d.periodic.leftSign * d.periodic.rightSign)) *
        d.interfaceFactor *
          (1 - chronologicalProduct outside * chronologicalProduct packet).det := by
  have hproduct : chronologicalProduct d.transfers =
      chronologicalProduct outside * chronologicalProduct packet := by
    rw [htransfers, chronologicalProduct_append]
  have hdet : (1 - chronologicalProduct d.transfers).det =
      (1 - chronologicalProduct outside * chronologicalProduct packet).det := by
    rw [hproduct]
  calc
    d.physical.det =
        (d.firstSign * (d.periodic.leftSign * d.periodic.rightSign)) *
          d.interfaceFactor *
            (1 - chronologicalProduct d.transfers).det :=
      block_floquet_identity d
    _ = _ := by rw [hdet]

end BlockFloquet

section ClearedCompounds

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- A list entry `(b,T)` represents the cleared exterior operator
`b ⋅ ∧^k T`; in the application `b = det B_j`. -/
def clearedCompound (k : ℕ) (b : ℂ) (T : Matrix n n ℂ) :
    Matrix (powersetCard n k) (powersetCard n k) ℂ :=
  b • compound k T

/-- Chronological product of the cleared exterior operators. -/
def clearedCompoundProduct (k : ℕ) :
    List (ℂ × Matrix n n ℂ) →
      Matrix (powersetCard n k) (powersetCard n k) ℂ
  | [] => compound k 1
  | (b, T) :: xs => clearedCompoundProduct k xs * clearedCompound k b T

/-- The scalar clearing factor associated with a list of steps. -/
def clearingFactor (xs : List (ℂ × Matrix n n ℂ)) : ℂ :=
  (xs.map Prod.fst).prod

/-- Forget the scalar clearing factors and retain the chronological list of
transfer matrices. -/
def transferList (xs : List (ℂ × Matrix n n ℂ)) :
    List (Matrix n n ℂ) :=
  xs.map Prod.snd

/-- Exterior functoriality with all scalar denominators cleared. -/
theorem clearedCompoundProduct_eq (k : ℕ)
    (xs : List (ℂ × Matrix n n ℂ)) :
    clearedCompoundProduct k xs =
      clearingFactor xs • compound k (chronologicalProduct (transferList xs)) := by
  induction xs with
  | nil =>
      simp [clearedCompoundProduct, clearingFactor, transferList]
  | cons x xs ih =>
      rcases x with ⟨b, T⟩
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

/-- The right-hand side of the cleared full-Fock expansion (9.70), bundled
over finsets in the same way as `signedCompoundTrace`. -/
def clearedSignedCompoundTrace (xs : List (ℂ × Matrix n n ℂ)) : ℂ :=
  ∑ s : Finset n, (-1 : ℂ) ^ s.card *
    clearedCompoundProduct s.card xs (ofCard rfl) (ofCard rfl)

/-- Algebraic version of (9.70): multiplying each exterior degree of every
step by its clearing determinant produces the globally cleared Floquet
determinant.  No invertibility assumption is used in this statement. -/
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

section DeterminantClearing

variable {w : Type*} [Fintype w] [DecidableEq w]

/-- Attach to every transfer `T_j` the paper's clearing factor `det B_j`. -/
def determinantClearedSteps
    (xs : List (Matrix w w ℂ × Matrix n n ℂ)) :
    List (ℂ × Matrix n n ℂ) :=
  xs.map fun x ↦ (x.1.det, x.2)

/-- Equation (9.70) with its clearing scalars written explicitly as the
determinants of the right-interface blocks. -/
theorem determinant_cleared_floquet_exterior_identity
    (xs : List (Matrix w w ℂ × Matrix n n ℂ)) :
    clearedSignedCompoundTrace (determinantClearedSteps xs) =
      (xs.map fun x ↦ x.1.det).prod *
        (1 - chronologicalProduct (xs.map Prod.snd)).det := by
  simpa [determinantClearedSteps, clearingFactor, transferList,
    List.map_map, Function.comp_def] using
    (cleared_floquet_exterior_identity (xs := determinantClearedSteps xs))

end DeterminantClearing

end ClearedCompounds

end BernoulliLinearAlgebra
