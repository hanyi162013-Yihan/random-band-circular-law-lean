import CircularLawSection4.StateCopyElimination

/-!
# Anchor-row scaling for the periodic state-copy elimination

The manuscript clears the denominator in each physical (last-copy) equation
by multiplying that row by a scalar `β i`.  After the independent cyclic
row/column relabelings of `StateCopyElimination.lean`, these are precisely the
`Sum.inr i` anchor rows.  This module records that row scaling as an explicit
block-diagonal matrix, computes its determinant, and feeds the scaled system
into `PhysicalEliminationCertificate`.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

section AnchorRowScaling

variable {R : Type*} [CommRing R]
variable (N m : ℕ)

/-- Block-diagonal row scaling which fixes all state-identification rows and
multiplies the physical anchor row `i` by `β i`. -/
def stateCopyAnchorRowScaling (β : Fin N → R) :
    Matrix (StateCopyIndex N m) (StateCopyIndex N m) R :=
  Matrix.fromBlocks 1 0 0 (Matrix.diagonal β)

/-- Equivalent diagonal description of the same block scaling. -/
theorem stateCopyAnchorRowScaling_eq_diagonal (β : Fin N → R) :
    stateCopyAnchorRowScaling (R := R) N m β =
      Matrix.diagonal (Sum.elim (fun _ : StateDifferenceIndex N m => 1) β) := by
  rw [stateCopyAnchorRowScaling, ← Matrix.fromBlocks_diagonal]
  simp

/-- The determinant of anchor-row scaling is exactly the product of the
physical denominator-clearing factors. -/
@[simp] theorem stateCopyAnchorRowScaling_det (β : Fin N → R) :
    (stateCopyAnchorRowScaling (R := R) N m β).det = ∏ i, β i := by
  rw [stateCopyAnchorRowScaling, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- Scaling only the anchor rows leaves every identification row unchanged. -/
theorem stateCopyAnchorRowScaling_mul_apply_inl
    (β : Fin N → R)
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R)
    (r : StateDifferenceIndex N m) (c : StateCopyIndex N m) :
    (stateCopyAnchorRowScaling (R := R) N m β * state) (Sum.inl r) c =
      state (Sum.inl r) c := by
  rw [stateCopyAnchorRowScaling_eq_diagonal (R := R) N m]
  change
    Matrix.diagonal (Sum.elim (fun _ : StateDifferenceIndex N m => 1) β)
        (Sum.inl r) ⬝ᵥ (fun a => state a c) = state (Sum.inl r) c
  simp

/-- On an anchor row, the block scaling acts by the prescribed scalar. -/
theorem stateCopyAnchorRowScaling_mul_apply_inr
    (β : Fin N → R)
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R)
    (i : Fin N) (c : StateCopyIndex N m) :
    (stateCopyAnchorRowScaling (R := R) N m β * state) (Sum.inr i) c =
      β i * state (Sum.inr i) c := by
  rw [stateCopyAnchorRowScaling_eq_diagonal (R := R) N m]
  change
    Matrix.diagonal (Sum.elim (fun _ : StateDifferenceIndex N m => 1) β)
        (Sum.inr i) ⬝ᵥ (fun a => state a c) = β i * state (Sum.inr i) c
  simp

/-- Hence an already ordered state system still has its strict
state-identification block after anchor-row scaling. -/
theorem stateCopyAnchorRowScaling_preserves_identification
    (β : Fin N → R)
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R)
    (hident : ∀ r c,
      state (Sum.inl r) c = stateIdentificationMatrix (R := R) N m r c) :
    ∀ r c,
      (stateCopyAnchorRowScaling (R := R) N m β * state) (Sum.inl r) c =
        stateIdentificationMatrix (R := R) N m r c := by
  intro r c
  rw [stateCopyAnchorRowScaling_mul_apply_inl (R := R) N m]
  exact hident r c

/-- The surviving physical block is row-scaled in the same way: its row `i`
is multiplied by `β i`. -/
theorem stateCopyPhysicalBlock_anchorRowScaling
    (β : Fin N → R)
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R)
    (i j : Fin N) :
    stateCopyPhysicalBlock (R := R) N m
        (stateCopyAnchorRowScaling (R := R) N m β * state) i j =
      β i * stateCopyPhysicalBlock (R := R) N m state i j := by
  change
    ((stateCopyAnchorRowScaling (R := R) N m β * state) *
        differenceAnchorRight (R := R) N m) (Sum.inr i) (Sum.inr j) =
      β i * (state * differenceAnchorRight (R := R) N m)
        (Sum.inr i) (Sum.inr j)
  rw [Matrix.mul_assoc]
  exact stateCopyAnchorRowScaling_mul_apply_inr (R := R) N m β
    (state * differenceAnchorRight (R := R) N m) i (Sum.inr j)

/-- Physical-elimination certificate including all anchor-row clearing
factors.  Its physical block is computed from the scaled state system, while
the certificate's `state` field remains the original unscaled matrix. -/
def scaledOrderedStateCopyPhysicalCertificate
    (β : Fin N → R)
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R)
    (hident : ∀ r c,
      state (Sum.inl r) c = stateIdentificationMatrix (R := R) N m r c) :
    PhysicalEliminationCertificate (a := StateDifferenceIndex N m)
      (stateCopyPhysicalBlock (R := R) N m
        (stateCopyAnchorRowScaling (R := R) N m β * state))
      state (∏ i, β i) where
  order := Equiv.refl _
  rowScaling := stateCopyAnchorRowScaling (R := R) N m β
  left := stateCopyPhysicalLeft (R := R) N m
    (stateCopyAnchorRowScaling (R := R) N m β * state)
  right := differenceAnchorRight (R := R) N m
  leftSign := 1
  rightSign := 1
  leftSign_spec := Or.inl rfl
  rightSign_spec := Or.inl rfl
  det_rowScaling := stateCopyAnchorRowScaling_det (R := R) N m β
  det_left := stateCopyPhysicalLeft_det (R := R) N m _
  det_right := differenceAnchorRight_det (R := R) N m
  reduction := by
    simpa using stateCopyPhysical_reduction (R := R) N m
      (stateCopyAnchorRowScaling (R := R) N m β * state)
      (stateCopyAnchorRowScaling_preserves_identification
        (R := R) N m β state hident)

/-- Determinant relation obtained from the scaled certificate, with no
remaining sign because both elimination matrices have determinant one. -/
theorem stateCopyPhysicalBlock_anchorRowScaling_det
    (β : Fin N → R)
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R)
    (hident : ∀ r c,
      state (Sum.inl r) c = stateIdentificationMatrix (R := R) N m r c) :
    (stateCopyPhysicalBlock (R := R) N m
      (stateCopyAnchorRowScaling (R := R) N m β * state)).det =
        (∏ i, β i) * state.det := by
  simpa [PhysicalEliminationCertificate.sign,
    scaledOrderedStateCopyPhysicalCertificate] using
    physicalElimination_det
      (stateCopyPhysicalBlock (R := R) N m
        (stateCopyAnchorRowScaling (R := R) N m β * state))
      state (∏ i, β i)
      (scaledOrderedStateCopyPhysicalCertificate (R := R) N m β state hident)

end AnchorRowScaling

section ConcreteCyclicCompanionScaling

/-- Direct specialization of anchor-row scaling to the independently
reindexed cyclic companion state system. -/
def scaledCyclicCompanionPhysicalCertificate
    {R : Type*} [CommRing R] (N m : ℕ) [NeZero N]
    (offset : ZMod N)
    (β : Fin N → R)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R)) :
    PhysicalEliminationCertificate (a := StateDifferenceIndex N m)
      (stateCopyPhysicalBlock (R := R) N m
        (stateCopyAnchorRowScaling (R := R) N m β *
          orderedCyclicCompanionState N m offset lastRow))
      (orderedCyclicCompanionState N m offset lastRow) (∏ i, β i) :=
  scaledOrderedStateCopyPhysicalCertificate (R := R) N m β
    (orderedCyclicCompanionState N m offset lastRow)
    (orderedCyclicCompanionState_identification N m offset lastRow)

end ConcreteCyclicCompanionScaling

end CircularLawSection4
