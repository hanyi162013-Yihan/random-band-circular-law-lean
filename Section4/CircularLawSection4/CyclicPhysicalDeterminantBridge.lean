import CircularLawSection4.CyclicReindexDeterminant
import CircularLawSection4.StateCopyRowScaling

/-!
# Raw cyclic determinant after physical state-copy elimination

This module combines the two determinant factors which occur before the
paper-specific identification of the residual physical block:

* independent cyclic equation/state reindexing contributes the deterministic
  sign `cyclicStateReindexSign`;
* clearing the anchor rows by `β` contributes `∏ i, β i`.

Thus the determinant of the scaled residual physical block is related directly
to the determinant of the raw cyclic companion state matrix, with no hidden
factor left between these two constructions.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

/-- Exact bridge from the determinant of the scaled residual physical block
to the determinant of the raw cyclic companion state matrix.  The only
reindexing factor is the explicitly defined deterministic sign. -/
theorem scaledCyclicCompanionPhysicalBlock_det
    {R : Type*} [CommRing R] (N m : ℕ) [NeZero N]
    (offset : ZMod N)
    (β : Fin N → R)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R)) :
    (stateCopyPhysicalBlock (R := R) N m
      (stateCopyAnchorRowScaling (R := R) N m β *
        orderedCyclicCompanionState N m offset lastRow)).det =
      cyclicStateReindexSign (R := R) N m offset * (∏ i, β i) *
        (cyclicCompanionStateMatrix N m offset lastRow).det := by
  calc
    (stateCopyPhysicalBlock (R := R) N m
      (stateCopyAnchorRowScaling (R := R) N m β *
        orderedCyclicCompanionState N m offset lastRow)).det =
        (∏ i, β i) *
          (orderedCyclicCompanionState N m offset lastRow).det :=
      stateCopyPhysicalBlock_anchorRowScaling_det (R := R) N m β
        (orderedCyclicCompanionState N m offset lastRow)
        (orderedCyclicCompanionState_identification N m offset lastRow)
    _ = (∏ i, β i) *
        (cyclicStateReindexSign (R := R) N m offset *
          (cyclicCompanionStateMatrix N m offset lastRow).det) := by
      rw [orderedCyclicCompanionState_det]
    _ = cyclicStateReindexSign (R := R) N m offset * (∏ i, β i) *
        (cyclicCompanionStateMatrix N m offset lastRow).det := by
      ac_rfl

/-- Sign-only form of `scaledCyclicCompanionPhysicalBlock_det`: there is an
explicit `σ = ±1` relating the scaled residual determinant to the raw cyclic
state determinant and all denominator-clearing factors. -/
theorem exists_sign_scaledCyclicCompanionPhysicalBlock_det
    {R : Type*} [CommRing R] (N m : ℕ) [NeZero N]
    (offset : ZMod N)
    (β : Fin N → R)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R)) :
    ∃ σ : R,
      (σ = 1 ∨ σ = -1) ∧
        (stateCopyPhysicalBlock (R := R) N m
          (stateCopyAnchorRowScaling (R := R) N m β *
            orderedCyclicCompanionState N m offset lastRow)).det =
          σ * (∏ i, β i) *
            (cyclicCompanionStateMatrix N m offset lastRow).det := by
  refine ⟨cyclicStateReindexSign (R := R) N m offset,
    cyclicStateReindexSign_spec (R := R) N m offset, ?_⟩
  exact scaledCyclicCompanionPhysicalBlock_det (R := R) N m offset β lastRow

end CircularLawSection4
