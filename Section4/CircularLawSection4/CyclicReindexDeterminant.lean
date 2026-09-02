import CircularLawSection4.StateCopyElimination

/-!
# Determinant sign of the independent cyclic row/column relabelings

The manuscript reorders equation rows and state-coordinate columns
independently.  Their only determinant contribution is the sign of the
resulting finite permutation.
-/

open scoped Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

/-- Deterministic sign contributed by the independent equation-row and
state-column cyclic relabelings. -/
def cyclicStateReindexSign
    {R : Type*} [CommRing R] (N m : ℕ) [NeZero N]
    (offset : ZMod N) : R :=
  (Equiv.Perm.sign
    ((cyclicStateCopyRelabel N m offset).trans
      (cyclicStateEquationRelabel N m offset).symm) : R)

/-- The cyclic reindexing factor is a sign. -/
theorem cyclicStateReindexSign_spec
    {R : Type*} [CommRing R] (N m : ℕ) [NeZero N]
    (offset : ZMod N) :
    cyclicStateReindexSign (R := R) N m offset = 1 ∨
      cyclicStateReindexSign (R := R) N m offset = -1 := by
  rcases Int.units_eq_one_or
      (Equiv.Perm.sign
        ((cyclicStateCopyRelabel N m offset).trans
          (cyclicStateEquationRelabel N m offset).symm)) with h | h
  · left
    simp [cyclicStateReindexSign, h]
  · right
    simp [cyclicStateReindexSign, h]

/-- Exact determinant comparison between the raw cyclic state matrix and the
matrix with independently ordered equation rows and state-copy columns. -/
theorem orderedCyclicCompanionState_det
    {R : Type*} [CommRing R] (N m : ℕ) [NeZero N]
    (offset : ZMod N)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R)) :
    (orderedCyclicCompanionState N m offset lastRow).det =
      cyclicStateReindexSign (R := R) N m offset *
        (cyclicCompanionStateMatrix N m offset lastRow).det := by
  exact Matrix.det_reindex
    (cyclicStateEquationRelabel N m offset)
    (cyclicStateCopyRelabel N m offset)
    (cyclicCompanionStateMatrix N m offset lastRow)

end CircularLawSection4
