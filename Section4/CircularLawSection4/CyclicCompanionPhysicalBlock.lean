import CircularLawSection4.StateCopyRowScaling
import CircularLawSection4.StateCopyPhysicalBlockFormula

/-!
# Concrete residual block for the cyclic companion state system

After the independent cyclic row/column relabelings, the physical row indexed
by `i : Fin N` comes from a uniquely determined raw last-copy equation.  The
difference/anchor substitution then adds the coefficients of that raw equation
over every copy belonging to the same physical site.  This module records that
entry formula before and after the manuscript's anchor-row scaling by `β`.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

variable {R : Type*} [CommRing R]

/-- The concrete physical matrix obtained from the supplied raw last rows:
for physical column `j`, add all raw coefficients whose relabeled state copies
belong to `j`. -/
def cyclicCompanionPhysicalMatrix
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R)) :
    Matrix (Fin N) (Fin N) R :=
  fun i j =>
    (∑ k : Fin m,
      lastRow (cyclicAnchorEquationRawSite N m offset i)
        (cyclicEarlyStateCopyRawSite N offset j k, k.castSucc)) +
      lastRow (cyclicAnchorEquationRawSite N m offset i)
        (cyclicAnchorStateCopyRawSite N m offset j, Fin.last m)

/-- Before denominator clearing, state-copy elimination leaves exactly the
concrete finite sum `cyclicCompanionPhysicalMatrix`. -/
theorem stateCopyPhysicalBlock_orderedCyclicCompanionState
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R)) :
    stateCopyPhysicalBlock (R := R) N m
        (orderedCyclicCompanionState N m offset lastRow) =
      cyclicCompanionPhysicalMatrix N m offset lastRow := by
  ext i j
  exact cyclicCompanionPhysicalBlock_eq_sum_lastRow_copies
    (R := R) N m offset lastRow i j

/-- After multiplying physical row `i` by `β i`, the residual entry is `β i`
times the sum of the raw last-equation coefficients over every copy of physical
site `j`. -/
theorem scaledCyclicCompanionPhysicalBlock_apply
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (β : Fin N → R)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R))
    (i j : Fin N) :
    stateCopyPhysicalBlock (R := R) N m
        (stateCopyAnchorRowScaling (R := R) N m β *
          orderedCyclicCompanionState N m offset lastRow) i j =
      β i * cyclicCompanionPhysicalMatrix N m offset lastRow i j := by
  rw [stateCopyPhysicalBlock_anchorRowScaling (R := R) N m]
  rw [stateCopyPhysicalBlock_orderedCyclicCompanionState
    (R := R) N m offset lastRow]

/-- Matrix form of the scaled residual-block formula. -/
theorem scaledCyclicCompanionPhysicalBlock_eq
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (β : Fin N → R)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R)) :
    stateCopyPhysicalBlock (R := R) N m
        (stateCopyAnchorRowScaling (R := R) N m β *
          orderedCyclicCompanionState N m offset lastRow) =
      Matrix.diagonal β *
        cyclicCompanionPhysicalMatrix N m offset lastRow := by
  ext i j
  rw [scaledCyclicCompanionPhysicalBlock_apply (R := R) N m]
  simp

end CircularLawSection4
