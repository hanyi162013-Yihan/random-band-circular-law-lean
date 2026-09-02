import CircularLawSection4.StateCopyElimination

/-!
# Entry formula for the residual physical block

The inverse difference/anchor transform sends an anchor basis vector to the
vector which is one on every state copy of the same physical site.  Therefore
an entry of the residual physical block is the sum of the corresponding last
row over all copies of that site.  This is the matrix form of the substitution
`s_{j,0} = \cdots = s_{j,m}` used in the periodic determinant proof.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

section AbstractState

variable {R : Type*} [CommRing R]
variable (N m : ℕ)

/-- A residual physical entry is the finite dot product of the corresponding
last state row with the lift of the physical anchor. -/
theorem stateCopyPhysicalBlock_eq_dotProduct
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R)
    (i j : Fin N) :
    stateCopyPhysicalBlock (R := R) N m state i j =
      dotProduct (state (Sum.inr i))
        (stateCopyAnchorLift (R := R) N m j) := by
  rw [stateCopyPhysicalBlock, Matrix.mul_apply]
  rw [← differenceAnchorRight_anchorColumn (R := R) N m j]
  rfl

/-- Explicitly, the residual entry is the sum of the coefficients on the
first `m` copies of the physical site, plus the coefficient on its anchor
copy. -/
theorem stateCopyPhysicalBlock_eq_sum_copies
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R)
    (i j : Fin N) :
    stateCopyPhysicalBlock (R := R) N m state i j =
      (∑ k : Fin m, state (Sum.inr i) (Sum.inl (toLex (j, k)))) +
        state (Sum.inr i) (Sum.inr j) := by
  rw [stateCopyPhysicalBlock_eq_dotProduct (R := R) N m]
  simp only [dotProduct, Fintype.sum_sum_type, stateCopyAnchorLift_inl,
    stateCopyAnchorLift_inr, mul_ite, mul_one, mul_zero]
  rw [← (toLex : (Fin N × Fin m) ≃ StateDifferenceIndex N m).sum_comp]
  rw [Fintype.sum_prod_type]
  have hfst (x : Fin N) (y : Fin m) : (toLex (x, y)).1 = x := rfl
  simp_rw [hfst]
  simp

end AbstractState

section CyclicCompanion

/-- Raw cyclic site of the last equation which becomes physical row `i`
after the independent equation-row relabeling. -/
def cyclicAnchorEquationRawSite (N m : ℕ) [NeZero N]
    (offset : ZMod N) (i : Fin N) : ZMod N :=
  ZMod.finEquiv N i - offset - 1 - (m : ZMod N)

/-- Raw cyclic site of the early copy which becomes copy `(j,k)` after the
state-column relabeling. -/
def cyclicEarlyStateCopyRawSite (N : ℕ) [NeZero N]
    (offset : ZMod N) (j : Fin N) (k : Fin m) : ZMod N :=
  ZMod.finEquiv N j - offset - (k.val : ZMod N)

/-- Raw cyclic site of the last copy which becomes physical anchor `j`. -/
def cyclicAnchorStateCopyRawSite (N m : ℕ) [NeZero N]
    (offset : ZMod N) (j : Fin N) : ZMod N :=
  ZMod.finEquiv N j - offset - (m : ZMod N)

@[simp] theorem cyclicStateEquationRelabel_symm_inr
    (N m : ℕ) [NeZero N] (offset : ZMod N) (i : Fin N) :
    (cyclicStateEquationRelabel N m offset).symm (Sum.inr i) =
      (cyclicAnchorEquationRawSite N m offset i, Fin.last m) := by
  apply (cyclicStateEquationRelabel N m offset).injective
  rw [(cyclicStateEquationRelabel N m offset).apply_symm_apply]
  rw [cyclicStateEquationRelabel_last]
  rw [Sum.inr.injEq]
  apply (ZMod.finEquiv N).injective
  simp [cyclicAnchorEquationRawSite]
  abel

@[simp] theorem cyclicStateCopyRelabel_symm_inl
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (j : Fin N) (k : Fin m) :
    (cyclicStateCopyRelabel N m offset).symm
        (Sum.inl (toLex (j, k))) =
      (cyclicEarlyStateCopyRawSite N offset j k, k.castSucc) := by
  apply (cyclicStateCopyRelabel N m offset).injective
  rw [(cyclicStateCopyRelabel N m offset).apply_symm_apply]
  rw [cyclicStateCopyRelabel_castSucc]
  rw [Sum.inl.injEq, toLex_inj, Prod.ext_iff]
  constructor
  · apply (ZMod.finEquiv N).injective
    simp [cyclicEarlyStateCopyRawSite]
    abel
  · rfl

@[simp] theorem cyclicStateCopyRelabel_symm_inr
    (N m : ℕ) [NeZero N] (offset : ZMod N) (j : Fin N) :
    (cyclicStateCopyRelabel N m offset).symm (Sum.inr j) =
      (cyclicAnchorStateCopyRawSite N m offset j, Fin.last m) := by
  apply (cyclicStateCopyRelabel N m offset).injective
  rw [(cyclicStateCopyRelabel N m offset).apply_symm_apply]
  rw [cyclicStateCopyRelabel_last]
  rw [Sum.inr.injEq]
  apply (ZMod.finEquiv N).injective
  simp [cyclicAnchorStateCopyRawSite]
  abel

/-- An anchor row of the ordered cyclic companion matrix is exactly the
supplied raw last row, evaluated at the inverse-relabelled state copy. -/
theorem orderedCyclicCompanionState_anchorRow_apply
    {R : Type*} [CommRing R] (N m : ℕ) [NeZero N]
    (offset : ZMod N)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R))
    (i : Fin N) (c : StateCopyIndex N m) :
    orderedCyclicCompanionState N m offset lastRow (Sum.inr i) c =
      lastRow (cyclicAnchorEquationRawSite N m offset i)
        ((cyclicStateCopyRelabel N m offset).symm c) := by
  simp [orderedCyclicCompanionState, Matrix.reindex_apply,
    cyclicCompanionStateMatrix]

/-- Closed entry formula for the physical block of the cyclic companion
system: sum the supplied last-row coefficients over all `m + 1` state copies
of the same physical site. -/
theorem cyclicCompanionPhysicalBlock_eq_sum_lastRow_copies
    {R : Type*} [CommRing R] (N m : ℕ) [NeZero N]
    (offset : ZMod N)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R))
    (i j : Fin N) :
    stateCopyPhysicalBlock (R := R) N m
        (orderedCyclicCompanionState N m offset lastRow) i j =
      (∑ k : Fin m,
        lastRow (cyclicAnchorEquationRawSite N m offset i)
          (cyclicEarlyStateCopyRawSite N offset j k, k.castSucc)) +
        lastRow (cyclicAnchorEquationRawSite N m offset i)
          (cyclicAnchorStateCopyRawSite N m offset j, Fin.last m) := by
  rw [stateCopyPhysicalBlock_eq_sum_copies (R := R) N m]
  simp [orderedCyclicCompanionState_anchorRow_apply]

end CyclicCompanion

end CircularLawSection4
