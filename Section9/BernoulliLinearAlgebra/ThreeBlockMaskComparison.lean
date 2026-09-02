import BernoulliLinearAlgebra.ThreeBlockMaskMinor
import Mathlib.Tactic

/-!
# Concrete three-block mask comparison

This file identifies the complementary block of a valid three-block pivot
with the actual square minor indexed by its unmatched outer rows and columns.
It then packages the resulting finite coefficient comparison.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard MvPolynomial

section ComplementaryMinor

variable {w : Type*} [Fintype w] [DecidableEq w]

local instance threeBlockMaskComparisonVariableDecidableEq :
    DecidableEq (ThreeBlockVariable w) := Classical.decEq _

/-- Forget the central/outer tag.  We only use this on indices which are
proved to be outer; the central branch is a harmless totalization. -/
def threeBlockOuterProjection : ThreeBlockIndex w → ThreeBlockOuter w
  | Sum.inl i => i
  | Sum.inr i => (false, i)

omit [Fintype w] [DecidableEq w] in
@[simp] theorem threeBlockOuterProjection_inl (i : ThreeBlockOuter w) :
    threeBlockOuterProjection (Sum.inl i : ThreeBlockIndex w) = i := rfl

/-- The matching permutation carries selected columns precisely to selected
rows. -/
theorem threeBlockMatchingPermutation_mem_rows_iff
    (a : ValidThreeBlockMatching w) (j : ThreeBlockIndex w) :
    threeBlockMatchingPermutation a j ∈ threeBlockMatchingRows a.1 ↔
      j ∈ threeBlockMatchingCols a.1 := by
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨e, he, hrow⟩
    have hp := threeBlockMatchingPermutation_apply a e he
    have hcol : j = e.1.2 :=
      (threeBlockMatchingPermutation a).injective
        (hrow.symm.trans hp.symm)
    exact Finset.mem_image.mpr ⟨e, he, hcol.symm⟩
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨e, he, hcol⟩
    have hp := threeBlockMatchingPermutation_apply a e he
    exact Finset.mem_image.mpr
      ⟨e, he, by rw [← hcol, hp]⟩

/-- An unselected full column is necessarily an outer column. -/
theorem threeBlockUnselectedColumn_eq_inl
    (a : ValidThreeBlockMatching w) (j : ThreeBlockIndex w)
    (hj : ¬threeBlockIsMatchingColumn a j) :
    j = Sum.inl (threeBlockOuterProjection j) := by
  rcases j with j | j
  · rfl
  · exfalso
    apply hj
    exact a.2.2.2.2 j

/-- The row paired with an unselected column is necessarily an outer row. -/
theorem threeBlockUnselectedPermutationRow_eq_inl
    (a : ValidThreeBlockMatching w) (j : ThreeBlockIndex w)
    (hj : ¬threeBlockIsMatchingColumn a j) :
    threeBlockMatchingPermutation a j =
      Sum.inl (threeBlockOuterProjection
        (threeBlockMatchingPermutation a j)) := by
  have hrow : threeBlockMatchingPermutation a j ∉
      threeBlockMatchingRows a.1 :=
    fun h => hj ((threeBlockMatchingPermutation_mem_rows_iff a j).mp h)
  rcases hperm : threeBlockMatchingPermutation a j with i | i
  · rfl
  · exfalso
    apply hrow
    rw [hperm]
    exact a.2.2.2.1 i

abbrev ThreeBlockUnselectedColumn (a : ValidThreeBlockMatching w) :=
  {j : ThreeBlockIndex w // ¬threeBlockIsMatchingColumn a j}

/-- Read an unselected full column as an unmatched outer column. -/
def threeBlockUnselectedToOuterCol
    (a : ValidThreeBlockMatching w) :
    ThreeBlockUnselectedColumn a →
      ↑(threeBlockUnmatchedOuterCols a.1) :=
  fun j => ⟨threeBlockOuterProjection j.1, by
    have hj : (Sum.inl (threeBlockOuterProjection j.1) :
        ThreeBlockIndex w) ∉ threeBlockMatchingCols a.1 := by
      rw [← threeBlockUnselectedColumn_eq_inl a j.1 j.2]
      exact j.2
    simpa [threeBlockUnmatchedOuterCols] using hj⟩

theorem threeBlockUnselectedToOuterCol_injective
    (a : ValidThreeBlockMatching w) :
    Function.Injective (threeBlockUnselectedToOuterCol a) := by
  intro i j hij
  apply Subtype.ext
  rw [threeBlockUnselectedColumn_eq_inl a i.1 i.2,
    threeBlockUnselectedColumn_eq_inl a j.1 j.2]
  exact congrArg (fun x : ↑(threeBlockUnmatchedOuterCols a.1) =>
    (Sum.inl x.1 : ThreeBlockIndex w)) hij

theorem threeBlockUnselectedToOuterCol_surjective
    (a : ValidThreeBlockMatching w) :
    Function.Surjective (threeBlockUnselectedToOuterCol a) := by
  intro j
  have hj : (Sum.inl j.1 : ThreeBlockIndex w) ∉
      threeBlockMatchingCols a.1 := by
    simpa [threeBlockUnmatchedOuterCols] using j.2
  refine ⟨⟨Sum.inl j.1, hj⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- Canonical equivalence between unselected full columns and unmatched
outer columns. -/
def threeBlockUnselectedOuterColEquiv
    (a : ValidThreeBlockMatching w) :
    ThreeBlockUnselectedColumn a ≃
      ↑(threeBlockUnmatchedOuterCols a.1) :=
  Equiv.ofBijective (threeBlockUnselectedToOuterCol a)
    ⟨threeBlockUnselectedToOuterCol_injective a,
      threeBlockUnselectedToOuterCol_surjective a⟩

/-- Read the permutation row paired with an unselected column as an
unmatched outer row. -/
def threeBlockUnselectedToOuterRow
    (a : ValidThreeBlockMatching w) :
    ThreeBlockUnselectedColumn a →
      ↑(threeBlockUnmatchedOuterRows a.1) :=
  fun j => ⟨threeBlockOuterProjection
      (threeBlockMatchingPermutation a j.1), by
    have hrow : threeBlockMatchingPermutation a j.1 ∉
        threeBlockMatchingRows a.1 :=
      fun h => j.2 ((threeBlockMatchingPermutation_mem_rows_iff a j.1).mp h)
    have hout := threeBlockUnselectedPermutationRow_eq_inl a j.1 j.2
    have : (Sum.inl (threeBlockOuterProjection
        (threeBlockMatchingPermutation a j.1)) : ThreeBlockIndex w) ∉
        threeBlockMatchingRows a.1 := by
      rw [← hout]
      exact hrow
    simpa [threeBlockUnmatchedOuterRows] using this⟩

theorem threeBlockUnselectedToOuterRow_injective
    (a : ValidThreeBlockMatching w) :
    Function.Injective (threeBlockUnselectedToOuterRow a) := by
  intro i j hij
  apply Subtype.ext
  apply (threeBlockMatchingPermutation a).injective
  rw [threeBlockUnselectedPermutationRow_eq_inl a i.1 i.2,
    threeBlockUnselectedPermutationRow_eq_inl a j.1 j.2]
  exact congrArg (fun x : ↑(threeBlockUnmatchedOuterRows a.1) =>
    (Sum.inl x.1 : ThreeBlockIndex w)) hij

theorem threeBlockUnselectedToOuterRow_surjective
    (a : ValidThreeBlockMatching w) :
    Function.Surjective (threeBlockUnselectedToOuterRow a) := by
  intro i
  let j : ThreeBlockIndex w :=
    (threeBlockMatchingPermutation a).symm (Sum.inl i.1)
  have hrow : (Sum.inl i.1 : ThreeBlockIndex w) ∉
      threeBlockMatchingRows a.1 := by
    simpa [threeBlockUnmatchedOuterRows] using i.2
  have hj : ¬threeBlockIsMatchingColumn a j := by
    intro h
    apply hrow
    have := (threeBlockMatchingPermutation_mem_rows_iff a j).mpr h
    simpa [j] using this
  refine ⟨⟨j, hj⟩, ?_⟩
  apply Subtype.ext
  simp [threeBlockUnselectedToOuterRow, j]

/-- Canonical equivalence between unselected full columns and unmatched
outer rows, using the matching permutation. -/
def threeBlockUnselectedOuterRowEquiv
    (a : ValidThreeBlockMatching w) :
    ThreeBlockUnselectedColumn a ≃
      ↑(threeBlockUnmatchedOuterRows a.1) :=
  Equiv.ofBijective (threeBlockUnselectedToOuterRow a)
    ⟨threeBlockUnselectedToOuterRow_injective a,
      threeBlockUnselectedToOuterRow_surjective a⟩

/-- Entrywise identification of the pivot complement with the corresponding
outer submatrix of `Q`. -/
theorem threeBlockPivotComplement_apply
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w)
    (i j : ThreeBlockUnselectedColumn a) :
    threeBlockPivotComplement Q a i j =
      Q (threeBlockUnselectedOuterRowEquiv a i)
        (threeBlockUnselectedOuterColEquiv a j) := by
  have hi := threeBlockUnselectedPermutationRow_eq_inl a i.1 i.2
  have hj := threeBlockUnselectedColumn_eq_inl a j.1 j.2
  have hjcol : (j : ThreeBlockIndex w) ∉
      threeBlockMatchingCols a.1 := j.2
  change (if (j : ThreeBlockIndex w) ∈ threeBlockMatchingCols a.1 then
      if threeBlockMatchingPermutation a i.1 =
          threeBlockMatchingPermutation a j.1 then 1 else 0
    else threeBlockEmb Q (threeBlockMatchingPermutation a i.1) j.1) =
      Q (threeBlockOuterProjection
          (threeBlockMatchingPermutation a i.1))
        (threeBlockOuterProjection j.1)
  rw [if_neg hjcol, hi, hj]
  rfl

section OrderedMinor

variable [LinearOrder w]

local instance threeBlockOuterLinearOrder :
    LinearOrder (ThreeBlockOuter w) :=
  LinearOrder.lift'
    (fun x : ThreeBlockOuter w => (toLex x : Bool ×ₗ w))
    toLex.injective

/-- The column powerset appearing definitionally in the concrete square
minor associated with `a`. -/
def threeBlockMatchingColumnPowerset (a : ValidThreeBlockMatching w) :
    powersetCard (ThreeBlockOuter w)
      (threeBlockUnmatchedOuterCols a.1).card :=
  ofCard rfl

/-- Increasing minor-row enumeration, transported back to the common
unselected-column index of the pivot complement. -/
def threeBlockMinorRowReindex (a : ValidThreeBlockMatching w) :
    Fin (threeBlockUnmatchedOuterCols a.1).card ≃
      ThreeBlockUnselectedColumn a :=
  (orderIsoOfFin (threeBlockMatchingMinorIndex a).2).toEquiv.trans
    (threeBlockUnselectedOuterRowEquiv a).symm

/-- Increasing minor-column enumeration, transported back to the common
unselected-column index of the pivot complement. -/
def threeBlockMinorColReindex (a : ValidThreeBlockMatching w) :
    Fin (threeBlockUnmatchedOuterCols a.1).card ≃
      ThreeBlockUnselectedColumn a :=
  (orderIsoOfFin (threeBlockMatchingColumnPowerset a)).toEquiv.trans
    (threeBlockUnselectedOuterColEquiv a).symm

set_option maxHeartbeats 300000 in
/-- After the two explicit equivalences, the pivot complement is literally
the ordered matrix used by `minor`. -/
theorem threeBlockPivotComplement_reindex_eq_minorMatrix
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w) :
    (threeBlockPivotComplement Q a).submatrix
        (threeBlockMinorRowReindex a) (threeBlockMinorColReindex a) =
      Q.submatrix
        (ofFinEmbEquiv.symm (threeBlockMatchingMinorIndex a).2)
        (ofFinEmbEquiv.symm (threeBlockMatchingColumnPowerset a)) := by
  ext i j
  rw [Matrix.submatrix_apply, threeBlockPivotComplement_apply]
  change
    Q (threeBlockUnselectedOuterRowEquiv a
          (threeBlockMinorRowReindex a i))
        (threeBlockUnselectedOuterColEquiv a
          (threeBlockMinorColReindex a j)) =
      Q (ofFinEmbEquiv.symm (threeBlockMatchingMinorIndex a).2 i)
        (ofFinEmbEquiv.symm (threeBlockMatchingColumnPowerset a) j)
  have hrow :
      threeBlockUnselectedOuterRowEquiv a
          (threeBlockMinorRowReindex a i) =
        orderIsoOfFin (threeBlockMatchingMinorIndex a).2 i := by
    change threeBlockUnselectedOuterRowEquiv a
      ((threeBlockUnselectedOuterRowEquiv a).symm
        (orderIsoOfFin (threeBlockMatchingMinorIndex a).2 i)) = _
    exact Equiv.apply_symm_apply (threeBlockUnselectedOuterRowEquiv a) _
  have hcol :
      threeBlockUnselectedOuterColEquiv a
          (threeBlockMinorColReindex a j) =
        orderIsoOfFin (threeBlockMatchingColumnPowerset a) j := by
    change threeBlockUnselectedOuterColEquiv a
      ((threeBlockUnselectedOuterColEquiv a).symm
        (orderIsoOfFin (threeBlockMatchingColumnPowerset a) j)) = _
    exact Equiv.apply_symm_apply (threeBlockUnselectedOuterColEquiv a) _
  rw [hrow, hcol]
  rfl

/-- Independent row and column equivalences change a complex determinant
only by a unit sign, so its norm is unchanged. -/
theorem norm_det_submatrix_equiv_equiv_complex
    {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (e₁ e₂ : n ≃ m) (A : Matrix m m ℂ) :
    ‖(A.submatrix e₁ e₂).det‖ = ‖A.det‖ := by
  have hdet := Matrix.det_reindex e₁.symm e₂.symm A
  change (A.submatrix e₁ e₂).det =
      (Equiv.Perm.sign (e₂.symm.trans e₁) : ℂ) * A.det at hdet
  have hsign :
      ‖(Equiv.Perm.sign (e₂.symm.trans e₁) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or
      (Equiv.Perm.sign (e₂.symm.trans e₁)) with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  rw [hdet, norm_mul, hsign, one_mul]

/-- The determinant norm of the complementary pivot block is exactly the
norm of the actual square minor selected by `a`. -/
theorem norm_threeBlockPivotComplement_det_eq_squareMinorValue
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w) :
    ‖(threeBlockPivotComplement Q a).det‖ =
      ‖squareMinorValue Q (threeBlockMatchingMinorIndex a)‖ := by
  have hmatrix := threeBlockPivotComplement_reindex_eq_minorMatrix Q a
  have hnorm := norm_det_submatrix_equiv_equiv_complex
    (threeBlockMinorRowReindex a) (threeBlockMinorColReindex a)
    (threeBlockPivotComplement Q a)
  rw [← hnorm]
  rw [congrArg Matrix.det hmatrix]
  rfl

/-- The literal determinant coefficient of every valid squarefree matching
has exactly the norm of its concrete complementary square minor. -/
theorem norm_threeBlockDetCoefficient_zero_eq_squareMinorValue
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w) :
    ‖threeBlockDetCoefficient Q 0 a.1‖ =
      ‖squareMinorValue Q (threeBlockMatchingMinorIndex a)‖ := by
  rw [threeBlockDetCoefficient_zero_eq_pivot_det,
    norm_threeBlockPivot_det_eq_complement_det,
    norm_threeBlockPivotComplement_det_eq_squareMinorValue]

end OrderedMinor

end ComplementaryMinor

end BernoulliLinearAlgebra
