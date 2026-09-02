import BernoulliLinearAlgebra.ThreeBlockMaskExpansion
import Mathlib.Tactic

/-!
# From valid three-block masks to complementary minors

This file reorganizes the literal Leibniz expansion into a determinant
whose selected columns are standard basis vectors.  Independent row and
column reindexing then leaves the complementary deterministic minor.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard MvPolynomial

section MatchingPermutation

variable {w : Type*} [Fintype w] [DecidableEq w]

local instance threeBlockMaskMinorVariableDecidableEq :
    DecidableEq (ThreeBlockVariable w) := Classical.decEq _

theorem threeBlockValidMatchingCols_injective
    (a : ValidThreeBlockMatching w) :
    Function.Injective (fun e : ↑a.1 => e.1.1.2) := by
  intro e f h
  apply Subtype.ext
  exact a.2.2.1 e.2 f.2 h

theorem threeBlockValidMatchingRows_injective
    (a : ValidThreeBlockMatching w) :
    Function.Injective (fun e : ↑a.1 => e.1.1.1) := by
  intro e f h
  apply Subtype.ext
  exact a.2.1 e.2 f.2 h

/-- Extend the selected column-to-row bijection to a permutation of all
full packet coordinates. -/
def threeBlockMatchingPermutation (a : ValidThreeBlockMatching w) :
    Equiv.Perm (ThreeBlockIndex w) :=
  Classical.choose
    (Equiv.Perm.exists_extending_pair
      (fun e : ↑a.1 => e.1.1.2)
      (fun e : ↑a.1 => e.1.1.1)
      (threeBlockValidMatchingCols_injective a)
      (threeBlockValidMatchingRows_injective a))

theorem threeBlockMatchingPermutation_apply
    (a : ValidThreeBlockMatching w)
    (e : ThreeBlockVariable w) (he : e ∈ a.1) :
    threeBlockMatchingPermutation a e.1.2 = e.1.1 := by
  exact Classical.choose_spec
    (Equiv.Perm.exists_extending_pair
      (fun e : ↑a.1 => e.1.1.2)
      (fun e : ↑a.1 => e.1.1.1)
      (threeBlockValidMatchingCols_injective a)
      (threeBlockValidMatchingRows_injective a)) ⟨e, he⟩

/-- A valid mask lies in a permutation graph exactly when the permutation
extends every selected column-to-row edge. -/
theorem threeBlockValid_subset_permutationGraph_iff
    (a : ValidThreeBlockMatching w)
    (σ : Equiv.Perm (ThreeBlockIndex w)) :
    a.1 ⊆ Finset.univ.image (threeBlockPermutationVariable σ) ↔
      ∀ e ∈ a.1, σ e.1.2 = e.1.1 := by
  constructor
  · intro h e he
    rcases Finset.mem_image.mp (h he) with ⟨j, -, hje⟩
    have hrow := congrArg (fun v : ThreeBlockVariable w => v.1.1) hje
    have hcol := congrArg (fun v : ThreeBlockVariable w => v.1.2) hje
    calc
      σ e.1.2 = σ j := congrArg σ hcol.symm
      _ = e.1.1 := hrow
  · intro h e he
    let j : ThreeBlockFreshColumn σ :=
      ⟨e.1.2, by rw [h e he]; exact e.2⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact Prod.ext (h e he) rfl

theorem threeBlockValid_subset_matchingPermutationGraph
    (a : ValidThreeBlockMatching w) :
    a.1 ⊆ Finset.univ.image
      (threeBlockPermutationVariable (threeBlockMatchingPermutation a)) := by
  exact (threeBlockValid_subset_permutationGraph_iff a _).2
    (threeBlockMatchingPermutation_apply a)

/-- Replace each selected column by the corresponding standard basis
column; keep every unselected column equal to the deterministic embedding. -/
def threeBlockPivotMatrix
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w) :
    Matrix (ThreeBlockIndex w) (ThreeBlockIndex w) ℂ :=
  fun i j =>
    if j ∈ threeBlockMatchingCols a.1 then
      if i = threeBlockMatchingPermutation a j then 1 else 0
    else threeBlockEmb Q i j

/-- Product of deterministic entries along the unselected columns of a
permutation. -/
def threeBlockUnselectedColumnProduct
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w)
    (σ : Equiv.Perm (ThreeBlockIndex w)) : ℂ :=
  ∏ j with j ∉ threeBlockMatchingCols a.1,
    threeBlockEmb Q (σ j) j

theorem threeBlockNonfreshColumn_not_matchingCol
    (a : ValidThreeBlockMatching w)
    (σ : Equiv.Perm (ThreeBlockIndex w))
    (hσ : ∀ e ∈ a.1, σ e.1.2 = e.1.1)
    (j : {j : ThreeBlockIndex w // ¬threeBlockFresh (σ j) j}) :
    (j : ThreeBlockIndex w) ∉ threeBlockMatchingCols a.1 := by
  intro hj
  rcases Finset.mem_image.mp hj with ⟨e, he, hcol⟩
  apply j.2
  rw [← hcol, hσ e he]
  exact e.2

theorem threeBlockPermutationVariable_mem_iff_matchingCol
    (a : ValidThreeBlockMatching w)
    (σ : Equiv.Perm (ThreeBlockIndex w))
    (hσ : ∀ e ∈ a.1, σ e.1.2 = e.1.1)
    (j : ThreeBlockFreshColumn σ) :
    threeBlockPermutationVariable σ j ∈ a.1 ↔
      (j : ThreeBlockIndex w) ∈ threeBlockMatchingCols a.1 := by
  constructor
  · intro hj
    exact Finset.mem_image.mpr
      ⟨threeBlockPermutationVariable σ j, hj, rfl⟩
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨e, he, hcol⟩
    have hvar : threeBlockPermutationVariable σ j = e := by
      apply Subtype.ext
      apply Prod.ext
      · calc
          σ (j : ThreeBlockIndex w) = σ e.1.2 :=
            congrArg σ hcol.symm
          _ = e.1.1 := hσ e he
      · exact hcol.symm
    exact hvar.symm ▸ he

/-- Under an extending permutation, the two complementary products in
the coefficient formula are exactly the product along all unselected
columns. -/
theorem threeBlockPermutationComplementProduct_eq_unselected
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w)
    (σ : Equiv.Perm (ThreeBlockIndex w))
    (hσ : ∀ e ∈ a.1, σ e.1.2 = e.1.1) :
    threeBlockPermutationNonfreshProduct Q σ *
        (∏ j : ThreeBlockFreshColumn σ with
            threeBlockPermutationVariable σ j ∉ a.1,
          threeBlockEmb Q (σ j) j) =
      threeBlockUnselectedColumnProduct Q a σ := by
  let g : ThreeBlockIndex w → ℂ := fun j =>
    if j ∉ threeBlockMatchingCols a.1 then
      threeBlockEmb Q (σ j) j else 1
  have hfresh :
      (∏ j : ThreeBlockFreshColumn σ with
          threeBlockPermutationVariable σ j ∉ a.1,
        threeBlockEmb Q (σ j) j) =
        ∏ j : ThreeBlockFreshColumn σ, g j := by
    calc
      _ = ∏ j : ThreeBlockFreshColumn σ,
          if threeBlockPermutationVariable σ j ∈ a.1 then 1
          else threeBlockEmb Q (σ j) j := by
        rw [← Fintype.prod_ite_mem]
        apply Fintype.prod_congr
        intro j
        by_cases hj : threeBlockPermutationVariable σ j ∈ a.1
        · simp [hj]
        · simp [hj]
      _ = _ := by
        apply Fintype.prod_congr
        intro j
        have hiff :=
          threeBlockPermutationVariable_mem_iff_matchingCol a σ hσ j
        by_cases hj : threeBlockPermutationVariable σ j ∈ a.1
        · have hcol := hiff.mp hj
          simp [g, hj, hcol]
        · have hcol : (j : ThreeBlockIndex w) ∉
              threeBlockMatchingCols a.1 := fun h => hj (hiff.mpr h)
          simp [g, hj, hcol]
  have hnonfresh :
      threeBlockPermutationNonfreshProduct Q σ =
        ∏ j : {j : ThreeBlockIndex w //
          ¬threeBlockFresh (σ j) j}, g j := by
    apply Fintype.prod_congr
    intro j
    have hcol := threeBlockNonfreshColumn_not_matchingCol a σ hσ j
    change threeBlockEmb Q (σ (j : ThreeBlockIndex w))
        (j : ThreeBlockIndex w) = g j
    simp [g, hcol]
  calc
    _ = (∏ j : ThreeBlockFreshColumn σ, g j) *
        ∏ j : {j : ThreeBlockIndex w //
          ¬threeBlockFresh (σ j) j}, g j := by
      rw [hfresh, hnonfresh, mul_comm]
    _ = ∏ j, g j :=
      Fintype.prod_subtype_mul_prod_subtype
        (fun j : ThreeBlockIndex w => threeBlockFresh (σ j) j) g
    _ = _ := by
      rw [threeBlockUnselectedColumnProduct]
      simpa [g] using
        (Fintype.prod_ite_mem
          (Finset.univ.filter (fun j : ThreeBlockIndex w =>
            j ∉ threeBlockMatchingCols a.1))
          (fun j : ThreeBlockIndex w => threeBlockEmb Q (σ j) j))

/-- A permutation extending the valid mask contributes the unselected
deterministic product to the pivot determinant. -/
theorem threeBlockPivotMatrix_prod_of_extends
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w)
    (σ : Equiv.Perm (ThreeBlockIndex w))
    (hσ : ∀ e ∈ a.1, σ e.1.2 = e.1.1) :
    (∏ j, threeBlockPivotMatrix Q a (σ j) j) =
      threeBlockUnselectedColumnProduct Q a σ := by
  rw [threeBlockUnselectedColumnProduct]
  calc
    (∏ j, threeBlockPivotMatrix Q a (σ j) j) =
        ∏ j, if j ∉ threeBlockMatchingCols a.1 then
          threeBlockEmb Q (σ j) j else 1 := by
      apply Fintype.prod_congr
      intro j
      by_cases hj : j ∈ threeBlockMatchingCols a.1
      · rcases Finset.mem_image.mp hj with ⟨e, he, hcol⟩
        have hp := threeBlockMatchingPermutation_apply a e he
        have heq : σ j = threeBlockMatchingPermutation a j := by
          calc
            σ j = σ e.1.2 := congrArg σ hcol.symm
            _ = e.1.1 := hσ e he
            _ = threeBlockMatchingPermutation a e.1.2 := hp.symm
            _ = threeBlockMatchingPermutation a j :=
              congrArg (threeBlockMatchingPermutation a) hcol
        simp [threeBlockPivotMatrix, hj, heq]
      · simp [threeBlockPivotMatrix, hj]
    _ = _ := by
      simpa using
        (Fintype.prod_ite_mem
          (Finset.univ.filter (fun j : ThreeBlockIndex w =>
            j ∉ threeBlockMatchingCols a.1))
          (fun j : ThreeBlockIndex w => threeBlockEmb Q (σ j) j))

theorem threeBlockPivotMatrix_prod_eq_zero_of_not_extends
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w)
    (σ : Equiv.Perm (ThreeBlockIndex w))
    (hσ : ¬∀ e ∈ a.1, σ e.1.2 = e.1.1) :
    (∏ j, threeBlockPivotMatrix Q a (σ j) j) = 0 := by
  push Not at hσ
  rcases hσ with ⟨e, he, hne⟩
  apply Finset.prod_eq_zero (Finset.mem_univ e.1.2)
  have hj : e.1.2 ∈ threeBlockMatchingCols a.1 :=
    Finset.mem_image.mpr ⟨e, he, rfl⟩
  have hp := threeBlockMatchingPermutation_apply a e he
  have hne' : σ e.1.2 ≠ threeBlockMatchingPermutation a e.1.2 := by
    intro h
    exact hne (h.trans hp)
  simp [threeBlockPivotMatrix, hj, hne']

/-- Coefficient of one Leibniz term equals the corresponding term of the
pivot determinant. -/
theorem coeff_threeBlockPermutationProduct_eq_pivotProduct
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w)
    (σ : Equiv.Perm (ThreeBlockIndex w)) :
    coeff (squarefreeExponent a.1)
        (∏ j, threeBlockHPolynomial Q 0 (σ j) j) =
      ∏ j, threeBlockPivotMatrix Q a (σ j) j := by
  rw [coeff_threeBlockPermutationPolynomialProduct]
  by_cases hσ : ∀ e ∈ a.1, σ e.1.2 = e.1.1
  · have hsub := (threeBlockValid_subset_permutationGraph_iff a σ).2 hσ
    rw [if_pos hsub,
      threeBlockPermutationComplementProduct_eq_unselected Q a σ hσ,
      threeBlockPivotMatrix_prod_of_extends Q a σ hσ]
  · have hsub : ¬a.1 ⊆
        Finset.univ.image (threeBlockPermutationVariable σ) :=
      mt (threeBlockValid_subset_permutationGraph_iff a σ).1 hσ
    rw [if_neg hsub, mul_zero,
      threeBlockPivotMatrix_prod_eq_zero_of_not_extends Q a σ hσ]

/-- A genuine squarefree matching coefficient is literally the determinant
of the matrix obtained by replacing the selected columns with their standard
basis columns. -/
theorem threeBlockDetCoefficient_zero_eq_pivot_det
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w) :
    threeBlockDetCoefficient Q 0 a.1 =
      (threeBlockPivotMatrix Q a).det := by
  rw [threeBlockDetCoefficient, threeBlockDetPolynomial,
    Matrix.det_apply, Matrix.det_apply]
  simp only [coeff_sum, coeff_smul]
  apply Finset.sum_congr rfl
  intro σ _
  exact congrArg (fun z : ℂ => Equiv.Perm.sign σ • z)
    (coeff_threeBlockPermutationProduct_eq_pivotProduct Q a σ)

/-- Reindex the pivot rows so that every selected standard basis column is
diagonal. -/
def threeBlockPivotReindexed
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w) :
    Matrix (ThreeBlockIndex w) (ThreeBlockIndex w) ℂ :=
  (threeBlockPivotMatrix Q a).submatrix
    (threeBlockMatchingPermutation a) id

/-- The selected-column predicate, kept opaque so all block determinants
use the same canonical finite subtype instance. -/
def threeBlockIsMatchingColumn (a : ValidThreeBlockMatching w)
    (j : ThreeBlockIndex w) : Prop :=
  j ∈ threeBlockMatchingCols a.1

instance threeBlockIsMatchingColumn_decidable
    (a : ValidThreeBlockMatching w) :
    DecidablePred (threeBlockIsMatchingColumn a) :=
  fun j => inferInstanceAs (Decidable (j ∈ threeBlockMatchingCols a.1))

theorem threeBlockPivotReindexed_selectedBlock_eq_one
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w) :
    Matrix.toSquareBlockProp (threeBlockPivotReindexed Q a)
        (threeBlockIsMatchingColumn a) = 1 := by
  ext i j
  simp only [Matrix.toSquareBlockProp_def, Matrix.of_apply,
    threeBlockPivotReindexed, Matrix.submatrix_apply, Function.id_def,
    threeBlockPivotMatrix, Matrix.one_apply]
  have hj : (j : ThreeBlockIndex w) ∈ threeBlockMatchingCols a.1 := by
    exact j.2
  rw [if_pos hj]
  by_cases hij : i = j
  · subst j
    simp
  · have hp : threeBlockMatchingPermutation a (i : ThreeBlockIndex w) ≠
        threeBlockMatchingPermutation a (j : ThreeBlockIndex w) :=
      (threeBlockMatchingPermutation a).injective.ne
        (fun h => hij (Subtype.ext h))
    simp [hij, hp]

theorem threeBlockPivotReindexed_lowerLeft_zero
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w) :
    ∀ i, i ∉ threeBlockMatchingCols a.1 →
      ∀ j, j ∈ threeBlockMatchingCols a.1 →
        threeBlockPivotReindexed Q a i j = 0 := by
  intro i hi j hj
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  have hp : threeBlockMatchingPermutation a i ≠
      threeBlockMatchingPermutation a j :=
    (threeBlockMatchingPermutation a).injective.ne hij
  simp [threeBlockPivotReindexed, threeBlockPivotMatrix, hj, hp]

/-- The unselected lower-right block after diagonalizing the selected
standard basis columns. -/
def threeBlockPivotComplement
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w) :=
  Matrix.toSquareBlockProp (threeBlockPivotReindexed Q a)
    (fun j => ¬threeBlockIsMatchingColumn a j)

theorem threeBlockPivotReindexed_det_eq_complement_det
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w) :
    (threeBlockPivotReindexed Q a).det =
      (threeBlockPivotComplement Q a).det := by
  rw [Matrix.twoBlockTriangular_det
    (threeBlockPivotReindexed Q a)
    (threeBlockIsMatchingColumn a)
    (by
      intro i hi j hj
      exact threeBlockPivotReindexed_lowerLeft_zero Q a i
        (by simpa [threeBlockIsMatchingColumn] using hi) j
        (by simpa [threeBlockIsMatchingColumn] using hj))]
  have hdet := congrArg Matrix.det
    (threeBlockPivotReindexed_selectedBlock_eq_one Q a)
  have hone :
      (Matrix.toSquareBlockProp (threeBlockPivotReindexed Q a)
        (threeBlockIsMatchingColumn a)).det = 1 := by
    simpa only [Matrix.det_one] using hdet
  rw [hone, one_mul]
  rfl

/-- Independent row reindexing contributes only a sign, hence no change of
complex norm. -/
theorem norm_threeBlockPivot_det_eq_complement_det
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w) :
    ‖(threeBlockPivotMatrix Q a).det‖ =
      ‖(threeBlockPivotComplement Q a).det‖ := by
  have hperm := Matrix.det_permute (threeBlockMatchingPermutation a)
    (threeBlockPivotMatrix Q a)
  have hblock := threeBlockPivotReindexed_det_eq_complement_det Q a
  have hsign :
      ‖(Equiv.Perm.sign (threeBlockMatchingPermutation a) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or
      (Equiv.Perm.sign (threeBlockMatchingPermutation a)) with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  calc
    ‖(threeBlockPivotMatrix Q a).det‖ =
        ‖(Equiv.Perm.sign (threeBlockMatchingPermutation a) : ℂ)‖ *
          ‖(threeBlockPivotMatrix Q a).det‖ := by rw [hsign, one_mul]
    _ = ‖(Equiv.Perm.sign (threeBlockMatchingPermutation a) : ℂ) *
          (threeBlockPivotMatrix Q a).det‖ := by rw [norm_mul]
    _ = ‖(threeBlockPivotReindexed Q a).det‖ := by
      exact congrArg norm hperm.symm
    _ = ‖(threeBlockPivotComplement Q a).det‖ :=
      congrArg norm hblock

end MatchingPermutation

end BernoulliLinearAlgebra
