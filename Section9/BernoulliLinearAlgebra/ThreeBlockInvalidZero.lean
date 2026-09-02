import BernoulliLinearAlgebra.ThreeBlockMaskComparison
import Mathlib.Tactic

/-!
# Invalid squarefree three-block masks have zero coefficient

A nonzero Leibniz summand forces the squarefree mask to lie in one
permutation graph.  This gives distinct rows and columns.  Moreover, if a
central row or column were omitted, its complementary deterministic factor
would be zero because `Emb_O(Q)` is supported only on outer coordinates.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set MvPolynomial

section InvalidMasks

variable {w : Type*} [Fintype w] [DecidableEq w]

local instance threeBlockInvalidZeroVariableDecidableEq :
    DecidableEq (ThreeBlockVariable w) := Classical.decEq _

/-- One signed term in the concrete matching expansion. -/
def threeBlockMatchingSummand
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (S : Finset (ThreeBlockVariable w))
    (σ : Equiv.Perm (ThreeBlockIndex w)) : ℂ :=
  Equiv.Perm.sign σ •
    (threeBlockPermutationNonfreshProduct Q σ *
      if S ⊆ Finset.univ.image (threeBlockPermutationVariable σ) then
        threeBlockPermutationFreshComplementProduct Q S σ
      else 0)

theorem threeBlockMatchingExpansion_eq_sum_summand
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (S : Finset (ThreeBlockVariable w)) :
    threeBlockMatchingExpansion Q S =
      ∑ σ, threeBlockMatchingSummand Q S σ := by
  rfl

/-- A nonzero matching summand forces distinct selected rows. -/
theorem threeBlockMatchingSummand_nonzero_row_injOn
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (S : Finset (ThreeBlockVariable w))
    (σ : Equiv.Perm (ThreeBlockIndex w))
    (hterm : threeBlockMatchingSummand Q S σ ≠ 0) :
    Set.InjOn (fun e : ThreeBlockVariable w => e.1.1) S := by
  have hsub : S ⊆
      Finset.univ.image (threeBlockPermutationVariable σ) := by
    by_contra h
    apply hterm
    simp [threeBlockMatchingSummand, h]
  intro e he f hf hrow
  rcases Finset.mem_image.mp (hsub he) with ⟨j, -, hje⟩
  rcases Finset.mem_image.mp (hsub hf) with ⟨k, -, hkf⟩
  have hσ : σ (j : ThreeBlockIndex w) = σ (k : ThreeBlockIndex w) := by
    calc
      σ (j : ThreeBlockIndex w) = e.1.1 :=
        congrArg (fun v : ThreeBlockVariable w => v.1.1) hje
      _ = f.1.1 := hrow
      _ = σ (k : ThreeBlockIndex w) :=
        (congrArg (fun v : ThreeBlockVariable w => v.1.1) hkf).symm
  have hjk : j = k := by
    apply Subtype.ext
    exact σ.injective hσ
  calc
    e = threeBlockPermutationVariable σ j := hje.symm
    _ = threeBlockPermutationVariable σ k := congrArg _ hjk
    _ = f := hkf

/-- A nonzero matching summand forces distinct selected columns. -/
theorem threeBlockMatchingSummand_nonzero_col_injOn
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (S : Finset (ThreeBlockVariable w))
    (σ : Equiv.Perm (ThreeBlockIndex w))
    (hterm : threeBlockMatchingSummand Q S σ ≠ 0) :
    Set.InjOn (fun e : ThreeBlockVariable w => e.1.2) S := by
  have hsub : S ⊆
      Finset.univ.image (threeBlockPermutationVariable σ) := by
    by_contra h
    apply hterm
    simp [threeBlockMatchingSummand, h]
  intro e he f hf hcol
  rcases Finset.mem_image.mp (hsub he) with ⟨j, -, hje⟩
  rcases Finset.mem_image.mp (hsub hf) with ⟨k, -, hkf⟩
  have hjk : j = k := by
    apply Subtype.ext
    calc
      (j : ThreeBlockIndex w) = e.1.2 :=
        congrArg (fun v : ThreeBlockVariable w => v.1.2) hje
      _ = f.1.2 := hcol
      _ = (k : ThreeBlockIndex w) :=
        (congrArg (fun v : ThreeBlockVariable w => v.1.2) hkf).symm
  calc
    e = threeBlockPermutationVariable σ j := hje.symm
    _ = threeBlockPermutationVariable σ k := congrArg _ hjk
    _ = f := hkf

/-- A nonzero summand must select every central column. -/
theorem threeBlockMatchingSummand_nonzero_center_cols
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (S : Finset (ThreeBlockVariable w))
    (σ : Equiv.Perm (ThreeBlockIndex w))
    (hterm : threeBlockMatchingSummand Q S σ ≠ 0) :
    ∀ k : w, Sum.inr k ∈ threeBlockMatchingCols S := by
  have hsub : S ⊆
      Finset.univ.image (threeBlockPermutationVariable σ) := by
    by_contra h
    apply hterm
    simp [threeBlockMatchingSummand, h]
  have hcomp : threeBlockPermutationFreshComplementProduct Q S σ ≠ 0 := by
    intro hzero
    apply hterm
    simp [threeBlockMatchingSummand, hsub, hzero]
  intro k
  let j : ThreeBlockFreshColumn σ :=
    ⟨Sum.inr k, threeBlockFresh_center_col _ k⟩
  have hv : threeBlockPermutationVariable σ j ∈ S := by
    by_contra hv
    apply hcomp
    rw [threeBlockPermutationFreshComplementProduct]
    apply Finset.prod_eq_zero (Finset.mem_filter.mpr
      ⟨Finset.mem_univ j, hv⟩)
    simp [j]
  exact Finset.mem_image.mpr
    ⟨threeBlockPermutationVariable σ j, hv, rfl⟩

/-- A nonzero summand must select every central row. -/
theorem threeBlockMatchingSummand_nonzero_center_rows
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (S : Finset (ThreeBlockVariable w))
    (σ : Equiv.Perm (ThreeBlockIndex w))
    (hterm : threeBlockMatchingSummand Q S σ ≠ 0) :
    ∀ k : w, Sum.inr k ∈ threeBlockMatchingRows S := by
  have hsub : S ⊆
      Finset.univ.image (threeBlockPermutationVariable σ) := by
    by_contra h
    apply hterm
    simp [threeBlockMatchingSummand, h]
  have hcomp : threeBlockPermutationFreshComplementProduct Q S σ ≠ 0 := by
    intro hzero
    apply hterm
    simp [threeBlockMatchingSummand, hsub, hzero]
  intro k
  let j : ThreeBlockFreshColumn σ :=
    ⟨σ.symm (Sum.inr k), by simp⟩
  have hv : threeBlockPermutationVariable σ j ∈ S := by
    by_contra hv
    apply hcomp
    rw [threeBlockPermutationFreshComplementProduct]
    apply Finset.prod_eq_zero (Finset.mem_filter.mpr
      ⟨Finset.mem_univ j, hv⟩)
    simp [j]
  apply Finset.mem_image.mpr
  refine ⟨threeBlockPermutationVariable σ j, hv, ?_⟩
  simp [threeBlockPermutationVariable, j]

/-- Any nonzero concrete Leibniz summand forces precisely the validity
conditions used by `ValidThreeBlockMatching`. -/
theorem threeBlockMatchingSummand_nonzero_isValid
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (S : Finset (ThreeBlockVariable w))
    (σ : Equiv.Perm (ThreeBlockIndex w))
    (hterm : threeBlockMatchingSummand Q S σ ≠ 0) :
    IsValidThreeBlockMatching S :=
  ⟨threeBlockMatchingSummand_nonzero_row_injOn Q S σ hterm,
    threeBlockMatchingSummand_nonzero_col_injOn Q S σ hterm,
    threeBlockMatchingSummand_nonzero_center_rows Q S σ hterm,
    threeBlockMatchingSummand_nonzero_center_cols Q S σ hterm⟩

/-- Every invalid squarefree monomial has zero actual determinant
coefficient at zero spectral shift. -/
theorem threeBlockDetCoefficient_zero_of_not_valid
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (S : Finset (ThreeBlockVariable w))
    (hS : ¬IsValidThreeBlockMatching S) :
    threeBlockDetCoefficient Q 0 S = 0 := by
  rw [threeBlockDetCoefficient_zero_eq_matchingExpansion,
    threeBlockMatchingExpansion_eq_sum_summand]
  apply Finset.sum_eq_zero
  intro σ _
  by_contra hterm
  exact hS (threeBlockMatchingSummand_nonzero_isValid Q S σ hterm)

end InvalidMasks

end BernoulliLinearAlgebra
