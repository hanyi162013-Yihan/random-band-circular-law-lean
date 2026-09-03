/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/Section5Formalization/MatrixNormal.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Section5Formalization.Section5Formalization

open scoped BigOperators

namespace Section5Formalization

open GinibreLSV

/-! # Literal deleted-row adjoint model

The manuscript writes the normal space as `ker (P_i A*)`.  The domain below
is indexed by all columns except `i`; its synthesis map sends coefficients to
the corresponding linear combination of columns.  Its adjoint is therefore
the coordinate-deleted adjoint matrix operator.
-/

/-- Indices remaining after deleting `i`. -/
abbrev DeletedIndex (N : Nat) (i : Fin N) := {j : Fin N // j ≠ i}

/-- Synthesis by all columns except column `i`. -/
noncomputable def paperDeletedColumnSynthesis {N : Nat}
    (A : Matrix (Fin N) (Fin N) Complex) (i : Fin N) :
    EuclideanSpace Complex (DeletedIndex N i) →ₗ[Complex]
      EuclideanSpace Complex (Fin N) where
  toFun x := ∑ j, x j • column A j.1
  map_add' x y := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp [Finset.smul_sum, smul_smul]

/-- The concrete deleted-column synthesis has exactly the other-column span as range. -/
theorem paperDeletedColumnSynthesis_range {N : Nat}
    (A : Matrix (Fin N) (Fin N) Complex) (i : Fin N) :
    (paperDeletedColumnSynthesis A i).range = columnSpanExcept A i := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    change (∑ j, x j • column A j.1) ∈ columnSpanExcept A i
    apply Submodule.sum_mem
    intro j _hj
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨j, rfl⟩)
  · rw [columnSpanExcept]
    apply Submodule.span_le.mpr
    rintro y ⟨j, rfl⟩
    refine ⟨EuclideanSpace.single j 1, ?_⟩
    simp [paperDeletedColumnSynthesis]

/-- Literal Lean representative of `P_i A*`. -/
noncomputable def paperDeletedRowAdjoint {N : Nat}
    (A : Matrix (Fin N) (Fin N) Complex) (i : Fin N) :
    EuclideanSpace Complex (Fin N) →ₗ[Complex]
      EuclideanSpace Complex (DeletedIndex N i) :=
  (paperDeletedColumnSynthesis A i).adjoint

/-- Coordinate formula: the `j`-th retained row is inner product with column `j`. -/
theorem paperDeletedRowAdjoint_apply {N : Nat}
    (A : Matrix (Fin N) (Fin N) Complex) (i : Fin N)
    (v : EuclideanSpace Complex (Fin N)) (j : DeletedIndex N i) :
    paperDeletedRowAdjoint A i v j = inner Complex (column A j.1) v := by
  have hadjoint := LinearMap.adjoint_inner_right
    (paperDeletedColumnSynthesis A i) (EuclideanSpace.single j 1) v
  simpa [paperDeletedRowAdjoint, paperDeletedColumnSynthesis,
    EuclideanSpace.inner_single_left] using hadjoint

/-- The exact manuscript identity `ker (P_i A*) = span(columns except i)^perp`. -/
theorem ker_paperDeletedRowAdjoint {N : Nat}
    (A : Matrix (Fin N) (Fin N) Complex) (i : Fin N) :
    (paperDeletedRowAdjoint A i).ker = normalSpaceDeletedColumn A i := by
  symm
  simpa [paperDeletedRowAdjoint] using
    (normalSpaceDeletedColumn_eq_ker_adjoint_of_range_eq
      A i (paperDeletedColumnSynthesis A i) (paperDeletedColumnSynthesis_range A i))

end Section5Formalization

