import BernoulliSection9.MatrixStrongMeasurable
import BernoulliSection9.TerminalConcreteResidual
import Mathlib.Tactic

/-!
# Conditional measurability of the literal terminal Cook deformations

The two Cook squares are selected from the global seven-block iid family.
This file proves, entry by entry, that the corresponding literal CUR/Schur
deformations only use coordinates in the complement of the square currently
kept fresh.  The result supplies the measurability premises of the two
conditional Cook applications without exposing a certificate to callers.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

open BernoulliLinearAlgebra
open MeasureTheory

/-! ## Coordinate exclusion -/

/-- A global fresh coordinate whose balanced row is not in the first
residual block cannot be one of the first Cook-square coordinates. -/
theorem terminalFreshCoordinate_not_mem_first_of_row
    {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i j : Fin r ⊕ TerminalBalancedResidualIndex rowEquiv colEquiv)
    (hfresh : threeBlockFresh
      (terminalBalancedRowEquiv rowEquiv colEquiv i)
      (terminalBalancedColEquiv rowEquiv colEquiv j))
    (hi : ∀ p : Fin (terminalBalancedSize rowEquiv colEquiv),
      i ≠ Sum.inr (Sum.inl p)) :
    (⟨(terminalBalancedRowEquiv rowEquiv colEquiv i,
        terminalBalancedColEquiv rowEquiv colEquiv j), hfresh⟩ :
      ThreeBlockVariable (Fin W)) ∉
      selectedCoordinateSet
        (terminalFirstBalancedEntryEmbedding rowEquiv colEquiv) := by
  intro hmem
  simp only [selectedCoordinateSet, Finset.mem_map, Finset.mem_univ,
    true_and] at hmem
  rcases hmem with ⟨p, hp⟩
  have hrow := congrArg
    (fun x : ThreeBlockVariable (Fin W) => x.1.1) hp
  simp only [terminalFirstBalancedEntryEmbedding_val] at hrow
  exact hi p.1
    ((terminalBalancedRowEquiv rowEquiv colEquiv).injective hrow.symm)

/-- Column version of `terminalFreshCoordinate_not_mem_first_of_row`. -/
theorem terminalFreshCoordinate_not_mem_first_of_col
    {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i j : Fin r ⊕ TerminalBalancedResidualIndex rowEquiv colEquiv)
    (hfresh : threeBlockFresh
      (terminalBalancedRowEquiv rowEquiv colEquiv i)
      (terminalBalancedColEquiv rowEquiv colEquiv j))
    (hj : ∀ p : Fin (terminalBalancedSize rowEquiv colEquiv),
      j ≠ Sum.inr (Sum.inl p)) :
    (⟨(terminalBalancedRowEquiv rowEquiv colEquiv i,
        terminalBalancedColEquiv rowEquiv colEquiv j), hfresh⟩ :
      ThreeBlockVariable (Fin W)) ∉
      selectedCoordinateSet
        (terminalFirstBalancedEntryEmbedding rowEquiv colEquiv) := by
  intro hmem
  simp only [selectedCoordinateSet, Finset.mem_map, Finset.mem_univ,
    true_and] at hmem
  rcases hmem with ⟨p, hp⟩
  have hcol := congrArg
    (fun x : ThreeBlockVariable (Fin W) => x.1.2) hp
  simp only [terminalFirstBalancedEntryEmbedding_val] at hcol
  exact hj p.2
    ((terminalBalancedColEquiv rowEquiv colEquiv).injective hcol.symm)

/-- A global fresh coordinate whose balanced row is not in the second
residual block cannot be one of the second Cook-square coordinates. -/
theorem terminalFreshCoordinate_not_mem_second_of_row
    {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i j : Fin r ⊕ TerminalBalancedResidualIndex rowEquiv colEquiv)
    (hfresh : threeBlockFresh
      (terminalBalancedRowEquiv rowEquiv colEquiv i)
      (terminalBalancedColEquiv rowEquiv colEquiv j))
    (hi : ∀ p : Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv),
      i ≠ Sum.inr (Sum.inr p)) :
    (⟨(terminalBalancedRowEquiv rowEquiv colEquiv i,
        terminalBalancedColEquiv rowEquiv colEquiv j), hfresh⟩ :
      ThreeBlockVariable (Fin W)) ∉
      selectedCoordinateSet
        (terminalSecondBalancedEntryEmbedding rowEquiv colEquiv) := by
  intro hmem
  simp only [selectedCoordinateSet, Finset.mem_map, Finset.mem_univ,
    true_and] at hmem
  rcases hmem with ⟨p, hp⟩
  have hrow := congrArg
    (fun x : ThreeBlockVariable (Fin W) => x.1.1) hp
  simp only [terminalSecondBalancedEntryEmbedding_val] at hrow
  exact hi p.1
    ((terminalBalancedRowEquiv rowEquiv colEquiv).injective hrow.symm)

/-- Column version of `terminalFreshCoordinate_not_mem_second_of_row`. -/
theorem terminalFreshCoordinate_not_mem_second_of_col
    {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i j : Fin r ⊕ TerminalBalancedResidualIndex rowEquiv colEquiv)
    (hfresh : threeBlockFresh
      (terminalBalancedRowEquiv rowEquiv colEquiv i)
      (terminalBalancedColEquiv rowEquiv colEquiv j))
    (hj : ∀ p : Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv),
      j ≠ Sum.inr (Sum.inr p)) :
    (⟨(terminalBalancedRowEquiv rowEquiv colEquiv i,
        terminalBalancedColEquiv rowEquiv colEquiv j), hfresh⟩ :
      ThreeBlockVariable (Fin W)) ∉
      selectedCoordinateSet
        (terminalSecondBalancedEntryEmbedding rowEquiv colEquiv) := by
  intro hmem
  simp only [selectedCoordinateSet, Finset.mem_map, Finset.mem_univ,
    true_and] at hmem
  rcases hmem with ⟨p, hp⟩
  have hcol := congrArg
    (fun x : ThreeBlockVariable (Fin W) => x.1.2) hp
  simp only [terminalSecondBalancedEntryEmbedding_val] at hcol
  exact hj p.2
    ((terminalBalancedColEquiv rowEquiv colEquiv).injective hcol.symm)

/-! ## A measurable perturbation entry from a complement coordinate -/

/-- An entry of the literal perturbation is strongly measurable in a
selected-square complement whenever its possible fresh atom is outside the
selected set. -/
theorem terminalBalancedPerturbation_entry_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q n : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (label : (Fin n × Fin n) ↪ ThreeBlockVariable (Fin W))
    (z : Complex)
    (i j : Fin r ⊕ TerminalBalancedResidualIndex rowEquiv colEquiv)
    (hout : ∀ hfresh : threeBlockFresh
        (terminalBalancedRowEquiv rowEquiv colEquiv i)
        (terminalBalancedColEquiv rowEquiv colEquiv j),
      (⟨(terminalBalancedRowEquiv rowEquiv colEquiv i,
          terminalBalancedColEquiv rowEquiv colEquiv j), hfresh⟩ :
        ThreeBlockVariable (Fin W)) ∉ selectedCoordinateSet label) :
    @StronglyMeasurable Omega Complex _
      (X.coordinateSquareConditioningSigma label)
      (fun omega =>
        terminalBalancedPerturbation rowEquiv colEquiv z X omega i j) := by
  by_cases hfresh : threeBlockFresh
      (terminalBalancedRowEquiv rowEquiv colEquiv i)
      (terminalBalancedColEquiv rowEquiv colEquiv j)
  · have hatom := X.coordinateSquare_complement_atom_stronglyMeasurable
      label
      (⟨(terminalBalancedRowEquiv rowEquiv colEquiv i,
          terminalBalancedColEquiv rowEquiv colEquiv j), hfresh⟩ :
        ThreeBlockVariable (Fin W))
      (hout hfresh)
    letI : MeasurableSpace Omega := X.coordinateSquareConditioningSigma label
    simp only [terminalBalancedPerturbation, Matrix.submatrix_apply,
      Matrix.sub_apply, Matrix.smul_apply,
      threeBlockDelta_apply_of_fresh _ _ _ hfresh]
    exact (Complex.continuous_ofReal.comp_stronglyMeasurable hatom).sub
      stronglyMeasurable_const
  · letI : MeasurableSpace Omega := X.coordinateSquareConditioningSigma label
    simp only [terminalBalancedPerturbation, Matrix.submatrix_apply,
      Matrix.sub_apply, Matrix.smul_apply,
      threeBlockDelta_apply_of_not_fresh _ _ _ hfresh]
    exact stronglyMeasurable_const.sub stronglyMeasurable_const

/-! ## Measurability through the CUR formula -/

/-- The cancellation-visible CUR deformation inherits entrywise strong
measurability from the three perturbation blocks that it actually uses.
This is deliberately stated independently of the terminal coordinates. -/
theorem F_entry_stronglyMeasurable_of_blocks
    {Omega p q : Type*} [mOmega : MeasurableSpace Omega]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (ms : MeasurableSpace Omega)
    (S : BlockSkeletonData p q)
    (Delta : Omega → Matrix (p ⊕ q) (p ⊕ q) Complex)
    (h11 : ∀ i j,
      @StronglyMeasurable Omega Complex _ ms
        (fun omega => delta11 (Delta omega) i j))
    (h12 : ∀ i j,
      @StronglyMeasurable Omega Complex _ ms
        (fun omega => delta12 (Delta omega) i j))
    (h21 : ∀ i j,
      @StronglyMeasurable Omega Complex _ ms
        (fun omega => delta21 (Delta omega) i j))
    (i j : q) :
    @StronglyMeasurable Omega Complex _ ms
      (fun omega => F S (Delta omega) i j) := by
  letI : MeasurableSpace Omega := ms
  have hY12 : ∀ a b,
      StronglyMeasurable
        (fun omega => (S.Yskel * delta12 (Delta omega)) a b) := by
    intro a b
    exact matrix_mul_entry_stronglyMeasurable ms
      (fun _ => S.Yskel) (fun omega => delta12 (Delta omega))
      (fun _ _ => stronglyMeasurable_const) h12 a b
  have h21X : ∀ a b,
      StronglyMeasurable
        (fun omega => (delta21 (Delta omega) * S.Xskel) a b) := by
    intro a b
    exact matrix_mul_entry_stronglyMeasurable ms
      (fun omega => delta21 (Delta omega)) (fun _ => S.Xskel)
      h21 (fun _ _ => stronglyMeasurable_const) a b
  have hY11 : ∀ a b,
      StronglyMeasurable
        (fun omega => (S.Yskel * delta11 (Delta omega)) a b) := by
    intro a b
    exact matrix_mul_entry_stronglyMeasurable ms
      (fun _ => S.Yskel) (fun omega => delta11 (Delta omega))
      (fun _ _ => stronglyMeasurable_const) h11 a b
  have hY11X : ∀ a b,
      StronglyMeasurable
        (fun omega => (S.Yskel * delta11 (Delta omega) * S.Xskel) a b) := by
    intro a b
    exact matrix_mul_entry_stronglyMeasurable ms
      (fun omega => S.Yskel * delta11 (Delta omega)) (fun _ => S.Xskel)
      hY11 (fun _ _ => stronglyMeasurable_const) a b
  have hK : ∀ a b,
      StronglyMeasurable (fun omega => KDelta S (Delta omega) a b) := by
    intro a b
    simp only [KDelta, Matrix.add_apply]
    exact stronglyMeasurable_const.add (h11 a b)
  have hKinv : ∀ a b,
      StronglyMeasurable (fun omega => (KDelta S (Delta omega))⁻¹ a b) := by
    intro a b
    exact matrix_nonsingInv_entry_stronglyMeasurable ms
      (fun omega => KDelta S (Delta omega)) hK a b
  have hG21 : ∀ a b,
      StronglyMeasurable (fun omega => G21 S (Delta omega) a b) := by
    intro a b
    have hmul := matrix_mul_entry_stronglyMeasurable ms
      (fun _ => S.Yskel) (fun omega => delta11 (Delta omega))
      (fun _ _ => stronglyMeasurable_const) h11 a b
    simp only [G21, Matrix.sub_apply]
    exact (h21 a b).sub hmul
  have hG12 : ∀ a b,
      StronglyMeasurable (fun omega => G12 S (Delta omega) a b) := by
    intro a b
    have hmul := matrix_mul_entry_stronglyMeasurable ms
      (fun omega => delta11 (Delta omega)) (fun _ => S.Xskel)
      h11 (fun _ _ => stronglyMeasurable_const) a b
    simp only [G12, Matrix.sub_apply]
    exact (h12 a b).sub hmul
  have hGinv : ∀ a b,
      StronglyMeasurable
        (fun omega => (G21 S (Delta omega) *
          (KDelta S (Delta omega))⁻¹) a b) := by
    intro a b
    exact matrix_mul_entry_stronglyMeasurable ms
      (fun omega => G21 S (Delta omega))
      (fun omega => (KDelta S (Delta omega))⁻¹)
      hG21 hKinv a b
  have hGinvG : ∀ a b,
      StronglyMeasurable
        (fun omega => (G21 S (Delta omega) *
          (KDelta S (Delta omega))⁻¹ * G12 S (Delta omega)) a b) := by
    intro a b
    exact matrix_mul_entry_stronglyMeasurable ms
      (fun omega => G21 S (Delta omega) * (KDelta S (Delta omega))⁻¹)
      (fun omega => G12 S (Delta omega)) hGinv hG12 a b
  simp only [F, Matrix.sub_apply, Matrix.add_apply]
  exact ((((stronglyMeasurable_const.sub (hY12 i j)).sub (h21X i j)).add
    (hY11X i j)).sub (hGinvG i j))

/-! ## First-square complement -/

theorem terminalDelta11_firstConditioning_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex) (i j : Fin r) :
    @StronglyMeasurable Omega Complex _
      (X.terminalFirstConditioningSigma rowEquiv colEquiv)
      (fun omega => delta11
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega) i j) := by
  apply terminalBalancedPerturbation_entry_stronglyMeasurable X rowEquiv colEquiv
    (terminalFirstBalancedEntryEmbedding rowEquiv colEquiv) z
      (Sum.inl i) (Sum.inl j)
  intro hfresh
  apply terminalFreshCoordinate_not_mem_first_of_row
    rowEquiv colEquiv (Sum.inl i) (Sum.inl j) hfresh
  intro p h
  cases h

theorem terminalDelta12_firstConditioning_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex) (i : Fin r)
    (j : TerminalBalancedResidualIndex rowEquiv colEquiv) :
    @StronglyMeasurable Omega Complex _
      (X.terminalFirstConditioningSigma rowEquiv colEquiv)
      (fun omega => delta12
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega) i j) := by
  apply terminalBalancedPerturbation_entry_stronglyMeasurable X rowEquiv colEquiv
    (terminalFirstBalancedEntryEmbedding rowEquiv colEquiv) z
      (Sum.inl i) (Sum.inr j)
  intro hfresh
  apply terminalFreshCoordinate_not_mem_first_of_row
    rowEquiv colEquiv (Sum.inl i) (Sum.inr j) hfresh
  intro p h
  cases h

theorem terminalDelta21_firstConditioning_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (i : TerminalBalancedResidualIndex rowEquiv colEquiv) (j : Fin r) :
    @StronglyMeasurable Omega Complex _
      (X.terminalFirstConditioningSigma rowEquiv colEquiv)
      (fun omega => delta21
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega) i j) := by
  apply terminalBalancedPerturbation_entry_stronglyMeasurable X rowEquiv colEquiv
    (terminalFirstBalancedEntryEmbedding rowEquiv colEquiv) z
      (Sum.inr i) (Sum.inl j)
  intro hfresh
  apply terminalFreshCoordinate_not_mem_first_of_col
    rowEquiv colEquiv (Sum.inr i) (Sum.inl j) hfresh
  intro p h
  cases h

theorem terminalF_firstConditioning_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (i j : TerminalBalancedResidualIndex rowEquiv colEquiv) :
    @StronglyMeasurable Omega Complex _
      (X.terminalFirstConditioningSigma rowEquiv colEquiv)
      (fun omega => F (terminalExtendedSkeletonData rowEquiv colEquiv S)
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega) i j) := by
  exact F_entry_stronglyMeasurable_of_blocks
    (X.terminalFirstConditioningSigma rowEquiv colEquiv)
    (terminalExtendedSkeletonData rowEquiv colEquiv S)
    (fun omega => terminalBalancedPerturbation rowEquiv colEquiv z X omega)
    (terminalDelta11_firstConditioning_stronglyMeasurable X rowEquiv colEquiv z)
    (terminalDelta12_firstConditioning_stronglyMeasurable X rowEquiv colEquiv z)
    (terminalDelta21_firstConditioning_stronglyMeasurable X rowEquiv colEquiv z)
    i j

/-- Every entry of the first literal Cook deformation is strongly measurable
in the complement of the first globally selected iid square. -/
theorem terminalFirstCookDeformation_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (i j : Fin (terminalBalancedSize rowEquiv colEquiv)) :
    @StronglyMeasurable Omega Complex _
      (X.terminalFirstConditioningSigma rowEquiv colEquiv)
      (fun omega => terminalFirstCookDeformation
        S rowEquiv colEquiv z X omega i j) := by
  have hF := terminalF_firstConditioning_stronglyMeasurable
    S rowEquiv colEquiv z X (Sum.inl i) (Sum.inl j)
  simp only [terminalFirstCookDeformation, terminalCURBaseDeformation,
    Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.add_apply, Matrix.neg_apply]
  exact stronglyMeasurable_const.add hF

/-! ## Second-square complement -/

theorem terminalDelta11_secondConditioning_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex) (i j : Fin r) :
    @StronglyMeasurable Omega Complex _
      (X.terminalSecondConditioningSigma rowEquiv colEquiv)
      (fun omega => delta11
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega) i j) := by
  apply terminalBalancedPerturbation_entry_stronglyMeasurable X rowEquiv colEquiv
    (terminalSecondBalancedEntryEmbedding rowEquiv colEquiv) z
      (Sum.inl i) (Sum.inl j)
  intro hfresh
  apply terminalFreshCoordinate_not_mem_second_of_row
    rowEquiv colEquiv (Sum.inl i) (Sum.inl j) hfresh
  intro p h
  cases h

theorem terminalDelta12_secondConditioning_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex) (i : Fin r)
    (j : TerminalBalancedResidualIndex rowEquiv colEquiv) :
    @StronglyMeasurable Omega Complex _
      (X.terminalSecondConditioningSigma rowEquiv colEquiv)
      (fun omega => delta12
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega) i j) := by
  apply terminalBalancedPerturbation_entry_stronglyMeasurable X rowEquiv colEquiv
    (terminalSecondBalancedEntryEmbedding rowEquiv colEquiv) z
      (Sum.inl i) (Sum.inr j)
  intro hfresh
  apply terminalFreshCoordinate_not_mem_second_of_row
    rowEquiv colEquiv (Sum.inl i) (Sum.inr j) hfresh
  intro p h
  cases h

theorem terminalDelta21_secondConditioning_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (i : TerminalBalancedResidualIndex rowEquiv colEquiv) (j : Fin r) :
    @StronglyMeasurable Omega Complex _
      (X.terminalSecondConditioningSigma rowEquiv colEquiv)
      (fun omega => delta21
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega) i j) := by
  apply terminalBalancedPerturbation_entry_stronglyMeasurable X rowEquiv colEquiv
    (terminalSecondBalancedEntryEmbedding rowEquiv colEquiv) z
      (Sum.inr i) (Sum.inl j)
  intro hfresh
  apply terminalFreshCoordinate_not_mem_second_of_col
    rowEquiv colEquiv (Sum.inr i) (Sum.inl j) hfresh
  intro p h
  cases h

theorem terminalF_secondConditioning_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (i j : TerminalBalancedResidualIndex rowEquiv colEquiv) :
    @StronglyMeasurable Omega Complex _
      (X.terminalSecondConditioningSigma rowEquiv colEquiv)
      (fun omega => F (terminalExtendedSkeletonData rowEquiv colEquiv S)
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega) i j) := by
  exact F_entry_stronglyMeasurable_of_blocks
    (X.terminalSecondConditioningSigma rowEquiv colEquiv)
    (terminalExtendedSkeletonData rowEquiv colEquiv S)
    (fun omega => terminalBalancedPerturbation rowEquiv colEquiv z X omega)
    (terminalDelta11_secondConditioning_stronglyMeasurable X rowEquiv colEquiv z)
    (terminalDelta12_secondConditioning_stronglyMeasurable X rowEquiv colEquiv z)
    (terminalDelta21_secondConditioning_stronglyMeasurable X rowEquiv colEquiv z)
    i j

/-- Entries whose residual row belongs to the first Cook block remain
measurable while the second Cook block is kept fresh. -/
theorem terminalDelta22_firstRow_secondConditioning_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (i : Fin (terminalBalancedSize rowEquiv colEquiv))
    (j : TerminalBalancedResidualIndex rowEquiv colEquiv) :
    @StronglyMeasurable Omega Complex _
      (X.terminalSecondConditioningSigma rowEquiv colEquiv)
      (fun omega => delta22
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega)
          (Sum.inl i) j) := by
  apply terminalBalancedPerturbation_entry_stronglyMeasurable X rowEquiv colEquiv
    (terminalSecondBalancedEntryEmbedding rowEquiv colEquiv) z
      (Sum.inr (Sum.inl i)) (Sum.inr j)
  intro hfresh
  apply terminalFreshCoordinate_not_mem_second_of_row
    rowEquiv colEquiv (Sum.inr (Sum.inl i)) (Sum.inr j) hfresh
  intro p h
  cases h

/-- Column analogue needed for the lower-left residual block. -/
theorem terminalDelta22_firstCol_secondConditioning_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (i : TerminalBalancedResidualIndex rowEquiv colEquiv)
    (j : Fin (terminalBalancedSize rowEquiv colEquiv)) :
    @StronglyMeasurable Omega Complex _
      (X.terminalSecondConditioningSigma rowEquiv colEquiv)
      (fun omega => delta22
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega)
          i (Sum.inl j)) := by
  apply terminalBalancedPerturbation_entry_stronglyMeasurable X rowEquiv colEquiv
    (terminalSecondBalancedEntryEmbedding rowEquiv colEquiv) z
      (Sum.inr i) (Sum.inr (Sum.inl j))
  intro hfresh
  apply terminalFreshCoordinate_not_mem_second_of_col
    rowEquiv colEquiv (Sum.inr i) (Sum.inr (Sum.inl j)) hfresh
  intro p h
  cases h

theorem terminalCURResidual_toBlocks11_secondConditioning_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (i j : Fin (terminalBalancedSize rowEquiv colEquiv)) :
    @StronglyMeasurable Omega Complex _
      (X.terminalSecondConditioningSigma rowEquiv colEquiv)
      (fun omega =>
        (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₁₁ i j) := by
  simp only [terminalCURResidual, Matrix.toBlocks₁₁, Matrix.of_apply,
    Matrix.add_apply]
  exact (terminalDelta22_firstRow_secondConditioning_stronglyMeasurable
    X rowEquiv colEquiv z i (Sum.inl j)).add
      (terminalF_secondConditioning_stronglyMeasurable
        S rowEquiv colEquiv z X (Sum.inl i) (Sum.inl j))

theorem terminalCURResidual_toBlocks12_secondConditioning_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (i : Fin (terminalBalancedSize rowEquiv colEquiv))
    (j : Fin (W + outerResidualLeftCount rowEquiv +
      outerResidualRightCount rowEquiv -
        terminalBalancedSize rowEquiv colEquiv)) :
    @StronglyMeasurable Omega Complex _
      (X.terminalSecondConditioningSigma rowEquiv colEquiv)
      (fun omega =>
        (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₁₂ i j) := by
  simp only [terminalCURResidual, Matrix.toBlocks₁₂, Matrix.of_apply,
    Matrix.add_apply]
  exact (terminalDelta22_firstRow_secondConditioning_stronglyMeasurable
    X rowEquiv colEquiv z i (Sum.inr j)).add
      (terminalF_secondConditioning_stronglyMeasurable
        S rowEquiv colEquiv z X (Sum.inl i) (Sum.inr j))

theorem terminalCURResidual_toBlocks21_secondConditioning_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (i : Fin (W + outerResidualLeftCount rowEquiv +
      outerResidualRightCount rowEquiv -
        terminalBalancedSize rowEquiv colEquiv))
    (j : Fin (terminalBalancedSize rowEquiv colEquiv)) :
    @StronglyMeasurable Omega Complex _
      (X.terminalSecondConditioningSigma rowEquiv colEquiv)
      (fun omega =>
        (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₂₁ i j) := by
  simp only [terminalCURResidual, Matrix.toBlocks₂₁, Matrix.of_apply,
    Matrix.add_apply]
  exact (terminalDelta22_firstCol_secondConditioning_stronglyMeasurable
    X rowEquiv colEquiv z (Sum.inr i) j).add
      (terminalF_secondConditioning_stronglyMeasurable
        S rowEquiv colEquiv z X (Sum.inr i) (Sum.inl j))

/-- The base bottom-right block contains no second-square atom. -/
theorem terminalCURBaseDeformation_toBlocks22_secondConditioning_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (i j : Fin (W + outerResidualLeftCount rowEquiv +
      outerResidualRightCount rowEquiv -
        terminalBalancedSize rowEquiv colEquiv)) :
    @StronglyMeasurable Omega Complex _
      (X.terminalSecondConditioningSigma rowEquiv colEquiv)
      (fun omega =>
        (terminalCURBaseDeformation S rowEquiv colEquiv z X omega).toBlocks₂₂
          i j) := by
  have hF := terminalF_secondConditioning_stronglyMeasurable
    S rowEquiv colEquiv z X (Sum.inr i) (Sum.inr j)
  simp only [terminalCURBaseDeformation, Matrix.toBlocks₂₂,
    Matrix.of_apply, Matrix.add_apply, Matrix.neg_apply]
  exact stronglyMeasurable_const.add hF

/-- Every entry of the second literal Cook/Schur deformation is strongly
measurable in the complement of the second globally selected iid square.
The nonsingular inverse is mathlib's total adjugate-over-determinant inverse,
so the statement needs no invertibility event. -/
theorem terminalSecondCookDeformation_stronglyMeasurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (i j : Fin (W + outerResidualLeftCount rowEquiv +
      outerResidualRightCount rowEquiv -
        terminalBalancedSize rowEquiv colEquiv)) :
    @StronglyMeasurable Omega Complex _
      (X.terminalSecondConditioningSigma rowEquiv colEquiv)
      (fun omega => terminalSecondCookDeformation
        S rowEquiv colEquiv z X omega i j) := by
  let residual := fun omega => terminalCURResidual
    S rowEquiv colEquiv z X omega
  have hbase : ∀ a b,
      @StronglyMeasurable Omega Complex _
        (X.terminalSecondConditioningSigma rowEquiv colEquiv)
        (fun omega =>
          (terminalCURBaseDeformation S rowEquiv colEquiv z X omega).toBlocks₂₂
            a b) :=
    terminalCURBaseDeformation_toBlocks22_secondConditioning_stronglyMeasurable
      S rowEquiv colEquiv z X
  have h11 : ∀ a b,
      @StronglyMeasurable Omega Complex _
        (X.terminalSecondConditioningSigma rowEquiv colEquiv)
        (fun omega => (residual omega).toBlocks₁₁ a b) :=
    terminalCURResidual_toBlocks11_secondConditioning_stronglyMeasurable
      S rowEquiv colEquiv z X
  have h12 : ∀ a b,
      @StronglyMeasurable Omega Complex _
        (X.terminalSecondConditioningSigma rowEquiv colEquiv)
        (fun omega => (residual omega).toBlocks₁₂ a b) :=
    terminalCURResidual_toBlocks12_secondConditioning_stronglyMeasurable
      S rowEquiv colEquiv z X
  have h21 : ∀ a b,
      @StronglyMeasurable Omega Complex _
        (X.terminalSecondConditioningSigma rowEquiv colEquiv)
        (fun omega => (residual omega).toBlocks₂₁ a b) :=
    terminalCURResidual_toBlocks21_secondConditioning_stronglyMeasurable
      S rowEquiv colEquiv z X
  let ms : MeasurableSpace Omega :=
    X.terminalSecondConditioningSigma rowEquiv colEquiv
  letI : MeasurableSpace Omega := ms
  have h11inv : ∀ a b,
      StronglyMeasurable
        (fun omega => ((residual omega).toBlocks₁₁)⁻¹ a b) := by
    intro a b
    exact matrix_nonsingInv_entry_stronglyMeasurable
      ms
      (fun omega => (residual omega).toBlocks₁₁) h11 a b
  have h21inv : ∀ a b,
      StronglyMeasurable
        (fun omega => ((residual omega).toBlocks₂₁ *
          ((residual omega).toBlocks₁₁)⁻¹) a b) := by
    intro a b
    exact matrix_mul_entry_stronglyMeasurable
      ms
      (fun omega => (residual omega).toBlocks₂₁)
      (fun omega => ((residual omega).toBlocks₁₁)⁻¹)
      h21 h11inv a b
  have hcorrection : ∀ a b,
      StronglyMeasurable
        (fun omega => ((residual omega).toBlocks₂₁ *
          ((residual omega).toBlocks₁₁)⁻¹ *
            (residual omega).toBlocks₁₂) a b) := by
    intro a b
    exact matrix_mul_entry_stronglyMeasurable
      ms
      (fun omega => (residual omega).toBlocks₂₁ *
        ((residual omega).toBlocks₁₁)⁻¹)
      (fun omega => (residual omega).toBlocks₁₂)
      h21inv h12 a b
  simp only [terminalSecondCookDeformation]
  exact (hbase i j).sub (hcorrection i j)

end BernoulliSection9
