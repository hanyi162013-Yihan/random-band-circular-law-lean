import BernoulliSection9.TerminalConcreteCUR
import BernoulliSection9.TerminalProbability
import Mathlib.Tactic

/-!
# Identifying the two literal Cook squares

This module identifies the diagonal blocks of the actual residual fresh
matrix with the two canonical iid squares used by the explicit Cook input.
The identifications are entrywise equalities, not distributional stand-ins.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

open BernoulliLinearAlgebra
open MeasureTheory ProbabilityTheory

universe u

/-- The unit deterministic profile appropriate for the normalized packet
model used by `packetTerminalValue`. -/
def unitCookProfile (n : Nat) : CookProfile n where
  weight := fun _ _ => 1
  lowerWeight := 1
  upperWeight := 1
  lowerWeight_pos := zero_lt_one
  bounds := by intro i j; norm_num

@[simp] theorem profiledMatrix_unitCookProfile
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {n : Nat}
    (S : IidSubgaussianSquare Omega mu n) (omega : Omega) :
    profiledMatrix S (unitCookProfile n) omega = S.rawMatrix omega := by
  ext i j
  simp [profiledMatrix, unitCookProfile, IidSubgaussianSquare.rawMatrix]

/-- Fill the seven-block residual mask with the literal atoms of `S`, and
put zero in the two forbidden rectangles. -/
def residualFreshMatrix
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (omega : Omega) :
    Matrix (ResidualIndex a b W) (ResidualIndex c e W) Complex := by
  classical
  exact fun i j => if h : residualFresh i j then
    (S.atom ⟨(i, j), h⟩ omega : Complex) else 0

/-- The first diagonal block is literally the first canonical Cook square. -/
theorem balancedResidualFreshMatrix_toBlocks11
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a ≤ W) (hc : c ≤ W)
    (hs : a + b = c + e) (hsW : a + b ≤ 2 * W)
    (omega : Omega) :
    (balancedResidualMatrix ha hc hs hsW
      (residualFreshMatrix S omega)).toBlocks₁₁ =
      (S.firstBalancedCookSquare ha hc hs hsW).rawMatrix omega := by
  ext i j
  rw [show (balancedResidualMatrix ha hc hs hsW
      (residualFreshMatrix S omega)).toBlocks₁₁ i j =
      residualFreshMatrix S omega
        (balancedResidualRowEquiv ha hc hs hsW (Sum.inl i))
        (balancedResidualColEquiv ha hc hs hsW (Sum.inl j)) by rfl]
  rw [balancedResidualRowEquiv_inl, balancedResidualColEquiv_inl]
  simp only [residualFreshMatrix,
    residualFresh_firstSquare, dite_true]
  change _ = (((S.firstBalancedCookSquare ha hc hs hsW).atom (i, j) omega :
    Real) : Complex)
  rw [firstBalancedCookSquare_atom]
  rfl

/-- The second diagonal block is literally the complementary canonical Cook
square. -/
theorem balancedResidualFreshMatrix_toBlocks22
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a ≤ W) (hc : c ≤ W)
    (hs : a + b = c + e) (hsW : a + b ≤ 2 * W)
    (omega : Omega) :
    (balancedResidualMatrix ha hc hs hsW
      (residualFreshMatrix S omega)).toBlocks₂₂ =
      (S.secondBalancedCookSquare ha hc hs hsW).rawMatrix omega := by
  ext i j
  rw [show (balancedResidualMatrix ha hc hs hsW
      (residualFreshMatrix S omega)).toBlocks₂₂ i j =
      residualFreshMatrix S omega
        (balancedResidualRowEquiv ha hc hs hsW (Sum.inr i))
        (balancedResidualColEquiv ha hc hs hsW (Sum.inr j)) by rfl]
  rw [balancedResidualRowEquiv_inr, balancedResidualColEquiv_inr]
  simp only [residualFreshMatrix,
    residualFresh_secondSquare, dite_true]
  change _ = (((S.secondBalancedCookSquare ha hc hs hsW).atom (i, j) omega :
    Real) : Complex)
  rw [secondBalancedCookSquare_atom]
  rfl

/-- The actual terminal `threeBlockDelta`, restricted to residual rows and
columns, is the abstract residual fresh matrix of the canonically restricted
family. -/
theorem threeBlockDelta_residual_eq_residualFreshMatrix
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (omega : Omega) :
    (threeBlockDelta (fun i => (X.atom i omega : Complex))).submatrix
        (terminalResidualIndexEmbedding rowEquiv)
        (terminalResidualIndexEmbedding colEquiv) =
      residualFreshMatrix
        (X.terminalResidualFamily rowEquiv colEquiv) omega := by
  ext i j
  change threeBlockDelta (fun i => (X.atom i omega : Complex))
      (terminalResidualIndexEmbedding rowEquiv i)
      (terminalResidualIndexEmbedding colEquiv j) =
    residualFreshMatrix
      (X.terminalResidualFamily rowEquiv colEquiv) omega i j
  by_cases h : residualFresh i j
  · rw [threeBlockDelta_apply_of_fresh _ _ _
      (terminalResidual_fresh rowEquiv colEquiv i j h)]
    simp only [residualFreshMatrix, h, dite_true,
      IidSubgaussianFamily.terminalResidualFamily,
      IidSubgaussianFamily.reindex]
    rfl
  · rw [threeBlockDelta_apply_of_not_fresh]
    · simp [residualFreshMatrix, h]
    · intro hfresh
      apply h
      rcases i with (i | i) | i <;> rcases j with (j | j) | j
      · simp [residualFresh]
      · rcases terminalResidualIndexEmbedding_left rowEquiv i with ⟨i', hi⟩
        rcases terminalResidualIndexEmbedding_right colEquiv j with ⟨j', hj⟩
        rw [hi, hj] at hfresh
        exact (not_threeBlockFresh_left_right i' j') hfresh
      · simp [residualFresh]
      · rcases terminalResidualIndexEmbedding_right rowEquiv i with ⟨i', hi⟩
        rcases terminalResidualIndexEmbedding_left colEquiv j with ⟨j', hj⟩
        rw [hi, hj] at hfresh
        exact (not_threeBlockFresh_right_left i' j') hfresh
      · simp [residualFresh]
      · simp [residualFresh]
      · simp [residualFresh]
      · simp [residualFresh]
      · simp [residualFresh]

/-! ## Correct global conditioning sigma-fields -/

/-- The first Cook-square entry labels, embedded all the way into the global
packet family rather than merely into the residual subfamily. -/
def terminalFirstBalancedEntryEmbedding {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    (Fin (terminalBalancedSize rowEquiv colEquiv) ×
      Fin (terminalBalancedSize rowEquiv colEquiv)) ↪
      ThreeBlockVariable (Fin W) :=
  (firstBalancedEntryEmbedding
      (outerResidualLeftCount_le rowEquiv)
      (outerResidualLeftCount_le colEquiv)
      (terminalResidual_sideCount_eq rowEquiv colEquiv)
      (outerResidualCount_add_le_two_mul rowEquiv)).trans
    (terminalResidualFreshEntryEmbedding rowEquiv colEquiv)

/-- Global labels of the complementary Cook square. -/
def terminalSecondBalancedEntryEmbedding {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    (Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv) ×
      Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv)) ↪
      ThreeBlockVariable (Fin W) :=
  (secondBalancedEntryEmbedding
      (outerResidualLeftCount_le rowEquiv)
      (outerResidualLeftCount_le colEquiv)
      (terminalResidual_sideCount_eq rowEquiv colEquiv)
      (outerResidualCount_add_le_two_mul rowEquiv)).trans
    (terminalResidualFreshEntryEmbedding rowEquiv colEquiv)

/-- The first global square label has the literal first residual-block row
and column coordinates in the balanced ordering. -/
@[simp] theorem terminalFirstBalancedEntryEmbedding_val {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (p : Fin (terminalBalancedSize rowEquiv colEquiv) ×
      Fin (terminalBalancedSize rowEquiv colEquiv)) :
    (terminalFirstBalancedEntryEmbedding rowEquiv colEquiv p).1 =
      (terminalBalancedRowEquiv rowEquiv colEquiv
          (Sum.inr (Sum.inl p.1)),
        terminalBalancedColEquiv rowEquiv colEquiv
          (Sum.inr (Sum.inl p.2))) := by
  apply Prod.ext
  · rw [terminalBalancedRowEquiv_inr]
    change terminalResidualIndexEmbedding rowEquiv
        ((firstBalancedEntryEmbedding
          (outerResidualLeftCount_le rowEquiv)
          (outerResidualLeftCount_le colEquiv)
          (terminalResidual_sideCount_eq rowEquiv colEquiv)
          (outerResidualCount_add_le_two_mul rowEquiv) p).1.1) =
      terminalResidualIndexEmbedding rowEquiv
        (terminalBalancedResidualRowEquiv rowEquiv colEquiv (Sum.inl p.1))
    apply congrArg (terminalResidualIndexEmbedding rowEquiv)
    exact (balancedResidualRowEquiv_inl
      (outerResidualLeftCount_le rowEquiv)
      (outerResidualLeftCount_le colEquiv)
      (terminalResidual_sideCount_eq rowEquiv colEquiv)
      (outerResidualCount_add_le_two_mul rowEquiv) p.1).symm
  · rw [terminalBalancedColEquiv_inr]
    change terminalResidualIndexEmbedding colEquiv
        ((firstBalancedEntryEmbedding
          (outerResidualLeftCount_le rowEquiv)
          (outerResidualLeftCount_le colEquiv)
          (terminalResidual_sideCount_eq rowEquiv colEquiv)
          (outerResidualCount_add_le_two_mul rowEquiv) p).1.2) =
      terminalResidualIndexEmbedding colEquiv
        (terminalBalancedResidualColEquiv rowEquiv colEquiv (Sum.inl p.2))
    apply congrArg (terminalResidualIndexEmbedding colEquiv)
    exact (balancedResidualColEquiv_inl
      (outerResidualLeftCount_le rowEquiv)
      (outerResidualLeftCount_le colEquiv)
      (terminalResidual_sideCount_eq rowEquiv colEquiv)
      (outerResidualCount_add_le_two_mul rowEquiv) p.2).symm

/-- The second global square occupies the complementary residual diagonal
block in the same balanced ordering. -/
@[simp] theorem terminalSecondBalancedEntryEmbedding_val {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (p : Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv) ×
      Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv)) :
    (terminalSecondBalancedEntryEmbedding rowEquiv colEquiv p).1 =
      (terminalBalancedRowEquiv rowEquiv colEquiv
          (Sum.inr (Sum.inr p.1)),
        terminalBalancedColEquiv rowEquiv colEquiv
          (Sum.inr (Sum.inr p.2))) := by
  apply Prod.ext
  · rw [terminalBalancedRowEquiv_inr]
    change terminalResidualIndexEmbedding rowEquiv
        ((secondBalancedEntryEmbedding
          (outerResidualLeftCount_le rowEquiv)
          (outerResidualLeftCount_le colEquiv)
          (terminalResidual_sideCount_eq rowEquiv colEquiv)
          (outerResidualCount_add_le_two_mul rowEquiv) p).1.1) =
      terminalResidualIndexEmbedding rowEquiv
        (terminalBalancedResidualRowEquiv rowEquiv colEquiv (Sum.inr p.1))
    apply congrArg (terminalResidualIndexEmbedding rowEquiv)
    exact (balancedResidualRowEquiv_inr
      (outerResidualLeftCount_le rowEquiv)
      (outerResidualLeftCount_le colEquiv)
      (terminalResidual_sideCount_eq rowEquiv colEquiv)
      (outerResidualCount_add_le_two_mul rowEquiv) p.1).symm
  · rw [terminalBalancedColEquiv_inr]
    change terminalResidualIndexEmbedding colEquiv
        ((secondBalancedEntryEmbedding
          (outerResidualLeftCount_le rowEquiv)
          (outerResidualLeftCount_le colEquiv)
          (terminalResidual_sideCount_eq rowEquiv colEquiv)
          (outerResidualCount_add_le_two_mul rowEquiv) p).1.2) =
      terminalResidualIndexEmbedding colEquiv
        (terminalBalancedResidualColEquiv rowEquiv colEquiv (Sum.inr p.2))
    apply congrArg (terminalResidualIndexEmbedding colEquiv)
    exact (balancedResidualColEquiv_inr
      (outerResidualLeftCount_le rowEquiv)
      (outerResidualLeftCount_le colEquiv)
      (terminalResidual_sideCount_eq rowEquiv colEquiv)
      (outerResidualCount_add_le_two_mul rowEquiv) p.2).symm

/-- The two globally embedded complete iid squares are entrywise disjoint. -/
theorem terminalBalancedEntryEmbeddings_ne {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (p : Fin (terminalBalancedSize rowEquiv colEquiv) ×
      Fin (terminalBalancedSize rowEquiv colEquiv))
    (s : Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv) ×
      Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv)) :
    terminalFirstBalancedEntryEmbedding rowEquiv colEquiv p ≠
      terminalSecondBalancedEntryEmbedding rowEquiv colEquiv s := by
  intro h
  have hrow := congrArg
    (fun x : ThreeBlockVariable (Fin W) => x.1.1) h
  simp only [terminalFirstBalancedEntryEmbedding_val,
    terminalSecondBalancedEntryEmbedding_val] at hrow
  have hinj := (terminalBalancedRowEquiv rowEquiv colEquiv).injective hrow
  simp at hinj

/-- Every first-square coordinate lies in the global complement of the
second square. -/
theorem terminalFirstEmbedding_not_mem_secondSelected {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (p : Fin (terminalBalancedSize rowEquiv colEquiv) ×
      Fin (terminalBalancedSize rowEquiv colEquiv)) :
    terminalFirstBalancedEntryEmbedding rowEquiv colEquiv p ∉
      selectedCoordinateSet
        (terminalSecondBalancedEntryEmbedding rowEquiv colEquiv) := by
  intro hp
  rw [selectedCoordinateSet, Finset.mem_map] at hp
  rcases hp with ⟨s, -, hs⟩
  exact terminalBalancedEntryEmbeddings_ne rowEquiv colEquiv p s hs.symm

/-- Symmetric complement membership for the other conditioning order. -/
theorem terminalSecondEmbedding_not_mem_firstSelected {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (s : Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv) ×
      Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv)) :
    terminalSecondBalancedEntryEmbedding rowEquiv colEquiv s ∉
      selectedCoordinateSet
        (terminalFirstBalancedEntryEmbedding rowEquiv colEquiv) := by
  intro hs
  rw [selectedCoordinateSet, Finset.mem_map] at hs
  rcases hs with ⟨p, -, hp⟩
  exact terminalBalancedEntryEmbeddings_ne rowEquiv colEquiv p s hp

/-- First Cook square directly restricted from the global packet iid family. -/
def IidSubgaussianFamily.terminalFirstCookSquare
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    IidSubgaussianSquare Omega mu (terminalBalancedSize rowEquiv colEquiv) :=
  X.squareRestriction (terminalFirstBalancedEntryEmbedding rowEquiv colEquiv)

/-- Second Cook square directly restricted from the global packet family. -/
def IidSubgaussianFamily.terminalSecondCookSquare
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    IidSubgaussianSquare Omega mu
      (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv) :=
  X.squareRestriction (terminalSecondBalancedEntryEmbedding rowEquiv colEquiv)

/-- The globally restricted first square agrees entrywise with the first
square obtained through the residual-family restriction. -/
theorem terminalFirstCookSquare_atom_eq_residual
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (p : Fin (terminalBalancedSize rowEquiv colEquiv) ×
      Fin (terminalBalancedSize rowEquiv colEquiv)) :
    (X.terminalFirstCookSquare rowEquiv colEquiv).atom p =
      ((X.terminalResidualFamily rowEquiv colEquiv).firstBalancedCookSquare
        (outerResidualLeftCount_le rowEquiv)
        (outerResidualLeftCount_le colEquiv)
        (terminalResidual_sideCount_eq rowEquiv colEquiv)
        (outerResidualCount_add_le_two_mul rowEquiv)).atom p := by
  rfl

/-- The analogous entrywise equality for the second square. -/
theorem terminalSecondCookSquare_atom_eq_residual
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (p : Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv) ×
      Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv)) :
    (X.terminalSecondCookSquare rowEquiv colEquiv).atom p =
      ((X.terminalResidualFamily rowEquiv colEquiv).secondBalancedCookSquare
        (outerResidualLeftCount_le rowEquiv)
        (outerResidualLeftCount_le colEquiv)
        (terminalResidual_sideCount_eq rowEquiv colEquiv)
        (outerResidualCount_add_le_two_mul rowEquiv)).atom p := by
  rfl

/-- Global fresh sigma-field generated by the first Cook square. -/
@[instance_reducible] def IidSubgaussianFamily.terminalFirstFreshSigma
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    MeasurableSpace Omega :=
  X.coordinateSigma
    (selectedCoordinateSet
      (terminalFirstBalancedEntryEmbedding rowEquiv colEquiv))

/-- Global complement sigma-field: it contains every packet coordinate not
in the first Cook square, including the RRQR pivot and pivot/residual cross
entries on which `F` depends. -/
@[instance_reducible] def IidSubgaussianFamily.terminalFirstConditioningSigma
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    MeasurableSpace Omega :=
  X.coordinateSigma
    (Finset.univ \ selectedCoordinateSet
      (terminalFirstBalancedEntryEmbedding rowEquiv colEquiv))

/-- Global fresh sigma-field generated by the second Cook square. -/
@[instance_reducible] def IidSubgaussianFamily.terminalSecondFreshSigma
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    MeasurableSpace Omega :=
  X.coordinateSigma
    (selectedCoordinateSet
      (terminalSecondBalancedEntryEmbedding rowEquiv colEquiv))

/-- Global complement sigma-field for the second Cook application.  It
contains the entire first square, all cross blocks, and all pivot data. -/
@[instance_reducible] def IidSubgaussianFamily.terminalSecondConditioningSigma
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    MeasurableSpace Omega :=
  X.coordinateSigma
    (Finset.univ \ selectedCoordinateSet
      (terminalSecondBalancedEntryEmbedding rowEquiv colEquiv))

end BernoulliSection9
