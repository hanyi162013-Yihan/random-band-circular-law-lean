import BernoulliSection9.TerminalConcreteCook
import Mathlib.Tactic

/-!
# The literal terminal residual as two concrete Cook squares

This module identifies the random part of the CUR residual with the two
globally selected iid squares.  The remaining matrix is defined by the
literal shift and the literal CUR deformation `F`; no abstract reindexing,
mask, or elimination certificate is exposed.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

open BernoulliLinearAlgebra

/-- The complete fresh residual matrix, in the balanced two-square order. -/
def terminalBalancedRandomResidual
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (omega : Omega) :
    Matrix (TerminalBalancedResidualIndex rowEquiv colEquiv)
      (TerminalBalancedResidualIndex rowEquiv colEquiv) Complex :=
  balancedResidualMatrix
    (outerResidualLeftCount_le rowEquiv)
    (outerResidualLeftCount_le colEquiv)
    (terminalResidual_sideCount_eq rowEquiv colEquiv)
    (outerResidualCount_add_le_two_mul rowEquiv)
    (residualFreshMatrix
      (X.terminalResidualFamily rowEquiv colEquiv) omega)

/-- The residual block of the reindexed unshifted packet matrix is exactly
the canonically reindexed complete fresh residual matrix. -/
theorem delta22_threeBlockDelta_reindexed_eq_randomResidual
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (omega : Omega) :
    delta22 ((threeBlockDelta (fun i => (X.atom i omega : Complex))).submatrix
      (terminalBalancedRowEquiv rowEquiv colEquiv)
      (terminalBalancedColEquiv rowEquiv colEquiv)) =
        terminalBalancedRandomResidual X rowEquiv colEquiv omega := by
  ext i j
  have h := congrFun (congrFun
    (threeBlockDelta_residual_eq_residualFreshMatrix
      X rowEquiv colEquiv omega)
    (terminalBalancedResidualRowEquiv rowEquiv colEquiv i))
    (terminalBalancedResidualColEquiv rowEquiv colEquiv j)
  change threeBlockDelta (fun k => (X.atom k omega : Complex))
      (terminalBalancedRowEquiv rowEquiv colEquiv (Sum.inr i))
      (terminalBalancedColEquiv rowEquiv colEquiv (Sum.inr j)) =
    residualFreshMatrix (X.terminalResidualFamily rowEquiv colEquiv) omega
      (terminalBalancedResidualRowEquiv rowEquiv colEquiv i)
      (terminalBalancedResidualColEquiv rowEquiv colEquiv j)
  rw [terminalBalancedRowEquiv_inr, terminalBalancedColEquiv_inr]
  exact h

/-- The literal reindexed spectral shift restricted to residual rows and
columns.  Independent row and column RRQR permutations mean this need not be
the identity matrix in balanced coordinates, so it is retained literally. -/
def terminalBalancedShiftResidual {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex) :
    Matrix (TerminalBalancedResidualIndex rowEquiv colEquiv)
      (TerminalBalancedResidualIndex rowEquiv colEquiv) Complex :=
  (z • (1 : Matrix (ThreeBlockIndex (Fin W))
    (ThreeBlockIndex (Fin W)) Complex)).submatrix
      (fun i => terminalBalancedRowEquiv rowEquiv colEquiv (Sum.inr i))
      (fun j => terminalBalancedColEquiv rowEquiv colEquiv (Sum.inr j))

/-- The `(2,2)` perturbation block is fresh randomness minus the literal
spectral shift. -/
theorem terminalBalancedPerturbation_delta22_eq
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex) (omega : Omega) :
    delta22 (terminalBalancedPerturbation rowEquiv colEquiv z X omega) =
      terminalBalancedRandomResidual X rowEquiv colEquiv omega -
        terminalBalancedShiftResidual rowEquiv colEquiv z := by
  ext i j
  have h := congrFun (congrFun
    (delta22_threeBlockDelta_reindexed_eq_randomResidual
      X rowEquiv colEquiv omega) i) j
  change threeBlockDelta (fun k => (X.atom k omega : Complex))
        (terminalBalancedRowEquiv rowEquiv colEquiv (Sum.inr i))
        (terminalBalancedColEquiv rowEquiv colEquiv (Sum.inr j)) -
      (z • (1 : Matrix (ThreeBlockIndex (Fin W))
        (ThreeBlockIndex (Fin W)) Complex))
        (terminalBalancedRowEquiv rowEquiv colEquiv (Sum.inr i))
        (terminalBalancedColEquiv rowEquiv colEquiv (Sum.inr j)) =
    terminalBalancedRandomResidual X rowEquiv colEquiv omega i j -
      (z • (1 : Matrix (ThreeBlockIndex (Fin W))
        (ThreeBlockIndex (Fin W)) Complex))
        (terminalBalancedRowEquiv rowEquiv colEquiv (Sum.inr i))
        (terminalBalancedColEquiv rowEquiv colEquiv (Sum.inr j))
  exact congrArg (fun x : Complex => x -
    (z • (1 : Matrix (ThreeBlockIndex (Fin W))
      (ThreeBlockIndex (Fin W)) Complex))
      (terminalBalancedRowEquiv rowEquiv colEquiv (Sum.inr i))
      (terminalBalancedColEquiv rowEquiv colEquiv (Sum.inr j))) h

/-- The shift plus CUR error left after removing all fresh residual entries. -/
def terminalCURBaseDeformation
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega) :
    Matrix (TerminalBalancedResidualIndex rowEquiv colEquiv)
      (TerminalBalancedResidualIndex rowEquiv colEquiv) Complex :=
  -terminalBalancedShiftResidual rowEquiv colEquiv z +
    F (terminalExtendedSkeletonData rowEquiv colEquiv S)
      (terminalBalancedPerturbation rowEquiv colEquiv z X omega)

/-- The literal residual determinant matrix after the first CUR elimination. -/
def terminalCURResidual
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega) :
    Matrix (TerminalBalancedResidualIndex rowEquiv colEquiv)
      (TerminalBalancedResidualIndex rowEquiv colEquiv) Complex :=
  delta22 (terminalBalancedPerturbation rowEquiv colEquiv z X omega) +
    F (terminalExtendedSkeletonData rowEquiv colEquiv S)
      (terminalBalancedPerturbation rowEquiv colEquiv z X omega)

/-- Exact separation of the residual into all fresh randomness and the CUR
deformation. -/
theorem terminalCURResidual_eq_random_add_deformation
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega) :
    terminalCURResidual S rowEquiv colEquiv z X omega =
      terminalBalancedRandomResidual X rowEquiv colEquiv omega +
        terminalCURBaseDeformation S rowEquiv colEquiv z X omega := by
  rw [terminalCURResidual, terminalCURBaseDeformation,
    terminalBalancedPerturbation_delta22_eq X rowEquiv colEquiv z omega]
  abel

/-- First diagonal fresh block, now identified directly with the square
restricted from the *global* packet family. -/
theorem terminalBalancedRandomResidual_toBlocks11
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (omega : Omega) :
    (terminalBalancedRandomResidual X rowEquiv colEquiv omega).toBlocks₁₁ =
      (X.terminalFirstCookSquare rowEquiv colEquiv).rawMatrix omega := by
  have h := balancedResidualFreshMatrix_toBlocks11
    (X.terminalResidualFamily rowEquiv colEquiv)
    (outerResidualLeftCount_le rowEquiv)
    (outerResidualLeftCount_le colEquiv)
    (terminalResidual_sideCount_eq rowEquiv colEquiv)
    (outerResidualCount_add_le_two_mul rowEquiv) omega
  ext i j
  have hij := congrFun (congrFun h i) j
  change balancedResidualMatrix
      (outerResidualLeftCount_le rowEquiv)
      (outerResidualLeftCount_le colEquiv)
      (terminalResidual_sideCount_eq rowEquiv colEquiv)
      (outerResidualCount_add_le_two_mul rowEquiv)
      (residualFreshMatrix (X.terminalResidualFamily rowEquiv colEquiv) omega)
        (Sum.inl i) (Sum.inl j) =
    ((((X.terminalResidualFamily rowEquiv colEquiv).firstBalancedCookSquare
      (outerResidualLeftCount_le rowEquiv)
      (outerResidualLeftCount_le colEquiv)
      (terminalResidual_sideCount_eq rowEquiv colEquiv)
      (outerResidualCount_add_le_two_mul rowEquiv)).atom (i, j) omega :
        Real) : Complex) at hij
  change terminalBalancedRandomResidual X rowEquiv colEquiv omega
      (Sum.inl i) (Sum.inl j) =
    (((X.terminalFirstCookSquare rowEquiv colEquiv).atom (i, j) omega :
      Real) : Complex)
  have hfresh : terminalBalancedRandomResidual X rowEquiv colEquiv omega
      (Sum.inl i) (Sum.inl j) =
    ((((X.terminalResidualFamily rowEquiv colEquiv).firstBalancedCookSquare
      (outerResidualLeftCount_le rowEquiv)
      (outerResidualLeftCount_le colEquiv)
      (terminalResidual_sideCount_eq rowEquiv colEquiv)
      (outerResidualCount_add_le_two_mul rowEquiv)).atom (i, j) omega :
        Real) : Complex) := by
    simpa [terminalBalancedRandomResidual, terminalBalancedSize,
      Matrix.toBlocks₁₁, Matrix.of_apply,
      IidSubgaussianSquare.rawMatrix] using hij
  rw [hfresh]
  exact congrArg (fun x : Real => (x : Complex))
    (congrFun (terminalFirstCookSquare_atom_eq_residual
      X rowEquiv colEquiv (i, j)).symm omega)

/-- Second diagonal fresh block, identified with the complementary globally
restricted square. -/
theorem terminalBalancedRandomResidual_toBlocks22
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (omega : Omega) :
    (terminalBalancedRandomResidual X rowEquiv colEquiv omega).toBlocks₂₂ =
      (X.terminalSecondCookSquare rowEquiv colEquiv).rawMatrix omega := by
  have h := balancedResidualFreshMatrix_toBlocks22
    (X.terminalResidualFamily rowEquiv colEquiv)
    (outerResidualLeftCount_le rowEquiv)
    (outerResidualLeftCount_le colEquiv)
    (terminalResidual_sideCount_eq rowEquiv colEquiv)
    (outerResidualCount_add_le_two_mul rowEquiv) omega
  ext i j
  have hij := congrFun (congrFun h i) j
  change balancedResidualMatrix
      (outerResidualLeftCount_le rowEquiv)
      (outerResidualLeftCount_le colEquiv)
      (terminalResidual_sideCount_eq rowEquiv colEquiv)
      (outerResidualCount_add_le_two_mul rowEquiv)
      (residualFreshMatrix (X.terminalResidualFamily rowEquiv colEquiv) omega)
        (Sum.inr i) (Sum.inr j) =
    ((((X.terminalResidualFamily rowEquiv colEquiv).secondBalancedCookSquare
      (outerResidualLeftCount_le rowEquiv)
      (outerResidualLeftCount_le colEquiv)
      (terminalResidual_sideCount_eq rowEquiv colEquiv)
      (outerResidualCount_add_le_two_mul rowEquiv)).atom (i, j) omega :
        Real) : Complex) at hij
  change terminalBalancedRandomResidual X rowEquiv colEquiv omega
      (Sum.inr i) (Sum.inr j) =
    (((X.terminalSecondCookSquare rowEquiv colEquiv).atom (i, j) omega :
      Real) : Complex)
  have hfresh : terminalBalancedRandomResidual X rowEquiv colEquiv omega
      (Sum.inr i) (Sum.inr j) =
    ((((X.terminalResidualFamily rowEquiv colEquiv).secondBalancedCookSquare
      (outerResidualLeftCount_le rowEquiv)
      (outerResidualLeftCount_le colEquiv)
      (terminalResidual_sideCount_eq rowEquiv colEquiv)
      (outerResidualCount_add_le_two_mul rowEquiv)).atom (i, j) omega :
        Real) : Complex) := by
    simpa [terminalBalancedRandomResidual, terminalBalancedSize,
      Matrix.toBlocks₂₂, Matrix.of_apply,
      IidSubgaussianSquare.rawMatrix] using hij
  rw [hfresh]
  exact congrArg (fun x : Real => (x : Complex))
    (congrFun (terminalSecondCookSquare_atom_eq_residual
      X rowEquiv colEquiv (i, j)).symm omega)

/-- The concrete first Cook deformation. -/
def terminalFirstCookDeformation
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega) :=
  (terminalCURBaseDeformation S rowEquiv colEquiv z X omega).toBlocks₁₁

/-- Literal first Cook identity. -/
theorem terminalCURResidual_toBlocks11_eq_profiled_add_deformation
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega) :
    (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₁₁ =
      profiledMatrix (X.terminalFirstCookSquare rowEquiv colEquiv)
          (unitCookProfile (terminalBalancedSize rowEquiv colEquiv)) omega +
        terminalFirstCookDeformation S rowEquiv colEquiv z X omega := by
  rw [terminalCURResidual_eq_random_add_deformation,
    profiledMatrix_unitCookProfile]
  change (terminalBalancedRandomResidual X rowEquiv colEquiv omega).toBlocks₁₁ +
      (terminalCURBaseDeformation S rowEquiv colEquiv z X omega).toBlocks₁₁ =
    (X.terminalFirstCookSquare rowEquiv colEquiv).rawMatrix omega +
      (terminalCURBaseDeformation S rowEquiv colEquiv z X omega).toBlocks₁₁
  rw [terminalBalancedRandomResidual_toBlocks11]

/-- The actual second Schur deformation after the first square is exposed. -/
def terminalSecondCookDeformation
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega) :=
  (terminalCURBaseDeformation S rowEquiv colEquiv z X omega).toBlocks₂₂ -
    (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₂₁ *
      ((terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₁₁)⁻¹ *
        (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₁₂

/-- Literal second Cook/Schur identity. -/
theorem terminalSecondCookSchur_eq_profiled_add_deformation
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega) :
    secondCookSchur
        (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₁₁
        (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₁₂
        (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₂₁
        (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₂₂ =
      profiledMatrix (X.terminalSecondCookSquare rowEquiv colEquiv)
          (unitCookProfile
            (W + outerResidualLeftCount rowEquiv +
              outerResidualRightCount rowEquiv -
                terminalBalancedSize rowEquiv colEquiv)) omega +
        terminalSecondCookDeformation S rowEquiv colEquiv z X omega := by
  have hbottom :
      (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₂₂ =
        (X.terminalSecondCookSquare rowEquiv colEquiv).rawMatrix omega +
          (terminalCURBaseDeformation S rowEquiv colEquiv z X omega).toBlocks₂₂ := by
    rw [terminalCURResidual_eq_random_add_deformation]
    change (terminalBalancedRandomResidual X rowEquiv colEquiv omega).toBlocks₂₂ +
        (terminalCURBaseDeformation S rowEquiv colEquiv z X omega).toBlocks₂₂ = _
    rw [terminalBalancedRandomResidual_toBlocks22]
  simp only [secondCookSchur, terminalSecondCookDeformation]
  rw [hbottom, profiledMatrix_unitCookProfile]
  abel

/-- Rearranged form of the preceding Schur identity, exactly matching the
`actualBottom` premise of the norm-truncation theorem. -/
theorem terminalCURResidual_bottom_eq_secondProfiled_add_deformation_add_correction
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega) :
    (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₂₂ =
      profiledMatrix (X.terminalSecondCookSquare rowEquiv colEquiv)
          (unitCookProfile
            (W + outerResidualLeftCount rowEquiv +
              outerResidualRightCount rowEquiv -
                terminalBalancedSize rowEquiv colEquiv)) omega +
        terminalSecondCookDeformation S rowEquiv colEquiv z X omega +
      (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₂₁ *
        (profiledMatrix (X.terminalFirstCookSquare rowEquiv colEquiv)
            (unitCookProfile (terminalBalancedSize rowEquiv colEquiv)) omega +
          terminalFirstCookDeformation S rowEquiv colEquiv z X omega)⁻¹ *
        (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₁₂ := by
  rw [← terminalCURResidual_toBlocks11_eq_profiled_add_deformation
    S rowEquiv colEquiv z X omega]
  have hbottom :
      (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₂₂ =
        (X.terminalSecondCookSquare rowEquiv colEquiv).rawMatrix omega +
          (terminalCURBaseDeformation S rowEquiv colEquiv z X omega).toBlocks₂₂ := by
    rw [terminalCURResidual_eq_random_add_deformation]
    change (terminalBalancedRandomResidual X rowEquiv colEquiv omega).toBlocks₂₂ +
        (terminalCURBaseDeformation S rowEquiv colEquiv z X omega).toBlocks₂₂ = _
    rw [terminalBalancedRandomResidual_toBlocks22]
  rw [hbottom, profiledMatrix_unitCookProfile]
  simp only [terminalSecondCookDeformation]
  abel

end BernoulliSection9
