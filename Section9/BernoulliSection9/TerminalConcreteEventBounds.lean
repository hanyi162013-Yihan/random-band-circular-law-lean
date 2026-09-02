import BernoulliSection9.TerminalConcreteScales

/-!
# Eventwise bounds for the literal Cook deformations

These lemmas convert the entrywise maximum-coordinate event and the CUR
bound into the two raw deformation estimates used by norm
truncation.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 3000000

namespace BernoulliSection9

open MeasureTheory BernoulliLinearAlgebra
open TerminalAssembly

private theorem firstSize_cast_le_three_mul {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    (terminalBalancedSize rowEquiv colEquiv : Real) <= (3 * W : Nat) := by
  exact_mod_cast terminalBalancedFirstSize_le_three_mul rowEquiv colEquiv

private theorem secondSize_cast_le_three_mul {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    ((W + outerResidualLeftCount rowEquiv + outerResidualRightCount rowEquiv -
      terminalBalancedSize rowEquiv colEquiv : Nat) : Real) <=
        (3 * W : Nat) := by
  exact_mod_cast terminalBalancedSecondSize_le_three_mul rowEquiv colEquiv

private theorem firstSize_sq_le_three_mul_sq {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    (terminalBalancedSize rowEquiv colEquiv : Real) ^ 2 <=
      ((3 * W : Nat) : Real) ^ 2 := by
  have h := firstSize_cast_le_three_mul rowEquiv colEquiv
  nlinarith [sq_nonneg
    ((terminalBalancedSize rowEquiv colEquiv : Real) - (3 * W : Nat))]

private theorem secondSize_sq_le_three_mul_sq {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    (((W + outerResidualLeftCount rowEquiv + outerResidualRightCount rowEquiv -
      terminalBalancedSize rowEquiv colEquiv : Nat) : Real)) ^ 2 <=
      ((3 * W : Nat) : Real) ^ 2 := by
  have h := secondSize_cast_le_three_mul rowEquiv colEquiv
  nlinarith [sq_nonneg
    (((W + outerResidualLeftCount rowEquiv + outerResidualRightCount rowEquiv -
      terminalBalancedSize rowEquiv colEquiv : Nat) : Real) - (3 * W : Nat))]

private theorem norm_shift11_le {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex) :
    ‖(terminalBalancedShiftResidual rowEquiv colEquiv z).toBlocks₁₁‖ <=
      ((3 * W : Nat) : Real) ^ 2 * ‖z‖ := by
  have hentry : forall i j,
      ‖(terminalBalancedShiftResidual rowEquiv colEquiv z).toBlocks₁₁ i j‖ <=
        ‖z‖ := by
    intro i j
    let a := terminalBalancedRowEquiv rowEquiv colEquiv
      (Sum.inr (Sum.inl i))
    let b := terminalBalancedColEquiv rowEquiv colEquiv
      (Sum.inr (Sum.inl j))
    change ‖z * (1 : Matrix (ThreeBlockIndex (Fin W))
      (ThreeBlockIndex (Fin W)) Complex) a b‖ <= ‖z‖
    rw [norm_mul]
    have hone : ‖(1 : Matrix (ThreeBlockIndex (Fin W))
        (ThreeBlockIndex (Fin W)) Complex) a b‖ <= 1 := by
      by_cases h : a = b <;> simp [Matrix.one_apply, h]
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hone (norm_nonneg z))
  have hraw := norm_matrix_le_card_mul_card_mul_of_entry_norm_le
    (terminalBalancedShiftResidual rowEquiv colEquiv z).toBlocks₁₁
    ‖z‖ hentry
  calc
    _ <= (terminalBalancedSize rowEquiv colEquiv : Real) ^ 2 * ‖z‖ := by
      simpa [pow_two] using hraw
    _ <= ((3 * W : Nat) : Real) ^ 2 * ‖z‖ :=
      mul_le_mul_of_nonneg_right
        (firstSize_sq_le_three_mul_sq rowEquiv colEquiv) (norm_nonneg z)

private theorem norm_shift22_le {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex) :
    ‖(terminalBalancedShiftResidual rowEquiv colEquiv z).toBlocks₂₂‖ <=
      ((3 * W : Nat) : Real) ^ 2 * ‖z‖ := by
  have hentry : forall i j,
      ‖(terminalBalancedShiftResidual rowEquiv colEquiv z).toBlocks₂₂ i j‖ <=
        ‖z‖ := by
    intro i j
    let a := terminalBalancedRowEquiv rowEquiv colEquiv
      (Sum.inr (Sum.inr i))
    let b := terminalBalancedColEquiv rowEquiv colEquiv
      (Sum.inr (Sum.inr j))
    change ‖z * (1 : Matrix (ThreeBlockIndex (Fin W))
      (ThreeBlockIndex (Fin W)) Complex) a b‖ <= ‖z‖
    rw [norm_mul]
    have hone : ‖(1 : Matrix (ThreeBlockIndex (Fin W))
        (ThreeBlockIndex (Fin W)) Complex) a b‖ <= 1 := by
      by_cases h : a = b <;> simp [Matrix.one_apply, h]
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hone (norm_nonneg z))
  have hraw := norm_matrix_le_card_mul_card_mul_of_entry_norm_le
    (terminalBalancedShiftResidual rowEquiv colEquiv z).toBlocks₂₂
    ‖z‖ hentry
  calc
    _ <= (((W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv : Nat) : Real)) ^ 2 * ‖z‖ := by
      simpa [pow_two] using hraw
    _ <= ((3 * W : Nat) : Real) ^ 2 * ‖z‖ :=
      mul_le_mul_of_nonneg_right
        (secondSize_sq_le_three_mul_sq rowEquiv colEquiv) (norm_nonneg z)

private theorem norm_F11_le
    {W r q : Nat} (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (Delta : Matrix (Fin r ⊕ TerminalBalancedResidualIndex rowEquiv colEquiv)
      (Fin r ⊕ TerminalBalancedResidualIndex rowEquiv colEquiv) Complex)
    (Fscale : Real) (hF0 : 0 <= Fscale)
    (hF : ‖F (terminalExtendedSkeletonData rowEquiv colEquiv S) Delta‖ <= Fscale) :
    ‖(F (terminalExtendedSkeletonData rowEquiv colEquiv S) Delta).toBlocks₁₁‖ <=
      ((3 * W : Nat) : Real) ^ 2 * Fscale := by
  have hraw := norm_matrix_le_card_mul_card_mul_of_entry_norm_le
    (F (terminalExtendedSkeletonData rowEquiv colEquiv S) Delta).toBlocks₁₁
    Fscale (fun i j =>
      (norm_matrix_entry_le_l2_opNorm
        (F (terminalExtendedSkeletonData rowEquiv colEquiv S) Delta)
        (Sum.inl i) (Sum.inl j)).trans hF)
  calc
    _ <= (terminalBalancedSize rowEquiv colEquiv : Real) ^ 2 * Fscale := by
      simpa [pow_two] using hraw
    _ <= ((3 * W : Nat) : Real) ^ 2 * Fscale :=
      mul_le_mul_of_nonneg_right
        (firstSize_sq_le_three_mul_sq rowEquiv colEquiv) hF0

private theorem norm_F22_le
    {W r q : Nat} (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (Delta : Matrix (Fin r ⊕ TerminalBalancedResidualIndex rowEquiv colEquiv)
      (Fin r ⊕ TerminalBalancedResidualIndex rowEquiv colEquiv) Complex)
    (Fscale : Real) (hF0 : 0 <= Fscale)
    (hF : ‖F (terminalExtendedSkeletonData rowEquiv colEquiv S) Delta‖ <= Fscale) :
    ‖(F (terminalExtendedSkeletonData rowEquiv colEquiv S) Delta).toBlocks₂₂‖ <=
      ((3 * W : Nat) : Real) ^ 2 * Fscale := by
  have hraw := norm_matrix_le_card_mul_card_mul_of_entry_norm_le
    (F (terminalExtendedSkeletonData rowEquiv colEquiv S) Delta).toBlocks₂₂
    Fscale (fun i j =>
      (norm_matrix_entry_le_l2_opNorm
        (F (terminalExtendedSkeletonData rowEquiv colEquiv S) Delta)
        (Sum.inr i) (Sum.inr j)).trans hF)
  calc
    _ <= (((W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv : Nat) : Real)) ^ 2 * Fscale := by
      simpa [pow_two] using hraw
    _ <= ((3 * W : Nat) : Real) ^ 2 * Fscale :=
      mul_le_mul_of_nonneg_right
        (secondSize_sq_le_three_mul_sq rowEquiv colEquiv) hF0

/-- Eventwise first raw deformation bound. -/
theorem norm_terminalFirstCookDeformation_le_scale
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega) (Fscale : Real) (hF0 : 0 <= Fscale)
    (hF : ‖F (terminalExtendedSkeletonData rowEquiv colEquiv S)
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega)‖ <= Fscale) :
    ‖terminalFirstCookDeformation S rowEquiv colEquiv z X omega‖ <=
      ((3 * W : Nat) : Real) ^ 2 * (‖z‖ + Fscale) := by
  unfold terminalFirstCookDeformation terminalCURBaseDeformation
  change ‖-(terminalBalancedShiftResidual rowEquiv colEquiv z).toBlocks₁₁ +
    (F (terminalExtendedSkeletonData rowEquiv colEquiv S)
      (terminalBalancedPerturbation rowEquiv colEquiv z X omega)).toBlocks₁₁‖ <= _
  calc
    _ <= ‖-(terminalBalancedShiftResidual rowEquiv colEquiv z).toBlocks₁₁‖ +
        ‖(F (terminalExtendedSkeletonData rowEquiv colEquiv S)
          (terminalBalancedPerturbation rowEquiv colEquiv z X omega)).toBlocks₁₁‖ :=
      norm_add_le _ _
    _ = ‖(terminalBalancedShiftResidual rowEquiv colEquiv z).toBlocks₁₁‖ +
        ‖(F (terminalExtendedSkeletonData rowEquiv colEquiv S)
          (terminalBalancedPerturbation rowEquiv colEquiv z X omega)).toBlocks₁₁‖ := by
      rw [norm_neg]
    _ <= ((3 * W : Nat) : Real) ^ 2 * ‖z‖ +
        ((3 * W : Nat) : Real) ^ 2 * Fscale :=
      add_le_add (norm_shift11_le rowEquiv colEquiv z)
        (norm_F11_le S rowEquiv colEquiv _ Fscale hF0 hF)
    _ = _ := by ring

/-- Eventwise bottom deterministic block bound. -/
theorem norm_terminalCURBaseDeformation22_le_scale
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega) (Fscale : Real) (hF0 : 0 <= Fscale)
    (hF : ‖F (terminalExtendedSkeletonData rowEquiv colEquiv S)
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega)‖ <= Fscale) :
    ‖(terminalCURBaseDeformation S rowEquiv colEquiv z X omega).toBlocks₂₂‖ <=
      ((3 * W : Nat) : Real) ^ 2 * (‖z‖ + Fscale) := by
  unfold terminalCURBaseDeformation
  change ‖-(terminalBalancedShiftResidual rowEquiv colEquiv z).toBlocks₂₂ +
    (F (terminalExtendedSkeletonData rowEquiv colEquiv S)
      (terminalBalancedPerturbation rowEquiv colEquiv z X omega)).toBlocks₂₂‖ <= _
  calc
    _ <= ‖-(terminalBalancedShiftResidual rowEquiv colEquiv z).toBlocks₂₂‖ +
        ‖(F (terminalExtendedSkeletonData rowEquiv colEquiv S)
          (terminalBalancedPerturbation rowEquiv colEquiv z X omega)).toBlocks₂₂‖ :=
      norm_add_le _ _
    _ = ‖(terminalBalancedShiftResidual rowEquiv colEquiv z).toBlocks₂₂‖ +
        ‖(F (terminalExtendedSkeletonData rowEquiv colEquiv S)
          (terminalBalancedPerturbation rowEquiv colEquiv z X omega)).toBlocks₂₂‖ := by
      rw [norm_neg]
    _ <= ((3 * W : Nat) : Real) ^ 2 * ‖z‖ +
        ((3 * W : Nat) : Real) ^ 2 * Fscale :=
      add_le_add (norm_shift22_le rowEquiv colEquiv z)
        (norm_F22_le S rowEquiv colEquiv _ Fscale hF0 hF)
    _ = _ := by ring

end BernoulliSection9
