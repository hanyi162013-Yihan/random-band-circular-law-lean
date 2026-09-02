import BernoulliSection9.TerminalConcreteEventBounds

/-!
# Eventwise bounds for the literal CUR cross blocks

On the coordinatewise exposure event, the two off-diagonal blocks of the
literal CUR residual have the same explicit `3W`-dimensional bound.  Combined
with the first-block inverse estimate, this controls the genuine second Cook
deformation.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 3000000

namespace BernoulliSection9

open MeasureTheory BernoulliLinearAlgebra
open TerminalAssembly

private theorem terminalCrossBlock_card_product_le {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    (terminalBalancedSize rowEquiv colEquiv : Real) *
        (W + outerResidualLeftCount rowEquiv +
          outerResidualRightCount rowEquiv -
            terminalBalancedSize rowEquiv colEquiv : Nat) <=
      ((3 * W : Nat) : Real) ^ 2 := by
  have hfirst : (terminalBalancedSize rowEquiv colEquiv : Real) <=
      (3 * W : Nat) := by
    exact_mod_cast terminalBalancedFirstSize_le_three_mul rowEquiv colEquiv
  have hsecond :
      ((W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv : Nat) : Real) <=
        (3 * W : Nat) := by
    exact_mod_cast terminalBalancedSecondSize_le_three_mul rowEquiv colEquiv
  calc
    _ <= ((3 * W : Nat) : Real) * (3 * W : Nat) :=
      mul_le_mul hfirst hsecond (by positivity) (by positivity)
    _ = _ := by ring

private theorem norm_terminalCURResidual_cross_entry_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (M : Real) (hM : 0 <= M) (omega : Omega)
    (homega : omega ∈ coordinatewiseBoundedEvent X M)
    (Fscale : Real)
    (hF : ‖F (terminalExtendedSkeletonData rowEquiv colEquiv S)
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega)‖ <= Fscale)
    (i j : TerminalBalancedResidualIndex rowEquiv colEquiv) :
    ‖terminalCURResidual S rowEquiv colEquiv z X omega i j‖ <=
      M + ‖z‖ + Fscale := by
  let Delta := terminalBalancedPerturbation rowEquiv colEquiv z X omega
  let Sext := terminalExtendedSkeletonData rowEquiv colEquiv S
  have hDelta : ‖Delta (Sum.inr i) (Sum.inr j)‖ <= M + ‖z‖ :=
    norm_terminalBalancedPerturbation_entry_le
      rowEquiv colEquiv z X M hM omega homega (Sum.inr i) (Sum.inr j)
  have hFentry : ‖F Sext Delta i j‖ <= Fscale :=
    (norm_matrix_entry_le_l2_opNorm (F Sext Delta) i j).trans hF
  change ‖Delta (Sum.inr i) (Sum.inr j) + F Sext Delta i j‖ <= _
  exact (norm_add_le _ _).trans (by linarith)

/-- On the coordinatewise exposure event, the upper-right block of the
literal CUR residual has the explicit ambient-dimension bound. -/
theorem norm_terminalCURResidual_toBlocks12_le_scale
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (M : Real) (hM : 0 <= M) (omega : Omega)
    (homega : omega ∈ coordinatewiseBoundedEvent X M)
    (Fscale : Real) (hF0 : 0 <= Fscale)
    (hF : ‖F (terminalExtendedSkeletonData rowEquiv colEquiv S)
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega)‖ <= Fscale) :
    ‖(terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₁₂‖ <=
      ((3 * W : Nat) : Real) ^ 2 * (M + ‖z‖ + Fscale) := by
  have hentry := fun i j => norm_terminalCURResidual_cross_entry_le
    S rowEquiv colEquiv z X M hM omega homega Fscale hF
      (Sum.inl i) (Sum.inr j)
  have hraw := norm_matrix_le_card_mul_card_mul_of_entry_norm_le
    (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₁₂
    (M + ‖z‖ + Fscale) hentry
  have hscale : 0 <= M + ‖z‖ + Fscale := by positivity
  have hcard :
      (Fintype.card (Fin (terminalBalancedSize rowEquiv colEquiv)) : Real) *
          Fintype.card (Fin (W + outerResidualLeftCount rowEquiv +
            outerResidualRightCount rowEquiv -
              terminalBalancedSize rowEquiv colEquiv)) <=
        ((3 * W : Nat) : Real) ^ 2 := by
    simpa only [Fintype.card_fin] using
      terminalCrossBlock_card_product_le rowEquiv colEquiv
  exact hraw.trans (mul_le_mul_of_nonneg_right hcard hscale)

/-- On the coordinatewise exposure event, the lower-left block of the
literal CUR residual has the same explicit ambient-dimension bound. -/
theorem norm_terminalCURResidual_toBlocks21_le_scale
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (M : Real) (hM : 0 <= M) (omega : Omega)
    (homega : omega ∈ coordinatewiseBoundedEvent X M)
    (Fscale : Real) (hF0 : 0 <= Fscale)
    (hF : ‖F (terminalExtendedSkeletonData rowEquiv colEquiv S)
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega)‖ <= Fscale) :
    ‖(terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₂₁‖ <=
      ((3 * W : Nat) : Real) ^ 2 * (M + ‖z‖ + Fscale) := by
  have hentry := fun i j => norm_terminalCURResidual_cross_entry_le
    S rowEquiv colEquiv z X M hM omega homega Fscale hF
      (Sum.inr i) (Sum.inl j)
  have hraw := norm_matrix_le_card_mul_card_mul_of_entry_norm_le
    (terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₂₁
    (M + ‖z‖ + Fscale) hentry
  have hscale : 0 <= M + ‖z‖ + Fscale := by positivity
  have hcard := terminalCrossBlock_card_product_le rowEquiv colEquiv
  have hcard' :
      ((W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv : Nat) : Real) *
          terminalBalancedSize rowEquiv colEquiv <=
        ((3 * W : Nat) : Real) ^ 2 := by
    simpa [mul_comm] using hcard
  have hcard'' :
      (Fintype.card (Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv)) : Real) *
          Fintype.card (Fin (terminalBalancedSize rowEquiv colEquiv)) <=
        ((3 * W : Nat) : Real) ^ 2 := by
    simpa only [Fintype.card_fin] using hcard'
  exact hraw.trans (mul_le_mul_of_nonneg_right hcard'' hscale)

/-- Eventwise bound for the genuine second Cook deformation.  Here
`crossScale` is the common explicit bound for the two off-diagonal residual
blocks. -/
theorem norm_terminalSecondCookDeformation_le_crossScale
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (M : Real) (hM : 0 <= M) (omega : Omega)
    (homega : omega ∈ coordinatewiseBoundedEvent X M)
    (Fscale : Real) (hF0 : 0 <= Fscale)
    (hF : ‖F (terminalExtendedSkeletonData rowEquiv colEquiv S)
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega)‖ <= Fscale)
    (J : Real)
    (hInv : ‖((terminalCURResidual S rowEquiv colEquiv z X omega).toBlocks₁₁)⁻¹‖ <= J) :
    let crossScale :=
      ((3 * W : Nat) : Real) ^ 2 * (M + ‖z‖ + Fscale)
    ‖terminalSecondCookDeformation S rowEquiv colEquiv z X omega‖ <=
      ((3 * W : Nat) : Real) ^ 2 * (‖z‖ + Fscale) +
        crossScale * J * crossScale := by
  dsimp only
  let R := terminalCURResidual S rowEquiv colEquiv z X omega
  let crossScale := ((3 * W : Nat) : Real) ^ 2 * (M + ‖z‖ + Fscale)
  have hcross0 : 0 <= crossScale := by
    dsimp [crossScale]
    positivity
  have hJ0 : 0 <= J := (norm_nonneg R.toBlocks₁₁⁻¹).trans hInv
  have h12 : ‖R.toBlocks₁₂‖ <= crossScale := by
    exact norm_terminalCURResidual_toBlocks12_le_scale
      S rowEquiv colEquiv z X M hM omega homega Fscale hF0 hF
  have h21 : ‖R.toBlocks₂₁‖ <= crossScale := by
    exact norm_terminalCURResidual_toBlocks21_le_scale
      S rowEquiv colEquiv z X M hM omega homega Fscale hF0 hF
  have hproduct : ‖R.toBlocks₂₁ * R.toBlocks₁₁⁻¹ * R.toBlocks₁₂‖ <=
      crossScale * J * crossScale := by
    calc
      _ <= (‖R.toBlocks₂₁‖ * ‖R.toBlocks₁₁⁻¹‖) * ‖R.toBlocks₁₂‖ := by
        exact (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _)
            (norm_nonneg _))
      _ <= _ := mul_le_mul
        (mul_le_mul h21 hInv (norm_nonneg _) hcross0) h12
        (norm_nonneg _) (mul_nonneg hcross0 hJ0)
  unfold terminalSecondCookDeformation
  change ‖(terminalCURBaseDeformation S rowEquiv colEquiv z X omega).toBlocks₂₂ -
      R.toBlocks₂₁ * R.toBlocks₁₁⁻¹ * R.toBlocks₁₂‖ <= _
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_terminalCURBaseDeformation22_le_scale
      S rowEquiv colEquiv z X omega Fscale hF0 hF)
    hproduct)

end BernoulliSection9
