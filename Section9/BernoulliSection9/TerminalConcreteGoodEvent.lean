import BernoulliSection9.TerminalConcreteControl
import BernoulliSection9.TerminalConcreteFactorBounds
import BernoulliSection9.TerminalUniformCook
import Mathlib.Tactic

/-!
# The concrete two-Cook good event

This is the probability-bearing part of the literal terminal assembly.  The
two deformations are norm-truncated, and the first Cook lower bound
is converted internally into the inverse estimate needed for the second
Schur deformation.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 8000000

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory BernoulliLinearAlgebra
open TerminalAssembly

universe u v

/-- Eventwise first-deformation norm bound with the dimension comparison
already discharged. -/
theorem terminalConcreteFirstDeformationNorm
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (row col : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (M Fscale L : Real) (hM : 0 <= M) (hF0 : 0 <= Fscale)
    (omega : Omega) (homega : omega ∈ coordinatewiseBoundedEvent X M)
    (hF : ‖F (terminalExtendedSkeletonData row col S)
      (terminalBalancedPerturbation row col z X omega)‖ <= Fscale)
    (hpoly : ((3 * W : Nat) : Real) ^ 2 * (‖z‖ + Fscale) <=
      ((W / 3 : Nat) : Real) ^ L)
    (hL : 0 <= L) :
    ‖terminalFirstCookDeformation S row col z X omega‖ <=
      (terminalBalancedSize row col : Real) ^ L := by
  have hraw := norm_terminalFirstCookDeformation_le_scale
    S row col z X omega Fscale hF0 hF
  exact (hraw.trans hpoly).trans
    (Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast div_three_le_terminalBalancedFirstSize row col) hL)

/-- Off the first Cook bad event for the truncated deformation, the literal first residual
block has the inverse bound used by the second Schur deformation. -/
theorem terminalConcreteFirstResidualInverse
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W r q : Nat}
    (cook : CookDeformedSquareInput)
    (S : BlockSkeletonData (Fin r) (Fin q))
    (row col : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega) (L : Real)
    (hn : 2 <= terminalBalancedSize row col)
    (hnW : terminalBalancedSize row col <= 3 * W)
    (hD : ‖terminalFirstCookDeformation S row col z X omega‖ <=
      (terminalBalancedSize row col : Real) ^ L)
    (hgood : omega ∉ cookBadEvent (X.terminalFirstCookSquare row col)
      (unitCookProfile (terminalBalancedSize row col))
      (matrixNormTruncation
        ((terminalBalancedSize row col : Real) ^ L)
        (terminalFirstCookDeformation S row col z X))
      (cook.beta L)) :
    ‖((terminalCURResidual S row col z X omega).toBlocks₁₁)⁻¹‖ <=
      ((3 * W : Nat) : Real) ^ cook.beta L := by
  let rawD := terminalFirstCookDeformation S row col z X
  let n := terminalBalancedSize row col
  let epsilon : Real := (n : Real) ^ (-cook.beta L)
  have hDeq := matrixNormTruncation_eq_of_norm_le rawD omega hD
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hnle : ¬ matrixSMin
      (profiledMatrix (X.terminalFirstCookSquare row col)
          (unitCookProfile n) omega +
        matrixNormTruncation ((n : Real) ^ L) rawD omega) <= epsilon := by
    simpa [cookBadEvent, rawD, n, epsilon] using hgood
  have hminRaw : epsilon <= matrixSMin
      (profiledMatrix (X.terminalFirstCookSquare row col)
          (unitCookProfile n) omega + rawD omega) := by
    rw [← hDeq]
    exact (lt_of_not_ge hnle).le
  have hresidual := terminalCURResidual_toBlocks11_eq_profiled_add_deformation
    S row col z X omega
  have hmin : epsilon <=
      matrixSMin (terminalCURResidual S row col z X omega).toBlocks₁₁ := by
    rw [hresidual]
    exact hminRaw
  have hinv := norm_nonsing_inv_le_inv_of_le_matrixSMin
    (lt_of_lt_of_le Nat.zero_lt_two hn)
    (terminalCURResidual S row col z X omega).toBlocks₁₁ hepsilon hmin
  calc
    _ <= epsilon⁻¹ := hinv
    _ = (n : Real) ^ cook.beta L := by
      dsimp [epsilon]
      rw [Real.rpow_neg (by positivity)]
      simp
    _ <= ((3 * W : Nat) : Real) ^ cook.beta L :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnW)
        (cook.beta_pos L).le

/-- Eventwise genuine second-deformation bound after the first residual
inverse has been controlled. -/
theorem terminalConcreteSecondDeformationNorm
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W r q : Nat}
    (S : BlockSkeletonData (Fin r) (Fin q))
    (row col : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (M Fscale J L : Real) (hM : 0 <= M) (hF0 : 0 <= Fscale)
    (omega : Omega) (homega : omega ∈ coordinatewiseBoundedEvent X M)
    (hF : ‖F (terminalExtendedSkeletonData row col S)
      (terminalBalancedPerturbation row col z X omega)‖ <= Fscale)
    (hInv : ‖((terminalCURResidual S row col z X omega).toBlocks₁₁)⁻¹‖ <= J)
    (hpoly : ((3 * W : Nat) : Real) ^ 2 * (‖z‖ + Fscale) +
      (((3 * W : Nat) : Real) ^ 2 * (M + ‖z‖ + Fscale)) * J *
        (((3 * W : Nat) : Real) ^ 2 * (M + ‖z‖ + Fscale)) <=
      ((W / 3 : Nat) : Real) ^ L)
    (hL : 0 <= L) :
    ‖terminalSecondCookDeformation S row col z X omega‖ <=
      ((W + outerResidualLeftCount row + outerResidualRightCount row -
        terminalBalancedSize row col : Nat) : Real) ^ L := by
  have hraw := norm_terminalSecondCookDeformation_le_crossScale
    S row col z X M hM omega homega Fscale hF0 hF J hInv
  exact (hraw.trans hpoly).trans
    (Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast div_three_le_terminalBalancedSecondSize row col) hL)

/-- Generic packaging of norm-truncated two-Cook control into the terminal
good-event interface. -/
structure CoordinateTwoCookTruncatedPremises
    {Omega : Type u} [MeasurableSpace Omega]
    (cook : CookDeformedSquareInput.{u, u})
    (mu : Measure Omega)
    {w : Type v} [Fintype w] [DecidableEq w]
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable w))
    {n₁ n₂ : Nat}
    (label₁ : (Fin n₁ × Fin n₁) ↪ ThreeBlockVariable w)
    (label₂ : (Fin n₂ × Fin n₂) ↪ ThreeBlockVariable w)
    (profile₁ : CookProfile n₁) (profile₂ : CookProfile n₂)
    (L₁ L₂ exposureFailure : Real)
    (rawD₁ : Omega -> Matrix (Fin n₁) (Fin n₁) Complex)
    (rawD₂ : Omega -> Matrix (Fin n₂) (Fin n₂) Complex)
    (cross₁₂ : Omega -> Matrix (Fin n₁) (Fin n₂) Complex)
    (cross₂₁ : Omega -> Matrix (Fin n₂) (Fin n₁) Complex)
    (actualBottom : Omega -> Matrix (Fin n₂) (Fin n₂) Complex)
    (exposure : Set Omega) : Prop where
  hsubgaussian : X.subgaussianParameter <= cook.subgaussianBound
  hprofile₁ : forall i j,
    cook.lowerWeight <= profile₁.weight i j ∧
      profile₁.weight i j <= cook.upperWeight
  hprofile₂ : forall i j,
    cook.lowerWeight <= profile₂.weight i j ∧
      profile₂.weight i j <= cook.upperWeight
  hn₁ : 2 <= n₁
  hn₂ : 2 <= n₂
  hL₁ : 0 <= L₁
  hL₂ : 0 <= L₂
  exposure_measurable : MeasurableSet exposure
  exposure_probability : mu.real exposureᶜ <= exposureFailure
  rawD₁_measurable : forall i j,
    @StronglyMeasurable Omega Complex _
      (X.coordinateSquareConditioningSigma label₁)
      (fun omega => rawD₁ omega i j)
  rawD₂_measurable : forall i j,
    @StronglyMeasurable Omega Complex _
      (X.coordinateSquareConditioningSigma label₂)
      (fun omega => rawD₂ omega i j)
  rawD₁_norm : forall omega, omega ∈ exposure ->
    ‖rawD₁ omega‖ <= (n₁ : Real) ^ L₁
  rawD₂_norm : forall omega, omega ∈ exposure ->
    omega ∉ cookBadEvent (X.squareRestriction label₁) profile₁
      (matrixNormTruncation ((n₁ : Real) ^ L₁) rawD₁)
      (cook.beta L₁) ->
    ‖rawD₂ omega‖ <= (n₂ : Real) ^ L₂
  actualBottom_eq : forall omega,
    actualBottom omega =
      profiledMatrix (X.squareRestriction label₂) profile₂ omega +
        rawD₂ omega +
      cross₂₁ omega *
        (profiledMatrix (X.squareRestriction label₁) profile₁ omega +
          rawD₁ omega)⁻¹ * cross₁₂ omega

noncomputable def packetTerminalGoodEventControl_of_coordinateTwoCookTruncated
    {Omega : Type u} [MeasurableSpace Omega]
    (cook : CookDeformedSquareInput.{u, u})
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {w : Type v} [Fintype w] [DecidableEq w]
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable w))
    {n₁ n₂ : Nat}
    (label₁ : (Fin n₁ × Fin n₁) ↪ ThreeBlockVariable w)
    (label₂ : (Fin n₂ × Fin n₂) ↪ ThreeBlockVariable w)
    (profile₁ : CookProfile n₁) (profile₂ : CookProfile n₂)
    (L₁ L₂ exposureFailure valueLoss badProbability : Real)
    (rawD₁ : Omega -> Matrix (Fin n₁) (Fin n₁) Complex)
    (rawD₂ : Omega -> Matrix (Fin n₂) (Fin n₂) Complex)
    (cross₁₂ : Omega -> Matrix (Fin n₁) (Fin n₂) Complex)
    (cross₂₁ : Omega -> Matrix (Fin n₂) (Fin n₁) Complex)
    (actualBottom : Omega -> Matrix (Fin n₂) (Fin n₂) Complex)
    (exposure : Set Omega)
    (P : CoordinateTwoCookTruncatedPremises cook mu X label₁ label₂
      profile₁ profile₂ L₁ L₂ exposureFailure rawD₁ rawD₂
      cross₁₂ cross₂₁ actualBottom exposure)
    (hprob : exposureFailure +
      (cookFailureBound (cook.cookC L₁) (cook.cookc L₁) n₁ +
        cookFailureBound (cook.cookC L₂) (cook.cookc L₂) n₂) <=
      badProbability)
    (hvalue : forall omega, omega ∈ exposure ->
      ((n₁ : Real) ^ (-cook.beta L₁)) ^ n₁ *
          ((n₂ : Real) ^ (-cook.beta L₂)) ^ n₂ <=
        ‖(Matrix.fromBlocks
          (profiledMatrix (X.squareRestriction label₁) profile₁ omega +
            rawD₁ omega)
          (cross₁₂ omega) (cross₂₁ omega) (actualBottom omega)).det‖ ->
      Real.exp (-valueLoss) * gramVolume Q <=
        ‖packetTerminalValue Q z X omega‖) :
    PacketTerminalGoodEventControl mu Q z X valueLoss badProbability := by
  have hCook := coordinateTwoCookTruncated_probability_and_det
    cook mu X label₁ label₂ profile₁ profile₂ L₁ L₂ exposureFailure
    rawD₁ rawD₂ cross₁₂ cross₂₁ actualBottom exposure
    P.hsubgaussian P.hprofile₁ P.hprofile₂ P.hn₁ P.hn₂ P.hL₁ P.hL₂ P.exposure_measurable
    P.exposure_probability P.rawD₁_measurable P.rawD₂_measurable
    P.rawD₁_norm P.rawD₂_norm P.actualBottom_eq
  let bad := coordinateTwoCookTruncatedBadEvent cook X label₁ label₂
    profile₁ profile₂ L₁ L₂ rawD₁ rawD₂ exposure
  refine
    { bad := bad
      measurable_bad := by simpa [bad] using hCook.1
      probability_bad := hCook.2.1.trans hprob
      value_lower := ?_ }
  intro omega homega
  have hexposure : omega ∈ exposure := by
    by_contra hnot
    apply homega
    simpa [bad, coordinateTwoCookTruncatedBadEvent] using Or.inl hnot
  exact hvalue omega hexposure
    (hCook.2.2 omega (by simpa [bad] using homega))

/-- All canonical measurability, truncation-norm and Schur-identity premises
for the two coordinate Cook calls.  This theorem is internal: its conclusion
contains only the definitions computed from the paper data, and no caller
chooses any of them. -/
theorem packetTerminalCanonicalCookPremises
    {Omega : Type u} [MeasurableSpace Omega]
    (cook : CookDeformedSquareInput.{u, u})
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W : Nat} (Kz : Nat) (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (t : Real)
    (hnum : PacketTerminalCanonicalLargeWConditions cook z X Kz t)
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (hn : 2 <= 2 * W)
    (htau : 1 <= terminalCanonicalThreshold W Kz) :
    let tau := terminalCanonicalThreshold W Kz
    let row := packetRRQRRowEquiv Q tau hn htau
    let col := packetRRQRColEquiv Q tau hn htau
    let S := packetRRQRSkeleton Q tau hn htau
    let M := terminalConcreteExposureThreshold X t
    let exposure : Set Omega := coordinatewiseBoundedEvent X M
    let n₁ := terminalBalancedSize row col
    let n₂ := W + outerResidualLeftCount row +
      outerResidualRightCount row - n₁
    let label₁ := terminalFirstBalancedEntryEmbedding row col
    let label₂ := terminalSecondBalancedEntryEmbedding row col
    let profile₁ := unitCookProfile n₁
    let profile₂ := unitCookProfile n₂
    let L₁ := terminalCanonicalFirstCookExponent Kz
    let L₂ := terminalCanonicalSecondCookExponent cook Kz
    let rawD₁ := terminalFirstCookDeformation S row col z X
    let rawD₂ := terminalSecondCookDeformation S row col z X
    let residual := terminalCURResidual S row col z X
    let cross₁₂ := fun omega => (residual omega).toBlocks₁₂
    let cross₂₁ := fun omega => (residual omega).toBlocks₂₁
    let actualBottom := fun omega => (residual omega).toBlocks₂₂
    CoordinateTwoCookTruncatedPremises cook mu X label₁ label₂
      profile₁ profile₂ L₁ L₂ (Real.exp (-t)) rawD₁ rawD₂
      cross₁₂ cross₂₁ actualBottom exposure := by
  have hWpos : 0 < W := by
    have hWlarge := hnum.W_large
    omega
  letI : Nonempty (Fin W) := Fin.pos_iff_nonempty.mp hWpos
  let tau := terminalCanonicalThreshold W Kz
  let row := packetRRQRRowEquiv Q tau hn htau
  let col := packetRRQRColEquiv Q tau hn htau
  let S := packetRRQRSkeleton Q tau hn htau
  let M := terminalConcreteExposureThreshold X t
  let exposure : Set Omega := coordinatewiseBoundedEvent X M
  let n₁ := terminalBalancedSize row col
  let n₂ := W + outerResidualLeftCount row + outerResidualRightCount row - n₁
  let label₁ := terminalFirstBalancedEntryEmbedding row col
  let label₂ := terminalSecondBalancedEntryEmbedding row col
  let profile₁ := unitCookProfile n₁
  let profile₂ := unitCookProfile n₂
  let L₁ := terminalCanonicalFirstCookExponent Kz
  let L₂ := terminalCanonicalSecondCookExponent cook Kz
  let rawD₁ := terminalFirstCookDeformation S row col z X
  let rawD₂ := terminalSecondCookDeformation S row col z X
  let residual := terminalCURResidual S row col z X
  let cross₁₂ := fun omega => (residual omega).toBlocks₁₂
  let cross₂₁ := fun omega => (residual omega).toBlocks₂₁
  let actualBottom := fun omega => (residual omega).toBlocks₂₂
  let Fscale := terminalUniformFScale W tau M z
  let J := terminalUniformFirstCookInverseScale cook W Kz
  change CoordinateTwoCookTruncatedPremises cook mu X label₁ label₂
    profile₁ profile₂ L₁ L₂ (Real.exp (-t)) rawD₁ rawD₂
    cross₁₂ cross₂₁ actualBottom exposure
  have hM : 0 <= M := by
    exact zero_le_one.trans (packetCoordinateMaxThreshold_one_le X t)
  have hF0 : 0 <= Fscale := by
    dsimp [Fscale]
    apply terminalFPolynomialScale_nonneg
    · dsimp [terminalUniformCoefficientScale]
      positivity
    · dsimp [terminalUniformErrorScale]
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
        (zero_le_one.trans htau))
    · dsimp [terminalUniformDeltaScale]
      exact mul_nonneg (by positivity) (add_nonneg hM (norm_nonneg z))
    · dsimp [terminalPivotInverseScale]
      positivity
  have hn₁ : 2 <= n₁ := by
    dsimp [n₁]
    exact terminalBalancedFirstSize_two_le row col (by
      have hWlarge := hnum.W_large
      omega)
  have hn₂ : 2 <= n₂ := by
    dsimp [n₂, n₁]
    exact terminalBalancedSecondSize_two_le row col (by
      have hWlarge := hnum.W_large
      omega)
  have hL₁ : 0 <= L₁ := terminalCanonicalFirstCookExponent_nonneg Kz
  have hL₂ : 0 <= L₂ := terminalCanonicalSecondCookExponent_nonneg cook Kz
  have hn₁W : n₁ <= 3 * W := by
    dsimp [n₁]
    exact terminalBalancedFirstSize_le_three_mul row col
  have hexposureMeas : MeasurableSet exposure :=
    measurableSet_coordinatewiseBoundedEvent X M
  have hexposureProb : mu.real exposureᶜ <= Real.exp (-t) :=
    measureReal_compl_packetCoordinateMaxEvent_le mu X t hnum.t_nonneg
  have hrawD₁Meas : forall i j,
      @StronglyMeasurable Omega Complex _
        (X.coordinateSquareConditioningSigma label₁)
        (fun omega => rawD₁ omega i j) := by
    intro i j
    change @StronglyMeasurable Omega Complex _
      (X.terminalFirstConditioningSigma row col)
      (fun omega => terminalFirstCookDeformation S row col z X omega i j)
    exact terminalFirstCookDeformation_stronglyMeasurable S row col z X i j
  have hrawD₂Meas : forall i j,
      @StronglyMeasurable Omega Complex _
        (X.coordinateSquareConditioningSigma label₂)
        (fun omega => rawD₂ omega i j) := by
    intro i j
    change @StronglyMeasurable Omega Complex _
      (X.terminalSecondConditioningSigma row col)
      (fun omega => terminalSecondCookDeformation S row col z X omega i j)
    exact terminalSecondCookDeformation_stronglyMeasurable S row col z X i j
  have hrawD₁Norm : forall omega, omega ∈ exposure ->
      ‖rawD₁ omega‖ <= (n₁ : Real) ^ L₁ := by
    intro omega homega
    have H := packetTerminalExposureBounds Q tau hn htau z X M hM
      (by simpa [tau, M] using hnum.pivot_small) omega homega
    exact terminalConcreteFirstDeformationNorm S row col z X M Fscale L₁
      hM hF0 omega homega
      (by simpa [S, row, col, Fscale] using H.F_norm)
      (by simpa [Fscale, L₁, tau, M,
        terminalUniformFirstDeformationScale] using hnum.first_polynomial)
      hL₁
  have hrawD₂Norm : forall omega, omega ∈ exposure ->
      omega ∉ cookBadEvent (X.squareRestriction label₁) profile₁
        (matrixNormTruncation ((n₁ : Real) ^ L₁) rawD₁)
        (cook.beta L₁) ->
      ‖rawD₂ omega‖ <= (n₂ : Real) ^ L₂ := by
    intro omega homega hfirstGood
    have H := packetTerminalExposureBounds Q tau hn htau z X M hM
      (by simpa [tau, M] using hnum.pivot_small) omega homega
    have hD₁bound := hrawD₁Norm omega homega
    have hinv : ‖((residual omega).toBlocks₁₁)⁻¹‖ <= J := by
      simpa [residual, J, L₁, terminalUniformFirstCookInverseScale,
        Nat.cast_mul] using
        terminalConcreteFirstResidualInverse cook S row col z X omega L₁
          (by simpa [n₁] using hn₁) (by simpa [n₁] using hn₁W)
          (by simpa [rawD₁, n₁] using hD₁bound)
          (by
            simpa [label₁, profile₁, rawD₁, n₁,
              IidSubgaussianFamily.terminalFirstCookSquare] using hfirstGood)
    exact terminalConcreteSecondDeformationNorm S row col z X M Fscale J L₂
      hM hF0 omega homega
      (by simpa [S, row, col, Fscale] using H.F_norm)
      (by simpa [residual] using hinv)
      (by simpa [Fscale, J, L₁, L₂, tau, M,
        terminalUniformSecondDeformationScale,
        terminalUniformFirstDeformationScale,
        terminalUniformCrossScale,
        terminalUniformFirstCookInverseScale] using hnum.second_polynomial)
      hL₂
  have hactualBottom : forall omega,
      actualBottom omega =
        profiledMatrix (X.squareRestriction label₂) profile₂ omega +
          rawD₂ omega +
        cross₂₁ omega *
          (profiledMatrix (X.squareRestriction label₁) profile₁ omega +
            rawD₁ omega)⁻¹ * cross₁₂ omega := by
    intro omega
    have h :=
      terminalCURResidual_bottom_eq_secondProfiled_add_deformation_add_correction
        S row col z X omega
    change actualBottom omega =
      profiledMatrix (X.squareRestriction label₂) profile₂ omega +
        rawD₂ omega +
      cross₂₁ omega *
        (profiledMatrix (X.squareRestriction label₁) profile₁ omega +
          rawD₁ omega)⁻¹ * cross₁₂ omega at h
    exact h
  exact
    { hsubgaussian := hnum.subgaussian_bound
      hprofile₁ := fun _ _ => ⟨cook.lowerWeight_le_one, cook.one_le_upperWeight⟩
      hprofile₂ := fun _ _ => ⟨cook.lowerWeight_le_one, cook.one_le_upperWeight⟩
      hn₁ := hn₁
      hn₂ := hn₂
      hL₁ := hL₁
      hL₂ := hL₂
      exposure_measurable := hexposureMeas
      exposure_probability := hexposureProb
      rawD₁_measurable := hrawD₁Meas
      rawD₂_measurable := hrawD₂Meas
      rawD₁_norm := hrawD₁Norm
      rawD₂_norm := hrawD₂Norm
      actualBottom_eq := hactualBottom }

/-- The scalar factor comparison, perturbed-pivot determinant bound and
literal CUR determinant identity convert a residual determinant bound into
the terminal value lower bound. -/
theorem terminalConcreteValueLower_of_residualDet
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W : Nat}
    (cook : CookDeformedSquareInput) (Kz : Nat) (hW : 9 <= W)
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (hn : 2 <= 2 * W)
    (htau : 1 <= terminalCanonicalThreshold W Kz)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (M : Real) (omega : Omega)
    (H : PacketTerminalExposureBounds Q
      (terminalCanonicalThreshold W Kz) hn htau z X M omega)
    (hdetResidual :
      let tau := terminalCanonicalThreshold W Kz
      let row := packetRRQRRowEquiv Q tau hn htau
      let col := packetRRQRColEquiv Q tau hn htau
      let S := packetRRQRSkeleton Q tau hn htau
      let n₁ := terminalBalancedSize row col
      let n₂ := W + outerResidualLeftCount row +
        outerResidualRightCount row - n₁
      ((n₁ : Real) ^
          (-cook.beta (terminalCanonicalFirstCookExponent Kz))) ^ n₁ *
          ((n₂ : Real) ^
            (-cook.beta
              (terminalCanonicalSecondCookExponent cook Kz))) ^ n₂ <=
        ‖(terminalCURResidual S row col z X omega).det‖) :
    Real.exp (-terminalUniformValueLoss cook W Kz) * gramVolume Q <=
      ‖packetTerminalValue Q z X omega‖ := by
  let tau := terminalCanonicalThreshold W Kz
  let r := packetLargeSingularValueCount Q tau
  let row := packetRRQRRowEquiv Q tau hn htau
  let col := packetRRQRColEquiv Q tau hn htau
  let S := packetRRQRSkeleton Q tau hn htau
  let n₁ := terminalBalancedSize row col
  let n₂ := W + outerResidualLeftCount row + outerResidualRightCount row - n₁
  let L₁ := terminalCanonicalFirstCookExponent Kz
  let L₂ := terminalCanonicalSecondCookExponent cook Kz
  let residual := terminalCURResidual S row col z X
  have hdetResidual' :
      ((n₁ : Real) ^ (-cook.beta L₁)) ^ n₁ *
          ((n₂ : Real) ^ (-cook.beta L₂)) ^ n₂ <=
        ‖(residual omega).det‖ := by
    simpa [tau, row, col, S, n₁, n₂, L₁, L₂, residual] using hdetResidual
  have hfactor := terminalUniformDeterminantFactor_le_actualFactors
    (Kz := Kz) cook hW (rrqr_split_rank_le_two_mul row)
    (div_three_le_terminalBalancedFirstSize row col)
    (terminalBalancedFirstSize_le_three_mul row col)
    (div_three_le_terminalBalancedSecondSize row col)
    (terminalBalancedSecondSize_le_three_mul row col)
  have hvalueScale := exp_neg_terminalUniformValueLoss_mul_gramVolume_le
    (Kz := Kz) cook (by omega : 0 < W) Q
  have hterminalEq :=
    norm_packetTerminal_det_eq_internalRRQR_pivot_mul_residual
      Q tau hn htau z X omega H.pivot_unit
  calc
    Real.exp (-terminalUniformValueLoss cook W Kz) * gramVolume Q <=
        terminalUniformDeterminantFactor cook W Kz *
          largeSingularProduct
            (Matrix.toEuclideanLin (packetOuterFinMatrix Q)) r := by
      simpa [tau, r] using hvalueScale
    _ <= ((2 : Real)⁻¹ ^ r * packetTerminalRRQRPivotLower Q tau) *
        (((n₁ : Real) ^ (-cook.beta L₁)) ^ n₁ *
          ((n₂ : Real) ^ (-cook.beta L₂)) ^ n₂) := by
      have hP := largeSingularProduct_nonneg
        (Matrix.toEuclideanLin (packetOuterFinMatrix Q)) r
      have hmul := mul_le_mul_of_nonneg_right hfactor hP
      simpa [packetTerminalRRQRPivotLower, tau, r, n₁, n₂, L₁, L₂,
        mul_assoc, mul_left_comm, mul_comm] using hmul
    _ <= ‖(KDelta
        (terminalExtendedSkeletonData row col S)
        (terminalBalancedPerturbation row col z X omega)).det‖ *
          ‖(residual omega).det‖ :=
      mul_le_mul H.pivot_determinant hdetResidual'
        (by positivity) (by positivity)
    _ = ‖packetTerminalValue Q z X omega‖ := by
      simpa [packetTerminalValue, residual, row, col, S, tau] using
        hterminalEq.symm

/-- The complete certificate-free RRQR/CUR/two-Cook good-event control for
one row-scaled packet matrix. -/
noncomputable def packetTerminalConcreteGoodEventControl
    {Omega : Type u} [MeasurableSpace Omega]
    (cook : CookDeformedSquareInput.{u, u})
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W : Nat} (Kz : Nat) (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (t : Real)
    (hnum : PacketTerminalCanonicalLargeWConditions cook z X Kz t)
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex) :
    PacketTerminalGoodEventControl mu Q z X
      (terminalUniformValueLoss cook W Kz)
      (terminalUniformBadProbability cook W Kz t) := by
  have hWpos : 0 < W := by
    have h := hnum.W_large
    omega
  letI : Nonempty (Fin W) := Fin.pos_iff_nonempty.mp hWpos
  let tau := terminalCanonicalThreshold W Kz
  have htau : 1 <= tau := by
    exact terminalCanonicalThreshold_one_le (by
      have h := hnum.W_large
      omega)
  have hn : 2 <= 2 * W := by
    have h := hnum.W_large
    omega
  let r := packetLargeSingularValueCount Q tau
  let q := 2 * W - r
  let row := packetRRQRRowEquiv Q tau hn htau
  let col := packetRRQRColEquiv Q tau hn htau
  let S := packetRRQRSkeleton Q tau hn htau
  let M := terminalConcreteExposureThreshold X t
  let exposure : Set Omega := coordinatewiseBoundedEvent X M
  let n₁ := terminalBalancedSize row col
  let n₂ := W + outerResidualLeftCount row + outerResidualRightCount row - n₁
  let label₁ := terminalFirstBalancedEntryEmbedding row col
  let label₂ := terminalSecondBalancedEntryEmbedding row col
  let profile₁ := unitCookProfile n₁
  let profile₂ := unitCookProfile n₂
  let L₁ := terminalCanonicalFirstCookExponent Kz
  let L₂ := terminalCanonicalSecondCookExponent cook Kz
  let rawD₁ := terminalFirstCookDeformation S row col z X
  let rawD₂ := terminalSecondCookDeformation S row col z X
  let residual := terminalCURResidual S row col z X
  let cross₁₂ := fun omega => (residual omega).toBlocks₁₂
  let cross₂₁ := fun omega => (residual omega).toBlocks₂₁
  let actualBottom := fun omega => (residual omega).toBlocks₂₂
  have hM : 0 <= M := by
    exact zero_le_one.trans (packetCoordinateMaxThreshold_one_le X t)
  have hWdiv₁ : W / 3 <= n₁ := by
    dsimp [n₁]
    exact div_three_le_terminalBalancedFirstSize row col
  have hWdiv₂ : W / 3 <= n₂ := by
    dsimp [n₂, n₁]
    exact div_three_le_terminalBalancedSecondSize row col
  have hn₁W : n₁ <= 3 * W := by
    dsimp [n₁]
    exact terminalBalancedFirstSize_le_three_mul row col
  have hn₂W : n₂ <= 3 * W := by
    dsimp [n₂, n₁]
    exact terminalBalancedSecondSize_le_three_mul row col
  have P : CoordinateTwoCookTruncatedPremises cook mu X label₁ label₂
      profile₁ profile₂ L₁ L₂ (Real.exp (-t)) rawD₁ rawD₂
      cross₁₂ cross₂₁ actualBottom exposure := by
    simpa [tau, row, col, S, M, exposure, n₁, n₂, label₁, label₂,
      profile₁, profile₂, L₁, L₂, rawD₁, rawD₂, residual, cross₁₂,
      cross₂₁, actualBottom] using
      packetTerminalCanonicalCookPremises cook mu Kz z X t hnum Q hn
        (by simpa [tau] using htau)
  apply packetTerminalGoodEventControl_of_coordinateTwoCookTruncated
    cook mu Q z X label₁ label₂ profile₁ profile₂ L₁ L₂
      (Real.exp (-t)) (terminalUniformValueLoss cook W Kz)
      (terminalUniformBadProbability cook W Kz t)
      rawD₁ rawD₂ cross₁₂ cross₂₁ actualBottom exposure
      P
  · have huniform := twoCookFailureBounds_le_uniform_of_input cook L₁ L₂
      W n₁ n₂ hnum.W_large hWdiv₁ hn₁W hWdiv₂ hn₂W
    dsimp [terminalUniformBadProbability]
    linarith
  · intro omega hexposure hdetResidualRaw
    have hdetResidual :
        ((n₁ : Real) ^ (-cook.beta L₁)) ^ n₁ *
            ((n₂ : Real) ^ (-cook.beta L₂)) ^ n₂ <=
          ‖(residual omega).det‖ := by
      have h11 := terminalCURResidual_toBlocks11_eq_profiled_add_deformation
        S row col z X omega
      have h11' : (residual omega).toBlocks₁₁ =
          profiledMatrix (X.squareRestriction label₁) profile₁ omega +
            rawD₁ omega := by
        simpa [residual, label₁, profile₁, n₁, rawD₁,
          IidSubgaussianFamily.terminalFirstCookSquare] using h11
      have hblocks : Matrix.fromBlocks
          (profiledMatrix (X.squareRestriction label₁) profile₁ omega + rawD₁ omega)
          (cross₁₂ omega) (cross₂₁ omega) (actualBottom omega) =
          residual omega := by
        rw [← h11']
        exact Matrix.fromBlocks_toBlocks (residual omega)
      simpa [hblocks] using hdetResidualRaw
    have H := packetTerminalExposureBounds Q tau hn htau z X M hM
      (by simpa [tau, M] using hnum.pivot_small) omega hexposure
    exact terminalConcreteValueLower_of_residualDet cook Kz hnum.W_large Q hn
      (by simpa [tau] using htau) z X M omega
      (by simpa [tau] using H)
      (by simpa [tau, row, col, S, n₁, n₂, L₁, L₂, residual] using
        hdetResidual)

end BernoulliSection9
