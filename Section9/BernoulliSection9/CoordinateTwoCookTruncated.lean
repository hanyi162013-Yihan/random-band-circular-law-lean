import BernoulliSection9.CookTruncation

/-!
# Two conditional Cook estimates with exposure truncation

The raw terminal deformations are polynomially bounded only on an exposure
event (and, for the second Schur deformation, on the first-Cook good event).
This module norm-truncates both deformations before applying Cook.  To keep
the second Schur identity true at every sample point, it also defines an
artificial bottom block whose Schur complement is tautologically the second
truncated square.  On the genuine good event both truncations disappear and
the artificial block is the actual residual block.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory

universe u v

/-- Artificial bottom block which makes the second truncated Schur identity
hold globally, including outside the exposure event. -/
def artificialSecondCookBottom
    {Omega iota : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [Fintype iota] [DecidableEq iota]
    {n₁ n₂ : Nat}
    (X : IidSubgaussianFamily Omega mu iota)
    (label₁ : (Fin n₁ × Fin n₁) ↪ iota)
    (label₂ : (Fin n₂ × Fin n₂) ↪ iota)
    (profile₁ : CookProfile n₁) (profile₂ : CookProfile n₂)
    (D₁ : Omega → Matrix (Fin n₁) (Fin n₁) Complex)
    (D₂ : Omega → Matrix (Fin n₂) (Fin n₂) Complex)
    (cross₁₂ : Omega → Matrix (Fin n₁) (Fin n₂) Complex)
    (cross₂₁ : Omega → Matrix (Fin n₂) (Fin n₁) Complex)
    (omega : Omega) : Matrix (Fin n₂) (Fin n₂) Complex :=
  profiledMatrix (X.squareRestriction label₂) profile₂ omega + D₂ omega +
    cross₂₁ omega *
      (profiledMatrix (X.squareRestriction label₁) profile₁ omega +
        D₁ omega)⁻¹ * cross₁₂ omega

/-- The enlarged bad event consists of exposure failure and the two Cook
failures for the norm-truncated deformations. -/
def coordinateTwoCookTruncatedBadEvent
    {Omega iota : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [Fintype iota] [DecidableEq iota]
    {n₁ n₂ : Nat}
    (cook : CookDeformedSquareInput)
    (X : IidSubgaussianFamily Omega mu iota)
    (label₁ : (Fin n₁ × Fin n₁) ↪ iota)
    (label₂ : (Fin n₂ × Fin n₂) ↪ iota)
    (profile₁ : CookProfile n₁) (profile₂ : CookProfile n₂)
    (L₁ L₂ : Real)
    (rawD₁ : Omega → Matrix (Fin n₁) (Fin n₁) Complex)
    (rawD₂ : Omega → Matrix (Fin n₂) (Fin n₂) Complex)
    (exposure : Set Omega) : Set Omega :=
  exposureᶜ ∪
    coordinateTwoCookBadEvent cook X label₁ label₂ profile₁ profile₂ L₁ L₂
      (matrixNormTruncation ((n₁ : Real) ^ L₁) rawD₁)
      (matrixNormTruncation ((n₂ : Real) ^ L₂) rawD₂)

/-- Two-Cook determinant estimate with exposure truncation.

The hypotheses about `rawD₁` and `rawD₂` are only concrete entrywise
measurability and the bounds on the events where the paper proves them.
Cook is applied to the globally bounded, measurable truncations. -/
theorem coordinateTwoCookTruncated_probability_and_det
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    (cook : CookDeformedSquareInput.{u, u})
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (X : IidSubgaussianFamily Omega mu iota)
    {n₁ n₂ : Nat}
    (label₁ : (Fin n₁ × Fin n₁) ↪ iota)
    (label₂ : (Fin n₂ × Fin n₂) ↪ iota)
    (profile₁ : CookProfile n₁) (profile₂ : CookProfile n₂)
    (L₁ L₂ exposureFailure : Real)
    (rawD₁ : Omega → Matrix (Fin n₁) (Fin n₁) Complex)
    (rawD₂ : Omega → Matrix (Fin n₂) (Fin n₂) Complex)
    (cross₁₂ : Omega → Matrix (Fin n₁) (Fin n₂) Complex)
    (cross₂₁ : Omega → Matrix (Fin n₂) (Fin n₁) Complex)
    (actualBottom : Omega → Matrix (Fin n₂) (Fin n₂) Complex)
    (exposure : Set Omega)
    (hsubgaussian : X.subgaussianParameter ≤ cook.subgaussianBound)
    (hprofile₁ : ∀ i j,
      cook.lowerWeight ≤ profile₁.weight i j ∧
        profile₁.weight i j ≤ cook.upperWeight)
    (hprofile₂ : ∀ i j,
      cook.lowerWeight ≤ profile₂.weight i j ∧
        profile₂.weight i j ≤ cook.upperWeight)
    (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hexposureMeas : MeasurableSet exposure)
    (hexposureProb : mu.real exposureᶜ ≤ exposureFailure)
    (hrawD₁Meas : ∀ i j,
      @StronglyMeasurable Omega Complex _
        (X.coordinateSquareConditioningSigma label₁)
        (fun omega => rawD₁ omega i j))
    (hrawD₂Meas : ∀ i j,
      @StronglyMeasurable Omega Complex _
        (X.coordinateSquareConditioningSigma label₂)
        (fun omega => rawD₂ omega i j))
    (hrawD₁Norm : ∀ omega, omega ∈ exposure →
      ‖rawD₁ omega‖ ≤ (n₁ : Real) ^ L₁)
    (hrawD₂Norm : ∀ omega, omega ∈ exposure →
      omega ∉ cookBadEvent (X.squareRestriction label₁) profile₁
        (matrixNormTruncation ((n₁ : Real) ^ L₁) rawD₁)
        (cook.beta L₁) →
      ‖rawD₂ omega‖ ≤ (n₂ : Real) ^ L₂)
    (hactualBottom : ∀ omega,
      actualBottom omega =
        profiledMatrix (X.squareRestriction label₂) profile₂ omega +
          rawD₂ omega +
        cross₂₁ omega *
          (profiledMatrix (X.squareRestriction label₁) profile₁ omega +
            rawD₁ omega)⁻¹ * cross₁₂ omega) :
    let bad := coordinateTwoCookTruncatedBadEvent cook X label₁ label₂
      profile₁ profile₂ L₁ L₂ rawD₁ rawD₂ exposure
    MeasurableSet bad ∧
      mu.real bad ≤ exposureFailure +
        (cookFailureBound (cook.cookC L₁) (cook.cookc L₁) n₁ +
          cookFailureBound (cook.cookC L₂) (cook.cookc L₂) n₂) ∧
      ∀ omega, omega ∉ bad →
        ((n₁ : Real) ^ (-cook.beta L₁)) ^ n₁ *
            ((n₂ : Real) ^ (-cook.beta L₂)) ^ n₂ ≤
          ‖(Matrix.fromBlocks
              (profiledMatrix (X.squareRestriction label₁) profile₁ omega +
                rawD₁ omega)
              (cross₁₂ omega) (cross₂₁ omega)
              (actualBottom omega)).det‖ := by
  dsimp only
  let R₁ : Real := (n₁ : Real) ^ L₁
  let R₂ : Real := (n₂ : Real) ^ L₂
  let D₁ := matrixNormTruncation R₁ rawD₁
  let D₂ := matrixNormTruncation R₂ rawD₂
  let artificialBottom := artificialSecondCookBottom X label₁ label₂
    profile₁ profile₂ D₁ D₂ cross₁₂ cross₂₁
  let cookBad := coordinateTwoCookBadEvent cook X label₁ label₂
    profile₁ profile₂ L₁ L₂ D₁ D₂
  have hR₁ : 0 ≤ R₁ := by
    dsimp [R₁]
    positivity
  have hR₂ : 0 ≤ R₂ := by
    dsimp [R₂]
    positivity
  have hD₁Meas : ∀ i j,
      @StronglyMeasurable Omega Complex _
        (X.coordinateSquareConditioningSigma label₁)
        (fun omega => D₁ omega i j) := by
    intro i j
    exact matrixNormTruncation_stronglyMeasurable_entry
      (X.coordinateSquareConditioningSigma label₁) R₁ rawD₁ hrawD₁Meas i j
  have hD₂Meas : ∀ i j,
      @StronglyMeasurable Omega Complex _
        (X.coordinateSquareConditioningSigma label₂)
        (fun omega => D₂ omega i j) := by
    intro i j
    exact matrixNormTruncation_stronglyMeasurable_entry
      (X.coordinateSquareConditioningSigma label₂) R₂ rawD₂ hrawD₂Meas i j
  have hD₁Norm : ∀ᵐ omega ∂mu, ‖D₁ omega‖ ≤ (n₁ : Real) ^ L₁ := by
    simpa [D₁, R₁] using eventually_norm_matrixNormTruncation_le
      R₁ hR₁ rawD₁ (mu := mu)
  have hD₂Norm : ∀ᵐ omega ∂mu, ‖D₂ omega‖ ≤ (n₂ : Real) ^ L₂ := by
    simpa [D₂, R₂] using eventually_norm_matrixNormTruncation_le
      R₂ hR₂ rawD₂ (mu := mu)
  have hsecond : ∀ omega,
      secondCookSchur
          (profiledMatrix (X.squareRestriction label₁) profile₁ omega +
            D₁ omega)
          (cross₁₂ omega) (cross₂₁ omega) (artificialBottom omega) =
        profiledMatrix (X.squareRestriction label₂) profile₂ omega +
          D₂ omega := by
    intro omega
    simp [artificialBottom, artificialSecondCookBottom, secondCookSchur]
  have htwo := coordinateTwoCook_probability_and_det cook mu X label₁ label₂
    profile₁ profile₂ L₁ L₂ D₁ D₂ cross₁₂ cross₂₁ artificialBottom
    hsubgaussian hprofile₁ hprofile₂ hn₁ hn₂ hL₁ hL₂
    hD₁Meas hD₂Meas hD₁Norm hD₂Norm hsecond
  have hcond₁ := cook.coordinateSquare_conditional mu X label₁ profile₁
    L₁ D₁ hsubgaussian hprofile₁ hn₁ hL₁ hD₁Meas hD₁Norm
  have hcond₂ := cook.coordinateSquare_conditional mu X label₂ profile₂
    L₂ D₂ hsubgaussian hprofile₂ hn₂ hL₂ hD₂Meas hD₂Norm
  have hcookMeas : MeasurableSet cookBad := by
    exact hcond₁.1.union hcond₂.1
  have hbadEq :
      coordinateTwoCookTruncatedBadEvent cook X label₁ label₂
        profile₁ profile₂ L₁ L₂ rawD₁ rawD₂ exposure =
      exposureᶜ ∪ cookBad := by
    rfl
  rw [hbadEq]
  constructor
  · exact hexposureMeas.compl.union hcookMeas
  constructor
  · exact (measureReal_union_le exposureᶜ cookBad).trans
      (add_le_add hexposureProb htwo.1)
  · intro omega hgood
    have hexposure : omega ∈ exposure := by
      by_contra hnot
      exact hgood (Or.inl hnot)
    have hcookGood : omega ∉ cookBad := by
      intro hbad
      exact hgood (Or.inr hbad)
    have hfirstGood : omega ∉
        cookBadEvent (X.squareRestriction label₁) profile₁ D₁
          (cook.beta L₁) := by
      intro hbad
      apply hcookGood
      exact Or.inl hbad
    have hD₁eq : D₁ omega = rawD₁ omega := by
      apply matrixNormTruncation_eq_of_norm_le
      simpa [R₁] using hrawD₁Norm omega hexposure
    have hD₂eq : D₂ omega = rawD₂ omega := by
      apply matrixNormTruncation_eq_of_norm_le
      simpa [R₂] using hrawD₂Norm omega hexposure hfirstGood
    have hbottomEq : artificialBottom omega = actualBottom omega := by
      rw [hactualBottom omega]
      simp only [artificialBottom, artificialSecondCookBottom, hD₁eq, hD₂eq]
    have hdet := htwo.2 omega hcookGood
    simpa [hD₁eq, hbottomEq] using hdet

end BernoulliSection9
