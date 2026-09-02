import BernoulliSection9.CoordinateConditionalCook
import BernoulliSection9.TwoCookDeterminant

/-!
# Two conditional Cook estimates inside one global iid family

This is the global-coordinate analogue of `twoBalancedCook_probability_and_det`.
Each Cook square is selected by an injection into the complete packet family,
so its conditioning sigma-field contains every coordinate outside that square.
The result gives the union probability and the determinant lower bound needed
for the literal terminal Schur complement.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory

universe u v

/-- The union of the two Cook failures for globally selected squares. -/
def coordinateTwoCookBadEvent
    {Omega iota : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [Fintype iota] [DecidableEq iota]
    {n₁ n₂ : Nat}
    (cook : CookDeformedSquareInput)
    (X : IidSubgaussianFamily Omega mu iota)
    (label₁ : (Fin n₁ × Fin n₁) ↪ iota)
    (label₂ : (Fin n₂ × Fin n₂) ↪ iota)
    (profile₁ : CookProfile n₁) (profile₂ : CookProfile n₂)
    (L₁ L₂ : Real)
    (D₁ : Omega → Matrix (Fin n₁) (Fin n₁) Complex)
    (D₂ : Omega → Matrix (Fin n₂) (Fin n₂) Complex) : Set Omega :=
  cookBadEvent (X.squareRestriction label₁) profile₁ D₁ (cook.beta L₁) ∪
    cookBadEvent (X.squareRestriction label₂) profile₂ D₂ (cook.beta L₂)

/-- Two conditional Cook calls, with both conditionings taken in the global
coordinate family, imply a determinant lower bound for the full two-by-two
block matrix outside the union of their failure events. -/
theorem coordinateTwoCook_probability_and_det
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    (cook : CookDeformedSquareInput.{u, u})
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (X : IidSubgaussianFamily Omega mu iota)
    {n₁ n₂ : Nat}
    (label₁ : (Fin n₁ × Fin n₁) ↪ iota)
    (label₂ : (Fin n₂ × Fin n₂) ↪ iota)
    (profile₁ : CookProfile n₁) (profile₂ : CookProfile n₂)
    (L₁ L₂ : Real)
    (D₁ : Omega → Matrix (Fin n₁) (Fin n₁) Complex)
    (D₂ : Omega → Matrix (Fin n₂) (Fin n₂) Complex)
    (cross₁₂ : Omega → Matrix (Fin n₁) (Fin n₂) Complex)
    (cross₂₁ : Omega → Matrix (Fin n₂) (Fin n₁) Complex)
    (bottom : Omega → Matrix (Fin n₂) (Fin n₂) Complex)
    (hsubgaussian : X.subgaussianParameter ≤ cook.subgaussianBound)
    (hprofile₁ : ∀ i j,
      cook.lowerWeight ≤ profile₁.weight i j ∧
        profile₁.weight i j ≤ cook.upperWeight)
    (hprofile₂ : ∀ i j,
      cook.lowerWeight ≤ profile₂.weight i j ∧
        profile₂.weight i j ≤ cook.upperWeight)
    (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hD₁meas : ∀ i j,
      @StronglyMeasurable Omega Complex _
        (X.coordinateSquareConditioningSigma label₁)
        (fun omega => D₁ omega i j))
    (hD₂meas : ∀ i j,
      @StronglyMeasurable Omega Complex _
        (X.coordinateSquareConditioningSigma label₂)
        (fun omega => D₂ omega i j))
    (hD₁norm : ∀ᵐ omega ∂mu, ‖D₁ omega‖ ≤ (n₁ : Real) ^ L₁)
    (hD₂norm : ∀ᵐ omega ∂mu, ‖D₂ omega‖ ≤ (n₂ : Real) ^ L₂)
    (hsecond : ∀ omega,
      secondCookSchur
          (profiledMatrix (X.squareRestriction label₁) profile₁ omega +
            D₁ omega)
          (cross₁₂ omega) (cross₂₁ omega) (bottom omega) =
        profiledMatrix (X.squareRestriction label₂) profile₂ omega +
          D₂ omega) :
    let bad := coordinateTwoCookBadEvent cook X label₁ label₂
      profile₁ profile₂ L₁ L₂ D₁ D₂
    mu.real bad ≤
        cookFailureBound (cook.cookC L₁) (cook.cookc L₁) n₁ +
          cookFailureBound (cook.cookC L₂) (cook.cookc L₂) n₂ ∧
      ∀ omega, omega ∉ bad →
        ((n₁ : Real) ^ (-cook.beta L₁)) ^ n₁ *
            ((n₂ : Real) ^ (-cook.beta L₂)) ^ n₂ ≤
          ‖(Matrix.fromBlocks
              (profiledMatrix (X.squareRestriction label₁) profile₁ omega +
                D₁ omega)
              (cross₁₂ omega) (cross₂₁ omega) (bottom omega)).det‖ := by
  dsimp only
  let bad₁ := cookBadEvent (X.squareRestriction label₁) profile₁ D₁
    (cook.beta L₁)
  let bad₂ := cookBadEvent (X.squareRestriction label₂) profile₂ D₂
    (cook.beta L₂)
  have hcond₁ := cook.coordinateSquare_conditional mu X label₁ profile₁
    L₁ D₁ hsubgaussian hprofile₁ hn₁ hL₁ hD₁meas hD₁norm
  have hcond₂ := cook.coordinateSquare_conditional mu X label₂ profile₂
    L₂ D₂ hsubgaussian hprofile₂ hn₂ hL₂ hD₂meas hD₂norm
  have hprob₁ : mu.real bad₁ ≤
      cookFailureBound (cook.cookC L₁) (cook.cookc L₁) n₁ := by
    exact cookBadEvent_probability_le_of_conditional mu
      (X.squareRestriction label₁) profile₁ D₁ (cook.beta L₁)
      (cookFailureBound (cook.cookC L₁) (cook.cookc L₁) n₁)
      (X.coordinateSquareConditioningSigma label₁)
      (X.coordinateSquareConditioningSigma_le label₁) hcond₁
  have hprob₂ : mu.real bad₂ ≤
      cookFailureBound (cook.cookC L₂) (cook.cookc L₂) n₂ := by
    exact cookBadEvent_probability_le_of_conditional mu
      (X.squareRestriction label₂) profile₂ D₂ (cook.beta L₂)
      (cookFailureBound (cook.cookC L₂) (cook.cookc L₂) n₂)
      (X.coordinateSquareConditioningSigma label₂)
      (X.coordinateSquareConditioningSigma_le label₂) hcond₂
  constructor
  · simpa [coordinateTwoCookBadEvent, bad₁, bad₂] using
      probability_union_le_sum mu bad₁ bad₂ _ _ hprob₁ hprob₂
  · intro omega hgood
    have hgood₁ : omega ∉ bad₁ := by
      intro homega
      apply hgood
      simpa [coordinateTwoCookBadEvent, bad₁, bad₂] using Or.inl homega
    have hgood₂ : omega ∉ bad₂ := by
      intro homega
      apply hgood
      simpa [coordinateTwoCookBadEvent, bad₁, bad₂] using Or.inr homega
    let epsilon₁ : Real := (n₁ : Real) ^ (-cook.beta L₁)
    let epsilon₂ : Real := (n₂ : Real) ^ (-cook.beta L₂)
    have hepsilon₁ : 0 < epsilon₁ := by
      dsimp [epsilon₁]
      positivity
    have hepsilon₂ : 0 ≤ epsilon₂ := by
      dsimp [epsilon₂]
      positivity
    have hmin₁ : epsilon₁ ≤ matrixSMin
        (profiledMatrix (X.squareRestriction label₁) profile₁ omega +
          D₁ omega) := by
      have hnle : ¬matrixSMin
          (profiledMatrix (X.squareRestriction label₁) profile₁ omega +
            D₁ omega) ≤ epsilon₁ := hgood₁
      exact (lt_of_not_ge hnle).le
    have hmin₂ : epsilon₂ ≤ matrixSMin
        (secondCookSchur
          (profiledMatrix (X.squareRestriction label₁) profile₁ omega +
            D₁ omega)
          (cross₁₂ omega) (cross₂₁ omega) (bottom omega)) := by
      rw [hsecond omega]
      have hnle : ¬matrixSMin
          (profiledMatrix (X.squareRestriction label₂) profile₂ omega +
            D₂ omega) ≤ epsilon₂ := hgood₂
      exact (lt_of_not_ge hnle).le
    exact twoCook_det_lower
      (profiledMatrix (X.squareRestriction label₁) profile₁ omega + D₁ omega)
      (cross₁₂ omega) (cross₂₁ omega) (bottom omega)
      (lt_of_lt_of_le Nat.zero_lt_two hn₁)
      (lt_of_lt_of_le Nat.zero_lt_two hn₂)
      hepsilon₁ hepsilon₂ hmin₁ hmin₂

end BernoulliSection9
