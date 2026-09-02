import BernoulliSection9.ConditionalCook
import BernoulliSection9.TwoCookDeterminant

/-!
# Two conditional Cook estimates and the residual determinant

This module joins (9.30), (9.32), and (9.35).  The square locations and their
independence are canonical consequences of the literal residual mask.  The
only algebraic hypotheses below identify the two deformations produced by
the preceding CUR/Schur calculation.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory

universe u

/-- The two canonical Cook failures. -/
def twoBalancedCookBadEvent
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {W a b c e : Nat}
    (cook : CookDeformedSquareInput)
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (profile1 : CookProfile (balancedSquareSize W a b c))
    (profile2 : CookProfile
      (W + a + b - balancedSquareSize W a b c))
    (L1 L2 : Real)
    (deform1 : Omega -> Matrix (Fin (balancedSquareSize W a b c))
      (Fin (balancedSquareSize W a b c)) Complex)
    (deform2 : Omega ->
      Matrix (Fin (W + a + b - balancedSquareSize W a b c))
        (Fin (W + a + b - balancedSquareSize W a b c)) Complex) :
    Set Omega :=
  cookBadEvent (S.firstBalancedCookSquare ha hc hs hsW)
      profile1 deform1 (cook.beta L1) ∪
    cookBadEvent (S.secondBalancedCookSquare ha hc hs hsW)
      profile2 deform2 (cook.beta L2)

/-- Two conditional Cook applications give both the union probability and,
off that union, the determinant lower bound for the full residual block.

`hfirst` and `hsecond` are literal matrix identities: the first diagonal
block is the first profiled square plus its deformation, and the second
Schur complement is the second profiled square plus its deformation.  They
are proved from `TerminalCUR.F` in the concrete terminal assembly; no
independence or RRQR certificate occurs here. -/
theorem twoBalancedCook_probability_and_det
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    (cook : CookDeformedSquareInput.{u, u})
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (profile1 : CookProfile (balancedSquareSize W a b c))
    (profile2 : CookProfile
      (W + a + b - balancedSquareSize W a b c))
    (L1 L2 : Real)
    (deform1 : Omega -> Matrix (Fin (balancedSquareSize W a b c))
      (Fin (balancedSquareSize W a b c)) Complex)
    (deform2 : Omega ->
      Matrix (Fin (W + a + b - balancedSquareSize W a b c))
        (Fin (W + a + b - balancedSquareSize W a b c)) Complex)
    (cross12 : Omega ->
      Matrix (Fin (balancedSquareSize W a b c))
        (Fin (W + a + b - balancedSquareSize W a b c)) Complex)
    (cross21 : Omega ->
      Matrix (Fin (W + a + b - balancedSquareSize W a b c))
        (Fin (balancedSquareSize W a b c)) Complex)
    (bottom : Omega ->
      Matrix (Fin (W + a + b - balancedSquareSize W a b c))
        (Fin (W + a + b - balancedSquareSize W a b c)) Complex)
    (hsubgaussian : S.subgaussianParameter <= cook.subgaussianBound)
    (hprofile1 : forall i j,
      cook.lowerWeight <= profile1.weight i j ∧
        profile1.weight i j <= cook.upperWeight)
    (hprofile2 : forall i j,
      cook.lowerWeight <= profile2.weight i j ∧
        profile2.weight i j <= cook.upperWeight)
    (hn1 : 2 <= balancedSquareSize W a b c)
    (hn2 : 2 <= W + a + b - balancedSquareSize W a b c)
    (hL1 : 0 <= L1) (hL2 : 0 <= L2)
    (hdeform1Meas : forall i j,
      @StronglyMeasurable Omega Complex _
        (S.firstBalancedConditioningSigma ha hc hs hsW)
        (fun omega => deform1 omega i j))
    (hdeform2Meas : forall i j,
      @StronglyMeasurable Omega Complex _
        (S.secondBalancedConditioningSigma ha hc hs hsW)
        (fun omega => deform2 omega i j))
    (hdeform1Norm : ∀ᵐ omega ∂mu,
      ‖deform1 omega‖ <= (balancedSquareSize W a b c : Real) ^ L1)
    (hdeform2Norm : ∀ᵐ omega ∂mu,
      ‖deform2 omega‖ <=
        ((W + a + b - balancedSquareSize W a b c : Nat) : Real) ^ L2)
    (hsecond : forall omega,
      secondCookSchur
          (profiledMatrix (S.firstBalancedCookSquare ha hc hs hsW)
            profile1 omega + deform1 omega)
          (cross12 omega) (cross21 omega) (bottom omega) =
        profiledMatrix (S.secondBalancedCookSquare ha hc hs hsW)
          profile2 omega + deform2 omega) :
    let bad := twoBalancedCookBadEvent cook S ha hc hs hsW
      profile1 profile2 L1 L2 deform1 deform2
    mu.real bad <=
        cookFailureBound (cook.cookC L1) (cook.cookc L1)
            (balancedSquareSize W a b c) +
          cookFailureBound (cook.cookC L2) (cook.cookc L2)
            (W + a + b - balancedSquareSize W a b c) ∧
      ∀ omega, omega ∉ bad →
        ((balancedSquareSize W a b c : Real) ^ (-cook.beta L1)) ^
              balancedSquareSize W a b c *
            (((W + a + b - balancedSquareSize W a b c : Nat) : Real) ^
              (-cook.beta L2)) ^
                (W + a + b - balancedSquareSize W a b c) <=
          ‖(Matrix.fromBlocks
              (profiledMatrix
                  (S.firstBalancedCookSquare ha hc hs hsW) profile1 omega +
                deform1 omega)
              (cross12 omega) (cross21 omega) (bottom omega)).det‖ := by
  dsimp only
  let bad1 := cookBadEvent
    (S.firstBalancedCookSquare ha hc hs hsW) profile1 deform1
      (cook.beta L1)
  let bad2 := cookBadEvent
    (S.secondBalancedCookSquare ha hc hs hsW) profile2 deform2
      (cook.beta L2)
  have hcond1 := cook.firstBalanced_conditional mu S ha hc hs hsW
    profile1 L1 deform1 hsubgaussian hprofile1 hn1 hL1 hdeform1Meas hdeform1Norm
  have hcond2 := cook.secondBalanced_conditional mu S ha hc hs hsW
    profile2 L2 deform2 hsubgaussian hprofile2 hn2 hL2 hdeform2Meas hdeform2Norm
  have hprob1 : mu.real bad1 <=
      cookFailureBound (cook.cookC L1) (cook.cookc L1)
        (balancedSquareSize W a b c) := by
    exact cookBadEvent_probability_le_of_conditional mu
      (S.firstBalancedCookSquare ha hc hs hsW) profile1 deform1
      (cook.beta L1)
      (cookFailureBound (cook.cookC L1) (cook.cookc L1)
        (balancedSquareSize W a b c))
      (S.firstBalancedConditioningSigma ha hc hs hsW)
      (S.firstBalancedConditioningSigma_le ha hc hs hsW) hcond1
  have hprob2 : mu.real bad2 <=
      cookFailureBound (cook.cookC L2) (cook.cookc L2)
        (W + a + b - balancedSquareSize W a b c) := by
    exact cookBadEvent_probability_le_of_conditional mu
      (S.secondBalancedCookSquare ha hc hs hsW) profile2 deform2
      (cook.beta L2)
      (cookFailureBound (cook.cookC L2) (cook.cookc L2)
        (W + a + b - balancedSquareSize W a b c))
      (S.secondBalancedConditioningSigma ha hc hs hsW)
      (S.secondBalancedConditioningSigma_le ha hc hs hsW) hcond2
  constructor
  · simpa [twoBalancedCookBadEvent, bad1, bad2] using
      probability_union_le_sum mu bad1 bad2 _ _ hprob1 hprob2
  · intro omega hgood
    have hgood1 : omega ∉ bad1 := by
      intro homega
      apply hgood
      simpa [twoBalancedCookBadEvent, bad1, bad2] using Or.inl homega
    have hgood2 : omega ∉ bad2 := by
      intro homega
      apply hgood
      simpa [twoBalancedCookBadEvent, bad1, bad2] using Or.inr homega
    let epsilon1 : Real :=
      (balancedSquareSize W a b c : Real) ^ (-cook.beta L1)
    let epsilon2 : Real :=
      ((W + a + b - balancedSquareSize W a b c : Nat) : Real) ^
        (-cook.beta L2)
    have hepsilon1 : 0 < epsilon1 := by
      dsimp [epsilon1]
      positivity
    have hepsilon2 : 0 <= epsilon2 := by
      dsimp [epsilon2]
      positivity
    have hmin1 : epsilon1 <= matrixSMin
        (profiledMatrix (S.firstBalancedCookSquare ha hc hs hsW)
          profile1 omega + deform1 omega) := by
      have hnle : ¬matrixSMin
          (profiledMatrix (S.firstBalancedCookSquare ha hc hs hsW)
            profile1 omega + deform1 omega) <= epsilon1 := by
        exact hgood1
      exact (lt_of_not_ge hnle).le
    have hmin2 : epsilon2 <= matrixSMin
        (secondCookSchur
          (profiledMatrix (S.firstBalancedCookSquare ha hc hs hsW)
            profile1 omega + deform1 omega)
          (cross12 omega) (cross21 omega) (bottom omega)) := by
      rw [hsecond omega]
      have hnle : ¬matrixSMin
          (profiledMatrix (S.secondBalancedCookSquare ha hc hs hsW)
            profile2 omega + deform2 omega) <= epsilon2 := by
        exact hgood2
      exact (lt_of_not_ge hnle).le
    exact twoCook_det_lower
      (profiledMatrix (S.firstBalancedCookSquare ha hc hs hsW)
        profile1 omega + deform1 omega)
      (cross12 omega) (cross21 omega) (bottom omega)
      (lt_of_lt_of_le Nat.zero_lt_two hn1)
      (lt_of_lt_of_le Nat.zero_lt_two hn2)
      hepsilon1 hepsilon2 hmin1 hmin2

end BernoulliSection9
