import BernoulliSection9.TwoSquareRandomness
import BernoulliSection9.TerminalSmallBall

/-!
# The two canonical conditional Cook applications

The fresh and conditioning sigma-fields in these wrappers are constructed
from the literal two-square coordinate partition.  Thus the independence and
fresh-atom measurability hypotheses of the external Cook theorem are
discharged internally.  Only the deformation's measurability and polynomial
norm bound remain to be proved by the terminal CUR construction.
-/

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory

universe u

/-- Integrate an explicit conditional Cook conclusion.  The measurability
component is part of the visible Cook input, so no hidden event-regularity
assumption is used here. -/
theorem cookBadEvent_probability_le_of_conditional
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {n : Nat} (square : IidSubgaussianSquare Omega mu n)
    (profile : CookProfile n) (D : Omega -> Matrix (Fin n) (Fin n) Complex)
    (beta p : Real) (m : MeasurableSpace Omega) (hm : m <= mOmega)
    (hconditional :
      @MeasurableSet Omega mOmega
          (@cookBadEvent Omega mOmega mu n square profile D beta) ∧
        ∀ᵐ omega ∂mu,
          @condExp Omega Real m (m₀ := mOmega) _ _ mu
            ((@cookBadEvent Omega mOmega mu n square profile D beta).indicator
              (fun _ => (1 : Real))) omega <= p) :
    mu.real (@cookBadEvent Omega mOmega mu n square profile D beta) <= p :=
  @probability_le_of_condExp_indicator_le Omega mOmega mu _ m hm
    (@cookBadEvent Omega mOmega mu n square profile D beta)
    p hconditional.1 hconditional.2

/-- First conditional Cook application, on the balanced first residual
square. -/
theorem CookDeformedSquareInput.firstBalanced_conditional
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    (cook : CookDeformedSquareInput.{u, u}) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (profile : CookProfile (balancedSquareSize W a b c))
    (L : Real)
    (D : Omega -> Matrix (Fin (balancedSquareSize W a b c))
      (Fin (balancedSquareSize W a b c)) Complex)
    (hsubgaussian : S.subgaussianParameter <= cook.subgaussianBound)
    (hprofile : forall i j,
      cook.lowerWeight <= profile.weight i j ∧
        profile.weight i j <= cook.upperWeight)
    (hn : 2 <= balancedSquareSize W a b c) (hL : 0 <= L)
    (hDmeas : forall i j,
      @StronglyMeasurable Omega Complex _
        (S.firstBalancedConditioningSigma ha hc hs hsW)
        (fun omega => D omega i j))
    (hDnorm : ∀ᵐ omega ∂mu,
      ‖D omega‖ <= (balancedSquareSize W a b c : Real) ^ L) :
    MeasurableSet (cookBadEvent
        (S.firstBalancedCookSquare ha hc hs hsW) profile D
        (cook.beta L)) ∧
      ∀ᵐ omega ∂mu,
        @condExp Omega Real
            (S.firstBalancedConditioningSigma ha hc hs hsW)
            (m₀ := mOmega) _ _ mu
            ((cookBadEvent
                (S.firstBalancedCookSquare ha hc hs hsW) profile D
                (cook.beta L)).indicator (fun _ => (1 : Real))) omega <=
          cookFailureBound (cook.cookC L) (cook.cookc L)
            (balancedSquareSize W a b c) := by
  exact cook.conditional mu
    (S.firstBalancedCookSquare ha hc hs hsW) profile L
    (S.firstBalancedFreshSigma ha hc hs hsW)
    (S.firstBalancedConditioningSigma ha hc hs hsW)
    (S.firstBalancedFreshSigma_le ha hc hs hsW)
    (S.firstBalancedConditioningSigma_le ha hc hs hsW)
    D hsubgaussian hprofile hn hL
    (S.firstBalancedCook_atom_measurable ha hc hs hsW)
    hDmeas
    (S.firstBalancedFresh_indep_conditioning ha hc hs hsW)
    hDnorm

/-- Second conditional Cook application, on the complementary complete
residual square. -/
theorem CookDeformedSquareInput.secondBalanced_conditional
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    (cook : CookDeformedSquareInput.{u, u}) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (profile : CookProfile
      (W + a + b - balancedSquareSize W a b c))
    (L : Real)
    (D : Omega ->
      Matrix (Fin (W + a + b - balancedSquareSize W a b c))
        (Fin (W + a + b - balancedSquareSize W a b c)) Complex)
    (hsubgaussian : S.subgaussianParameter <= cook.subgaussianBound)
    (hprofile : forall i j,
      cook.lowerWeight <= profile.weight i j ∧
        profile.weight i j <= cook.upperWeight)
    (hn : 2 <= W + a + b - balancedSquareSize W a b c)
    (hL : 0 <= L)
    (hDmeas : forall i j,
      @StronglyMeasurable Omega Complex _
        (S.secondBalancedConditioningSigma ha hc hs hsW)
        (fun omega => D omega i j))
    (hDnorm : ∀ᵐ omega ∂mu,
      ‖D omega‖ <=
        ((W + a + b - balancedSquareSize W a b c : Nat) : Real) ^ L) :
    MeasurableSet (cookBadEvent
        (S.secondBalancedCookSquare ha hc hs hsW) profile D
        (cook.beta L)) ∧
      ∀ᵐ omega ∂mu,
        @condExp Omega Real
            (S.secondBalancedConditioningSigma ha hc hs hsW)
            (m₀ := mOmega) _ _ mu
            ((cookBadEvent
                (S.secondBalancedCookSquare ha hc hs hsW) profile D
                (cook.beta L)).indicator (fun _ => (1 : Real))) omega <=
          cookFailureBound (cook.cookC L) (cook.cookc L)
            (W + a + b - balancedSquareSize W a b c) := by
  exact cook.conditional mu
    (S.secondBalancedCookSquare ha hc hs hsW) profile L
    (S.secondBalancedFreshSigma ha hc hs hsW)
    (S.secondBalancedConditioningSigma ha hc hs hsW)
    (S.secondBalancedFreshSigma_le ha hc hs hsW)
    (S.secondBalancedConditioningSigma_le ha hc hs hsW)
    D hsubgaussian hprofile hn hL
    (S.secondBalancedCook_atom_measurable ha hc hs hsW)
    hDmeas
    (S.secondBalancedFresh_indep_conditioning ha hc hs hsW)
    hDnorm

end BernoulliSection9
