import BernoulliSection9.TerminalReverse
import BernoulliSection9.TerminalCoefficientBounds

/-!
# Paper-quantitative terminal conclusion assembly

This module installs the valid-matching reverse estimate in the terminal
small-ball package.  The only remaining internal input is the good-event
value lower bound produced by the RRQR/CUR/two-Cook reduction; coefficient
comparison, measurability, capped-loss integration, the zero event, the
reverse event, and Parseval are all internal.
-/

noncomputable section

namespace BernoulliSection9

open MeasureTheory

namespace TerminalAssembly

/-- Proposition 7.3 assembled from the good-event determinant control, with
the explicit `(N^2+1)^N`, `N=3W`, valid-matching count in the reverse
factor.  Its logarithm is `O(W log W)`; no mask or matching certificate is
an argument. -/
noncomputable def packetTerminalSmallBallConclusion_indexPolynomial
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w] [LinearOrder w]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (valueLoss badProbability M : Real)
    (hvalueLoss : 0 <= valueLoss)
    (hshift : 1 <= M + norm z)
    (control : PacketTerminalGoodEventControl mu Q z X
      valueLoss badProbability)
    (hreverseFactor :
      (validMatchingIndexPolynomialCount w : Real) *
        BernoulliLinearAlgebra.threeBlockTranslationFactor (w := w) z *
        (M + norm z) ^
          Fintype.card (BernoulliLinearAlgebra.ThreeBlockIndex w) <=
        Real.exp
          (Real.log
            (BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
              (W := w) z) + valueLoss)) :
    TerminalSmallBallConclusion mu (packetTerminalCoefficientNorm Q z)
      (packetTerminalValue Q z X)
      (Real.log (BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
        (W := w) z) + valueLoss)
      badProbability := by
  apply packetTerminalSmallBallConclusion_of_goodEventControl
    mu Q z X valueLoss badProbability hvalueLoss control
    (coordinatewiseBoundedEvent X M)
  exact packetTerminal_reverse_indexPolynomial Q z X M
    (Real.log
      (BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
        (W := w) z) + valueLoss)
    hshift
    (add_nonneg
      (Real.log_nonneg
        (BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket_concreteComparison
          (W := w) z).one_le)
      hvalueLoss)
    hreverseFactor

/-- The literal terminal coefficient norm, in the notation of the assembly
module, satisfies the exact RRQR-threshold product comparison.  This is the
coefficient-side bridge of (9.41)--(9.42), with no pivot, mask, or elimination
certificate in its signature. -/
theorem packetTerminalCoefficientNorm_product_bounds
    {w : Type*} [Fintype w] [DecidableEq w] [LinearOrder w]
    (z : Complex) (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (r : Nat) (tau : Real) (htau : 1 <= tau)
    (hlarge : ∀ i : Fin
        (Module.finrank Complex
          (EuclideanSpace Complex (PacketOuter w))),
      (i : Nat) < r -> tau < (Matrix.toEuclideanLin Q).singularValues i)
    (hsmall : ∀ i : Fin
        (Module.finrank Complex
          (EuclideanSpace Complex (PacketOuter w))),
      r <= (i : Nat) -> (Matrix.toEuclideanLin Q).singularValues i <= tau) :
    let K := BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
      (W := w) z
    let productScale := largeSingularProduct (Matrix.toEuclideanLin Q) r
    K⁻¹ * productScale <= packetTerminalCoefficientNorm Q z ∧
      packetTerminalCoefficientNorm Q z <=
        K * ((2 * tau) ^ Fintype.card (PacketOuter w) * productScale) := by
  simpa [packetTerminalCoefficientNorm] using
    (threeBlockTerminalCoefficient_product_bounds z Q r tau htau
      hlarge hsmall)

end TerminalAssembly

end BernoulliSection9
