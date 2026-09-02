import BernoulliSection9.TerminalAssembly
import BernoulliSection9.TerminalNumerics

/-!
# Terminal conclusion with an internally determined reverse loss

The good-event determinant estimate naturally supplies the value loss.  The
valid-matching argument supplies a second, completely explicit loss for the
reverse estimate.  This file enlarges the good-event loss by that nonnegative
quantity, so the four conclusions can be packaged without a caller-provided
counting or reverse-factor inequality.
-/

noncomputable section

namespace BernoulliSection9

open MeasureTheory

namespace TerminalAssembly

/-- A good-event lower bound remains valid after adding a nonnegative amount
to its logarithmic loss. -/
noncomputable def PacketTerminalGoodEventControl.addLoss
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    {mu : Measure Omega}
    {Q : Matrix (PacketOuter w) (PacketOuter w) Complex}
    {z : Complex}
    {X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w)}
    {valueLoss badProbability : Real}
    (control : PacketTerminalGoodEventControl mu Q z X
      valueLoss badProbability)
    (extraLoss : Real) (hextraLoss : 0 <= extraLoss) :
    PacketTerminalGoodEventControl mu Q z X
      (valueLoss + extraLoss) badProbability := by
  refine
    { bad := control.bad
      measurable_bad := control.measurable_bad
      probability_bad := control.probability_bad
      value_lower := ?_ }
  intro omega homega
  have hexp : Real.exp (-(valueLoss + extraLoss)) <=
      Real.exp (-valueLoss) := by
    apply Real.exp_le_exp.mpr
    linarith
  exact (mul_le_mul_of_nonneg_right hexp
      (BernoulliLinearAlgebra.gramVolume_nonneg Q)).trans
    (control.value_lower omega homega)

/-- The terminal small-ball package with the sharp-support reverse estimate
and its finite loss chosen internally.  Its base loss is
`log K + valueLoss + terminalReverseLoss`; the last term has the explicit
`O(W log W)` bound proved in `TerminalNumerics`. -/
noncomputable def packetTerminalSmallBallConclusion_canonicalReverse
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
      valueLoss badProbability) :
    TerminalSmallBallConclusion mu (packetTerminalCoefficientNorm Q z)
      (packetTerminalValue Q z X)
      (Real.log (BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
          (W := w) z) +
        (valueLoss + terminalReverseLoss w z M))
      badProbability := by
  let reverseLoss := terminalReverseLoss w z M
  have hreverseLoss : 0 <= reverseLoss := by
    exact terminalReverseLoss_nonneg w z M
  let enlargedControl : PacketTerminalGoodEventControl mu Q z X
      (valueLoss + reverseLoss) badProbability :=
    control.addLoss reverseLoss hreverseLoss
  apply packetTerminalSmallBallConclusion_of_goodEventControl
    mu Q z X (valueLoss + reverseLoss) badProbability
    (add_nonneg hvalueLoss hreverseLoss) enlargedControl
    (coordinatewiseBoundedEvent X M)
  intro omega homega
  have hreverse := packetTerminal_reverse Q z X M hshift omega homega
  have hlog : 0 <=
      Real.log (BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
        (W := w) z) :=
    Real.log_nonneg
      (BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket_concreteComparison
        (W := w) z).one_le
  exact hreverse.trans (by
    dsimp [reverseLoss]
    linarith)

end TerminalAssembly

end BernoulliSection9
