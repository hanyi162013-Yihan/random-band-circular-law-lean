import BernoulliSection9.TerminalExactConclusion
import BernoulliSection9.TerminalMaxEvent
import BernoulliSection9.TerminalComparisonNumerics

/-!
# Terminal conclusion together with the canonical maximum-coordinate event

This module joins the reverse estimate to its internally proved probability
bound.  The threshold is chosen from the subgaussian parameter and the
finite packet-coordinate count, and is enlarged to at least one so that the
reverse estimate's harmless shift condition is automatic.
-/

noncomputable section

namespace BernoulliSection9

open MeasureTheory BernoulliLinearAlgebra

namespace TerminalAssembly

/-- Canonical `E_max` cutoff for the terminal packet variables. -/
def packetCoordinateMaxThreshold
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    {mu : Measure Omega}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable w))
    (t : Real) : Real :=
  max 1 (familyCoordinateMaxThreshold X t)

theorem packetCoordinateMaxThreshold_one_le
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    {mu : Measure Omega}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable w))
    (t : Real) :
    1 <= packetCoordinateMaxThreshold X t :=
  le_max_left _ _

/-- Enlarging the canonical threshold to at least one can only improve the
maximum-coordinate event probability. -/
theorem measureReal_compl_packetCoordinateMaxEvent_le
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w] [Nonempty w]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable w))
    (t : Real) (ht : 0 <= t) :
    mu.real
        (coordinatewiseBoundedEvent X
          (packetCoordinateMaxThreshold X t))ᶜ <=
      Real.exp (-t) := by
  have hmono :
      (coordinatewiseBoundedEvent X
        (packetCoordinateMaxThreshold X t))ᶜ ⊆
      (coordinatewiseBoundedEvent X
        (familyCoordinateMaxThreshold X t))ᶜ := by
    apply Set.compl_subset_compl.mpr
    intro omega homega i
    exact (homega i).trans (le_max_right _ _)
  exact (measureReal_mono hmono).trans
    (measureReal_compl_packetCoordinatewiseBoundedEvent_threshold_le
      mu X t ht)

/-- Both internally determined finite losses are bounded by one logarithm
of a polynomial base per packet coordinate.  This is the exact numerical
form of the terminal `O(W log W)` loss, apart from the upstream two-Cook
value loss. -/
theorem packetTerminalBaseLoss_le_explicit
    (w : Type*) [Fintype w] [DecidableEq w]
    (z : Complex) (M valueLoss : Real) (hshift : 0 <= M + norm z) :
    Real.log (threeBlockConcreteComparisonConstant (W := w) z) +
        (valueLoss + terminalReverseLoss w z M) <=
      valueLoss +
        (Fintype.card (ThreeBlockIndex w) : Real) *
          (Real.log (terminalComparisonPolynomialBase w z) +
            Real.log (terminalReversePolynomialBase w z M)) := by
  have hcoefficient :=
    log_threeBlockConcreteComparisonConstant_le_card_mul_log_base w z
  have hreverse :=
    terminalReverseLoss_le_card_mul_log_polynomialBase w z M hshift
  linarith

/-- Proposition-style terminal output: the four analytic conclusions and
the exponential probability estimate for the very event used by the
reverse inequality. -/
structure PacketTerminalSmallBallResult
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    (mu : Measure Omega)
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable w))
    (baseLoss badProbability maxEventRate : Real) where
  conclusion : TerminalSmallBallConclusion mu
    (packetTerminalCoefficientNorm Q z)
    (packetTerminalValue Q z X) baseLoss badProbability
  reverse_event_eq : conclusion.reverse_event =
    coordinatewiseBoundedEvent X
      (packetCoordinateMaxThreshold X maxEventRate)
  reverse_event_compl_probability :
    mu.real conclusion.reverse_eventᶜ <= Real.exp (-maxEventRate)

/-- Assemble the terminal result at failure scale `exp (-t)`.  The sole
remaining internal premise is the concrete RRQR/CUR/two-Cook good-event
control; no reverse-event or counting certificate is requested. -/
noncomputable def packetTerminalSmallBallResult_of_goodEventControl
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w] [LinearOrder w] [Nonempty w]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable w))
    (valueLoss badProbability t : Real)
    (hvalueLoss : 0 <= valueLoss) (ht : 0 <= t)
    (control : PacketTerminalGoodEventControl mu Q z X
      valueLoss badProbability) :
    PacketTerminalSmallBallResult mu Q z X
      (Real.log (threeBlockConcreteComparisonConstant (W := w) z) +
        (valueLoss + terminalReverseLoss w z
          (packetCoordinateMaxThreshold X t)))
      badProbability t := by
  let M := packetCoordinateMaxThreshold X t
  let conclusion := packetTerminalSmallBallConclusion_canonicalReverse
    mu Q z X valueLoss badProbability M hvalueLoss
      (by
        have hM : 1 <= M := packetCoordinateMaxThreshold_one_le X t
        exact hM.trans (le_add_of_nonneg_right (norm_nonneg z)))
      control
  refine
    { conclusion := conclusion
      reverse_event_eq := ?_
      reverse_event_compl_probability := ?_ }
  · rfl
  · rw [show conclusion.reverse_event = coordinatewiseBoundedEvent X M by rfl]
    exact measureReal_compl_packetCoordinateMaxEvent_le mu X t ht

end TerminalAssembly

end BernoulliSection9
