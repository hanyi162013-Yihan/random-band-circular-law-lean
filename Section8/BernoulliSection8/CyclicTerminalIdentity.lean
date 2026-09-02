import BernoulliSection8.PhysicalFock
import BernoulliSection10.PhysicalBoundaryExpression

/-! # The terminal cut preserves the actual polynomial determinant -/

open scoped Matrix

noncomputable section

namespace BernoulliSection8

open BernoulliSection10 BernoulliLinearAlgebra

local instance cyclicTerminalSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  BernoulliLinearAlgebra.clearedStepCompoundSumLinearOrder

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem cyclicFockValue_terminalPacket
    (W s : ℕ) (z : ℂ) (outside : IntervalRows W s) (packet : IntervalRows W 3)
    (hB : ∀ j, IsUnit (intervalSiteBlocks z outside j).B.det) :
    cyclicFockValue W s z (intervalConcat W s 3 (outside, packet)) =
      intervalClearingFactor W s z outside *
        physicalBoundaryExpression W 3 z packet (intervalTransferProduct W s z outside) := by
  unfold cyclicFockValue
  rw [physicalIntervalSteps_concat]
  have hp (a : Finset (Fin W ⊕ Fin W)) :
      polynomialClearedCompoundProduct a.card (physicalIntervalSteps W s z outside) =
        intervalClearingFactor W s z outside •
          compound a.card (intervalTransferProduct W s z outside) := by
    exact (polynomialClearedCompoundProduct_physicalIntervalSteps W s z outside
      (exteriorDegreeOfFinset W a)).trans
      (intervalClearedProduct_eq_clearing_smul_compound W s z outside hB
        (exteriorDegreeOfFinset W a))
  unfold polynomialClearedSignedCompoundTrace physicalBoundaryExpression polynomialClearedBoundaryTrace
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [polynomialClearedCompoundProduct_append, hp, Matrix.mul_smul,
    Matrix.smul_apply, smul_eq_mul]
  ring

end BernoulliSection8
