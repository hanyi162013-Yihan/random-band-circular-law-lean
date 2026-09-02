import BernoulliSection10.CyclicPhysicalModel
import BernoulliSection10.IntervalConcatenation
import BernoulliSection10.IntervalTransfer
import BernoulliSection10.PacketPhysicalIdentification

/-! # Literal interval boundary expressions and packet identification -/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliSection10

open BernoulliLinearAlgebra Matrix Set Set.powersetCard

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance physicalBoundarySumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  BernoulliLinearAlgebra.clearedStepCompoundSumLinearOrder

def physicalBoundaryExpression (W s : ℕ) (z : ℂ) (x : IntervalRows W s)
    (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) : ℂ :=
  polynomialClearedBoundaryTrace (physicalIntervalSteps W s z x) R

def exteriorDegreeOfFinset (W : ℕ) (a : Finset (Fin W ⊕ Fin W)) : Fin (2 * W + 1) :=
  ⟨a.card, by
    have h := Finset.card_le_univ a
    simp only [Fintype.card_sum, Fintype.card_fin] at h
    omega⟩

theorem continuous_physicalBoundaryExpression (W s : ℕ) (z : ℂ)
    (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    Continuous (fun x : IntervalRows W s => physicalBoundaryExpression W s z x R) := by
  unfold physicalBoundaryExpression polynomialClearedBoundaryTrace
  apply continuous_finset_sum
  intro a _
  have hp : Continuous (fun x : IntervalRows W s =>
      polynomialClearedCompoundProduct a.card (physicalIntervalSteps W s z x)) := by
    have h := continuous_intervalClearedProduct W s z (exteriorDegreeOfFinset W a)
    simpa only [← polynomialClearedCompoundProduct_physicalIntervalSteps,
      exteriorDegreeOfFinset] using h
  have hm : Continuous (fun x : IntervalRows W s =>
      polynomialClearedCompoundProduct a.card (physicalIntervalSteps W s z x) *
        compound a.card R) := hp.matrix_mul continuous_const
  exact continuous_const.mul ((continuous_apply (ofCard rfl)).comp
    ((continuous_apply (ofCard rfl)).comp hm))

theorem physicalIntervalSteps_packetPhysicalRows
    (W : ℕ) (z : ℂ) (p : EndpointBlockPair W × PacketAtomRows W) :
    physicalIntervalSteps W 3 z (packetPhysicalRows W p) =
      boundaryCompanionSteps
        (threeBlockBL (packetAtomAssignment W p.2))
        (threeBlockBC (packetAtomAssignment W p.2))
        (normalizedBlockMatrix W p.1.2)
        (threeBlockAL (packetAtomAssignment W p.2) - z • 1)
        (threeBlockAC (packetAtomAssignment W p.2) - z • 1)
        (threeBlockAR (packetAtomAssignment W p.2) - z • 1)
        (normalizedBlockMatrix W p.1.1)
        (threeBlockCC (packetAtomAssignment W p.2))
        (threeBlockCR (packetAtomAssignment W p.2)) := by
  simp [physicalIntervalSteps, List.ofFn_succ, intervalSiteBlocks_packetPhysicalRows,
    boundaryCompanionSteps]

theorem packetBoundaryEval_eq_physical
    (W : ℕ) (z : ℂ) (ep : EndpointBlockPair W) (x : PacketAtomRows W)
    (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    packetBoundaryEval W z (normalizedBlockMatrix W ep.1)
      (normalizedBlockMatrix W ep.2) R x =
        physicalBoundaryExpression W 3 z (packetPhysicalRows W (ep, x)) R := by
  rw [packetBoundaryEval, eval_packetBoundaryPolynomial_eq_packetLiteralK_det,
    packetLiteralK_eq_concreteKTheta]
  unfold physicalBoundaryExpression
  rw [physicalIntervalSteps_packetPhysicalRows]
  have h := polynomialClearedBoundaryTrace_boundaryCompanionSteps_eq_concreteKTheta_det
    (threeBlockAL (packetAtomAssignment W x) - z • 1)
    (threeBlockBL (packetAtomAssignment W x))
    (threeBlockCC (packetAtomAssignment W x))
    (threeBlockAC (packetAtomAssignment W x) - z • 1)
    (threeBlockBC (packetAtomAssignment W x))
    (threeBlockCR (packetAtomAssignment W x))
    (threeBlockAR (packetAtomAssignment W x) - z • 1)
    (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
    R.toBlocks₁₁ R.toBlocks₁₂ R.toBlocks₂₁ R.toBlocks₂₂
  simpa only [Matrix.fromBlocks_toBlocks] using h.symm

theorem physicalIntervalSteps_concat (W p q : ℕ) (z : ℂ)
    (x : IntervalRows W p) (y : IntervalRows W q) :
    physicalIntervalSteps W (p + q) z (intervalConcat W p q (x, y)) =
      physicalIntervalSteps W p z x ++ physicalIntervalSteps W q z y := by
  have hp (j : Fin p) : intervalSiteBlocks z (intervalConcat W p q (x, y)) (j.castAdd q) =
      intervalSiteBlocks z x j := by
    have h := intervalSiteBlocks_intervalRestriction (Fin.castAddEmb q) z
      (intervalConcat W p q (x, y)) j
    simpa only [intervalRestriction_concat_prefix, Fin.castAddEmb_apply] using h.symm
  have hq (j : Fin q) : intervalSiteBlocks z (intervalConcat W p q (x, y)) (j.natAdd p) =
      intervalSiteBlocks z y j := by
    have h := intervalSiteBlocks_intervalRestriction (Fin.natAddEmb p) z
      (intervalConcat W p q (x, y)) j
    simpa only [intervalRestriction_concat_suffix, Fin.natAddEmb_apply] using h.symm
  simp only [physicalIntervalSteps, List.ofFn_add, hq]
  congr 1
  apply congrArg List.ofFn
  funext j
  exact congrArg (fun M : PhysicalBlocks (Fin W) =>
    (⟨M.B, M.D, M.C⟩ : CompanionStep (Fin W))) (hp j)

theorem polynomialClearedCompoundProduct_append
    {W : Type*} [Fintype W] [LinearOrder W] (k : ℕ)
    (xs ys : List (CompanionStep W)) :
    polynomialClearedCompoundProduct k (xs ++ ys) =
      polynomialClearedCompoundProduct k ys * polynomialClearedCompoundProduct k xs := by
  simp only [polynomialClearedCompoundProduct_eq_reverse, List.reverse_append,
    List.map_append, List.prod_append]

theorem densityCyclicLogDet_terminalPacket
    (W s : ℕ) (z : ℂ) (outside : IntervalRows W s) (packet : IntervalRows W 3)
    (hB : ∀ j, IsUnit (intervalSiteBlocks z outside j).B.det) :
    densityCyclicLogDet W s z (intervalConcat W s 3 (outside, packet)) =
      Real.log ‖intervalClearingFactor W s z outside *
        physicalBoundaryExpression W 3 z packet (intervalTransferProduct W s z outside)‖ := by
  rw [densityCyclicLogDet_eq_polynomial_trace, physicalIntervalSteps_concat]
  have hp (a : Finset (Fin W ⊕ Fin W)) :
      polynomialClearedCompoundProduct a.card (physicalIntervalSteps W s z outside) =
        intervalClearingFactor W s z outside •
          compound a.card (intervalTransferProduct W s z outside) := by
    exact (polynomialClearedCompoundProduct_physicalIntervalSteps W s z outside
      (exteriorDegreeOfFinset W a)).trans
      (intervalClearedProduct_eq_clearing_smul_compound W s z outside hB
        (exteriorDegreeOfFinset W a))
  have heq : polynomialClearedSignedCompoundTrace
      (physicalIntervalSteps W s z outside ++ physicalIntervalSteps W 3 z packet) =
        intervalClearingFactor W s z outside *
          physicalBoundaryExpression W 3 z packet (intervalTransferProduct W s z outside) := by
    unfold polynomialClearedSignedCompoundTrace physicalBoundaryExpression polynomialClearedBoundaryTrace
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [polynomialClearedCompoundProduct_append, hp, Matrix.mul_smul,
      Matrix.smul_apply, smul_eq_mul]
    ring
  rw [heq]

end BernoulliSection10
