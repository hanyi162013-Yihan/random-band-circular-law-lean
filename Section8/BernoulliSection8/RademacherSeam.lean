import BernoulliSection8.CenteredTerminal
import BernoulliSection8.ProbabilityFibers
import BernoulliSection8.RademacherBoundaryGrowth
import BernoulliSection8.RademacherFrameSmallBall
import BernoulliSection8.OutsidePressure
import BernoulliSection8.CyclicTerminalIdentity
import BernoulliSection10.CyclicSeamAssembly

/-!
# Terminal comparison on the actual Rademacher cyclic matrix

The event explicitly includes a zero determinant. Fixed outside data are
integrated first over the fresh packet and then over its two endpoints.
The only external estimates in the resulting bound are Cook and Nguyen.
-/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra

local instance rademacherSeamSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  BernoulliLinearAlgebra.clearedStepCompoundSumLinearOrder

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def rademacherSeamCost (I : NguyenBottomSingularInput) (W : ℕ) (z : ℂ) : ℝ :=
  rademacherBoundaryLogConstant I z * W * densityLogScale W + (W : ℝ) * Real.log 2

theorem rademacherSeamCost_nonneg (I : NguyenBottomSingularInput)
    (W : ℕ) (hW : 0 < W) (z : ℂ) : 0 ≤ rademacherSeamCost I W z := by
  unfold rademacherSeamCost
  exact add_nonneg (mul_nonneg (mul_nonneg (rademacherBoundaryLogConstant_nonneg I z)
    (Nat.cast_nonneg W)) (densityLogScale_nonneg hW))
    (mul_nonneg (Nat.cast_nonneg W) (Real.log_nonneg (by norm_num)))

theorem rademacherSeam_fresh_probability_le
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput)
    (W : ℕ) (z : ℂ) (hW : rademacherBoundaryWidthThreshold cook z ≤ W)
    (ep : EndpointBlockPair W) (hep : ep ∈ rademacherEndpointGoodEvent I W)
    (a : ℂ) (ha : a ≠ 0) (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hR : IsUnit R.det) {t : ℝ} (ht : 0 < t) :
    (packetAtomRowsLaw W rademacherLaw).real {x |
      absoluteLogDeviation (t + rademacherSeamCost I W z) (outsideExteriorPressure a R)
        (a * physicalBoundaryExpression W 3 z (packetPhysicalRows W (ep, x)) R)} ≤
      rademacherBoundaryBadProbability cook W + rademacherBoundaryBaseLoss cook W z / t +
        Real.exp (-(2 * t)) := by
  have hW0 := (rademacherBoundaryWidthThreshold_pos cook z).trans_le hW
  have hepg := rademacherEndpointGoodEvent_spec I W ep hep
  have hCL := isUnit_iff_ne_zero.mpr
    (norm_pos_iff.mp (hepg.delta_pos.trans_le hepg.delta_le_norm_det_CL))
  have hBR := isUnit_iff_ne_zero.mpr
    (norm_pos_iff.mp (hepg.delta_pos.trans_le hepg.delta_le_norm_det_BR))
  have hcoef := rademacherPacketBoundaryCoefficient_log_gramVolume_le_on_endpoint_good
    I W hW0 z ep hep R hR
  have hgram := abs_log_gramVolume_sub_log_maxExteriorOperatorGrowth_le R
  simp only [Fintype.card_fin] at hgram
  have hcenter : |Real.log (rademacherPacketBoundaryCoefficient W z
      (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2) R) -
      Real.log (maxExteriorOperatorGrowth R)| ≤ rademacherSeamCost I W z := by
    exact (abs_sub_le _ (Real.log (gramVolume R)) _).trans (add_le_add hcoef hgram)
  have h := scaled_centered_terminal_probability_le (packetAtomRowsLaw W rademacherLaw) ht
    (measurable_packetBoundaryEval W z (normalizedBlockMatrix W ep.1)
      (normalizedBlockMatrix W ep.2) R)
    (rademacherBoundarySmallBall cook W z hW _ _ hCL hBR R hR) hcenter a ha
  simpa only [outsideExteriorPressure, packetBoundaryEval_eq_physical] using h

theorem rademacherSeam_packet_probability_le
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput)
    (hI : 1 ≤ I.subgaussianBound) (W : ℕ) (z : ℂ)
    (hW : rademacherBoundaryWidthThreshold cook z ≤ W)
    (hWI : interfaceCanonicalLargeWThreshold I ≤ W)
    (a : ℂ) (ha : a ≠ 0) (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hR : IsUnit R.det) {t : ℝ} (ht : 0 < t) :
    (intervalRowsLaw W 3 rademacherLaw).real {x |
      absoluteLogDeviation (t + rademacherSeamCost I W z) (outsideExteriorPressure a R)
        (a * physicalBoundaryExpression W 3 z x R)} ≤
      rademacherBoundaryBadProbability cook W + rademacherBoundaryBaseLoss cook W z / t +
        Real.exp (-(2 * t)) + 9 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
  letI : IsProbabilityMeasure (endpointBlockPairLaw W rademacherLaw) := by
    dsimp [endpointBlockPairLaw, blockAtomRowsLaw]
    infer_instance
  let E : Set (IntervalRows W 3) := {x |
    absoluteLogDeviation (t + rademacherSeamCost I W z) (outsideExteriorPressure a R)
      (a * physicalBoundaryExpression W 3 z x R)}
  have hE : MeasurableSet E := measurableSet_absoluteLogDeviation _
    (measurable_const.mul (continuous_physicalBoundaryExpression W 3 z R).measurable)
    measurable_const
  have hmp := packetPhysicalRows_measurePreserving (μ := rademacherLaw) W
  have h := prod_probability_le_of_good_fibers
    (endpointBlockPairLaw W rademacherLaw) (packetAtomRowsLaw W rademacherLaw)
    (hE.preimage hmp.measurable) (measurableSet_rademacherEndpointGoodEvent I W).compl
    (show 0 ≤ rademacherBoundaryBadProbability cook W +
      rademacherBoundaryBaseLoss cook W z / t + Real.exp (-(2 * t)) from
      add_nonneg (add_nonneg (rademacherBoundaryBadProbability_nonneg cook W)
        (div_nonneg (rademacherBoundaryBaseLoss_nonneg cook W z) ht.le)) (Real.exp_pos _).le)
    (fun ep hep => rademacherSeam_fresh_probability_le cook I W z hW ep
      (by simpa using hep) a ha R hR ht)
  rw [hmp.measureReal_preimage hE.nullMeasurableSet] at h
  exact h.trans (add_le_add_left
    (rademacherEndpointGoodEvent_compl_probability_le I hI W hWI) _)

theorem continuous_cyclicFockValue (W s : ℕ) (z : ℂ) :
    Continuous (cyclicFockValue W s z) := by
  simpa only [cyclicFockValue, physicalBoundaryExpression, polynomialClearedBoundaryTrace,
    polynomialClearedSignedCompoundTrace, compound_one, Matrix.mul_one] using
      continuous_physicalBoundaryExpression W (s + 3) z 1

def cyclicSeamBadEvent (I : NguyenBottomSingularInput) (W s : ℕ) (z : ℂ) (t : ℝ) :
    Set (IntervalRows W (s + 3)) :=
  {x | cyclicFockValue W s z x = 0 ∨
    t + rademacherSeamCost I W z ≤ |cyclicSeamDifference W s z x|}

theorem measurableSet_cyclicSeamBadEvent (I : NguyenBottomSingularInput)
    (W s : ℕ) (z : ℂ) (t : ℝ) : MeasurableSet (cyclicSeamBadEvent I W s z t) :=
  ((continuous_cyclicFockValue W s z).measurable (measurableSet_singleton 0)).union
    (measurableSet_le measurable_const (measurable_cyclicSeamDifference W s z).norm)

theorem cyclicSeamBadEvent_probability_le
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput)
    (hI : 1 ≤ I.subgaussianBound) (W s : ℕ) (z : ℂ)
    (hW : rademacherBoundaryWidthThreshold cook z ≤ W)
    (hWI : interfaceCanonicalLargeWThreshold I ≤ W) {t : ℝ} (ht : 0 < t) :
    (intervalRowsLaw W (s + 3) rademacherLaw).real (cyclicSeamBadEvent I W s z t) ≤
      rademacherBoundaryBadProbability cook W + rademacherBoundaryBaseLoss cook W z / t +
        Real.exp (-(2 * t)) + (9 + 3 * (s : ℝ)) *
          Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
  have hmp := intervalConcat_measurePreserving (μ := rademacherLaw) W s 3
  have hE := measurableSet_cyclicSeamBadEvent I W s z t
  have hprob : ∀ outside ∉ (rademacherInterfaceGoodEvent I W s)ᶜ,
      (intervalRowsLaw W 3 rademacherLaw).real {packet |
        intervalConcat W s 3 (outside, packet) ∈ cyclicSeamBadEvent I W s z t} ≤
        rademacherBoundaryBadProbability cook W + rademacherBoundaryBaseLoss cook W z / t +
          Real.exp (-(2 * t)) + 9 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
    intro outside hout
    have hg : outside ∈ rademacherInterfaceGoodEvent I W s := by simpa using hout
    have hblocks := rademacherInterface_dets_isUnit_of_good I hI W s hWI outside hg.2 z
    have hB := fun j => (hblocks j).1
    have hC := fun j => (hblocks j).2
    have hrep := rademacherIntervalTransfer_representation_of_good I hI W s hWI outside hg.2 z
    have hp := intervalMaxDegreeLog_eq_outsidePressure_of_units W s z outside hB hC
    have heq : {packet | intervalConcat W s 3 (outside, packet) ∈ cyclicSeamBadEvent I W s z t} =
        {packet | absoluteLogDeviation (t + rademacherSeamCost I W z)
          (outsideExteriorPressure (intervalClearingFactor W s z outside)
            (intervalTransferProduct W s z outside))
          (intervalClearingFactor W s z outside * physicalBoundaryExpression W 3 z packet
            (intervalTransferProduct W s z outside))} := by
      ext packet
      simp only [cyclicSeamBadEvent, Set.mem_setOf_eq, cyclicFockValue_terminalPacket W s z
        outside packet hB, cyclicSeamDifference, intervalRestriction_concat_prefix,
        densityCyclicLogDet_terminalPacket W s z outside packet hB, hp, absoluteLogDeviation]
    rw [heq]
    exact rademacherSeam_packet_probability_le cook I hI W z hW hWI _ hrep.1 _ hrep.2.1 ht
  have hnonneg : 0 ≤ rademacherBoundaryBadProbability cook W +
      rademacherBoundaryBaseLoss cook W z / t + Real.exp (-(2 * t)) +
      9 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
    have h1 := rademacherBoundaryBadProbability_nonneg cook W
    have h2 := rademacherBoundaryBaseLoss_nonneg cook W z
    positivity
  have h := prod_probability_le_of_good_fibers
    (intervalRowsLaw W s rademacherLaw) (intervalRowsLaw W 3 rademacherLaw)
    (hE.preimage hmp.measurable) (measurableSet_rademacherInterfaceGoodEvent I W s).compl
    hnonneg hprob
  rw [hmp.measureReal_preimage hE.nullMeasurableSet] at h
  have hb := rademacherInterfaceGoodEvent_compl_probability_le I hI W s hWI
  nlinarith

end BernoulliSection8
