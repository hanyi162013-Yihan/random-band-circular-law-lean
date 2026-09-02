import BernoulliSection8.CenteredTerminal
import BernoulliSection8.ProbabilityFibers
import SubgaussianSection8.BoundaryGrowth
import SubgaussianSection8.FrameSmallBall
import BernoulliSection8.OutsidePressure
import BernoulliSection8.CyclicTerminalIdentity
import BernoulliSection10.CyclicSeamAssembly

/-!
# Terminal comparison on the actual subgaussian cyclic matrix

The event explicitly includes a zero determinant. Fixed outside data are
integrated first over the fresh packet and then over its two endpoints.
The only external estimates in the resulting bound are Cook and Nguyen.
-/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace SubgaussianSection8
open BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra

local instance rademacherSeamSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  BernoulliLinearAlgebra.clearedStepCompoundSumLinearOrder

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def subgaussianSeamCost (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) (z : ℂ) : ℝ :=
  (subgaussianBoundaryLogConstant Ξ) I z * W * densityLogScale W + (W : ℝ) * Real.log 2

theorem subgaussianSeamCost_nonneg (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0})
    (W : ℕ) (hW : 0 < W) (z : ℂ) : 0 ≤ (subgaussianSeamCost Ξ) I W z := by
  unfold subgaussianSeamCost
  exact add_nonneg (mul_nonneg (mul_nonneg ((subgaussianBoundaryLogConstant_nonneg Ξ) I z)
    (Nat.cast_nonneg W)) (densityLogScale_nonneg hW))
    (mul_nonneg (Nat.cast_nonneg W) (Real.log_nonneg (by norm_num)))

theorem subgaussianSeam_fresh_probability_le (Ξ : Atom)
    (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0})
    (W : ℕ) (z : ℂ) (hW : (subgaussianBoundaryWidthThreshold Ξ) cook z ≤ W)
    (ep : EndpointBlockPair W) (hep : ep ∈ (subgaussianEndpointGoodEvent Ξ) I W)
    (a : ℂ) (ha : a ≠ 0) (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hR : IsUnit R.det) {t : ℝ} (ht : 0 < t) :
    (packetAtomRowsLaw W Ξ.law).real {x |
      absoluteLogDeviation (t + (subgaussianSeamCost Ξ) I W z) (outsideExteriorPressure a R)
        (a * physicalBoundaryExpression W 3 z (packetPhysicalRows W (ep, x)) R)} ≤
      (subgaussianBoundaryBadProbability Ξ) cook W + (subgaussianBoundaryBaseLoss Ξ) cook W z / t +
        Real.exp (-(2 * t)) := by
  have hW0 := ((subgaussianBoundaryWidthThreshold_pos Ξ) cook z).trans_le hW
  have hepg := (subgaussianEndpointGoodEvent_spec Ξ) I W ep hep
  have hCL := isUnit_iff_ne_zero.mpr
    (norm_pos_iff.mp (hepg.delta_pos.trans_le hepg.delta_le_norm_det_CL))
  have hBR := isUnit_iff_ne_zero.mpr
    (norm_pos_iff.mp (hepg.delta_pos.trans_le hepg.delta_le_norm_det_BR))
  have hcoef := (subgaussianPacketBoundaryCoefficient_log_gramVolume_le_on_endpoint_good Ξ)
    I W hW0 z ep hep R hR
  have hgram := abs_log_gramVolume_sub_log_maxExteriorOperatorGrowth_le R
  simp only [Fintype.card_fin] at hgram
  have hcenter : |Real.log (rademacherPacketBoundaryCoefficient W z
      (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2) R) -
      Real.log (maxExteriorOperatorGrowth R)| ≤ (subgaussianSeamCost Ξ) I W z := by
    exact (abs_sub_le _ (Real.log (gramVolume R)) _).trans (add_le_add hcoef hgram)
  have h := scaled_centered_terminal_probability_le (packetAtomRowsLaw W Ξ.law) ht
    ((measurable_packetBoundaryEval Ξ) W z (normalizedBlockMatrix W ep.1)
      (normalizedBlockMatrix W ep.2) R)
    ((subgaussianBoundarySmallBall Ξ) cook W z hW _ _ hCL hBR R hR) hcenter a ha
  simpa only [outsideExteriorPressure, packetBoundaryEval_eq_physical] using h

theorem subgaussianSeam_packet_probability_le (Ξ : Atom)
    (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0})
    (hI : Ξ.parameter ≤ I.subgaussianBound) (W : ℕ) (z : ℂ)
    (hW : (subgaussianBoundaryWidthThreshold Ξ) cook z ≤ W)
    (hWI : interfaceCanonicalLargeWThreshold I ≤ W)
    (a : ℂ) (ha : a ≠ 0) (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hR : IsUnit R.det) {t : ℝ} (ht : 0 < t) :
    (intervalRowsLaw W 3 Ξ.law).real {x |
      absoluteLogDeviation (t + (subgaussianSeamCost Ξ) I W z) (outsideExteriorPressure a R)
        (a * physicalBoundaryExpression W 3 z x R)} ≤
      (subgaussianBoundaryBadProbability Ξ) cook W + (subgaussianBoundaryBaseLoss Ξ) cook W z / t +
        Real.exp (-(2 * t)) + 9 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
  letI : IsProbabilityMeasure (endpointBlockPairLaw W Ξ.law) := by
    dsimp [endpointBlockPairLaw, blockAtomRowsLaw]
    infer_instance
  let E : Set (IntervalRows W 3) := {x |
    absoluteLogDeviation (t + (subgaussianSeamCost Ξ) I W z) (outsideExteriorPressure a R)
      (a * physicalBoundaryExpression W 3 z x R)}
  have hE : MeasurableSet E := measurableSet_absoluteLogDeviation _
    (measurable_const.mul (continuous_physicalBoundaryExpression W 3 z R).measurable)
    measurable_const
  have hmp := packetPhysicalRows_measurePreserving (μ := Ξ.law) W
  have h := prod_probability_le_of_good_fibers
    (endpointBlockPairLaw W Ξ.law) (packetAtomRowsLaw W Ξ.law)
    (hE.preimage hmp.measurable) ((measurableSet_subgaussianEndpointGoodEvent Ξ) I W).compl
    (show 0 ≤ (subgaussianBoundaryBadProbability Ξ) cook W +
      (subgaussianBoundaryBaseLoss Ξ) cook W z / t + Real.exp (-(2 * t)) from
      add_nonneg (add_nonneg ((subgaussianBoundaryBadProbability_nonneg Ξ) cook W)
        (div_nonneg ((subgaussianBoundaryBaseLoss_nonneg Ξ) cook W z) ht.le)) (Real.exp_pos _).le)
    (fun ep hep => (subgaussianSeam_fresh_probability_le Ξ) cook I W z hW ep
      (by simpa using hep) a ha R hR ht)
  rw [hmp.measureReal_preimage hE.nullMeasurableSet] at h
  exact h.trans (add_le_add le_rfl
    ((subgaussianEndpointGoodEvent_compl_probability_le Ξ) I hI W hWI))

theorem continuous_cyclicFockValue (Ξ : Atom) (W s : ℕ) (z : ℂ) :
    Continuous (cyclicFockValue W s z) := by
  refine (continuous_physicalBoundaryExpression W (s + 3) z 1).congr ?_
  intro x
  simp only [cyclicFockValue, physicalBoundaryExpression, polynomialClearedBoundaryTrace,
    polynomialClearedSignedCompoundTrace, compound_one, Matrix.mul_one]

def cyclicSeamBadEvent (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) (W s : ℕ) (z : ℂ) (t : ℝ) :
    Set (IntervalRows W (s + 3)) :=
  {x | cyclicFockValue W s z x = 0 ∨
    t + (subgaussianSeamCost Ξ) I W z ≤ |cyclicSeamDifference W s z x|}

theorem measurableSet_cyclicSeamBadEvent (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0})
    (W s : ℕ) (z : ℂ) (t : ℝ) : MeasurableSet ((cyclicSeamBadEvent Ξ) I W s z t) :=
  (((continuous_cyclicFockValue Ξ) W s z).measurable (measurableSet_singleton 0)).union
    (measurableSet_le measurable_const (measurable_cyclicSeamDifference W s z).norm)

theorem cyclicSeamBadEvent_probability_le (Ξ : Atom)
    (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0})
    (hI : Ξ.parameter ≤ I.subgaussianBound) (W s : ℕ) (z : ℂ)
    (hW : (subgaussianBoundaryWidthThreshold Ξ) cook z ≤ W)
    (hWI : interfaceCanonicalLargeWThreshold I ≤ W) {t : ℝ} (ht : 0 < t) :
    (intervalRowsLaw W (s + 3) Ξ.law).real ((cyclicSeamBadEvent Ξ) I W s z t) ≤
      (subgaussianBoundaryBadProbability Ξ) cook W + (subgaussianBoundaryBaseLoss Ξ) cook W z / t +
        Real.exp (-(2 * t)) + (9 + 3 * (s : ℝ)) *
          Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
  have hmp := intervalConcat_measurePreserving (μ := Ξ.law) W s 3
  have hE := (measurableSet_cyclicSeamBadEvent Ξ) I W s z t
  have hprob : ∀ outside ∉ ((subgaussianInterfaceGoodEvent Ξ) I W s)ᶜ,
      (intervalRowsLaw W 3 Ξ.law).real {packet |
        intervalConcat W s 3 (outside, packet) ∈ (cyclicSeamBadEvent Ξ) I W s z t} ≤
        (subgaussianBoundaryBadProbability Ξ) cook W + (subgaussianBoundaryBaseLoss Ξ) cook W z / t +
          Real.exp (-(2 * t)) + 9 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
    intro outside hout
    have hg : outside ∈ (subgaussianInterfaceGoodEvent Ξ) I W s := by simpa using hout
    have hblocks := (subgaussianInterface_dets_isUnit_of_good Ξ) I hI W s hWI outside hg z
    have hB := fun j => (hblocks j).1
    have hC := fun j => (hblocks j).2
    have hrep := (subgaussianIntervalTransfer_representation_of_good Ξ) I hI W s hWI outside hg z
    have hp := intervalMaxDegreeLog_eq_outsidePressure_of_units W s z outside hB hC
    have heq : {packet | intervalConcat W s 3 (outside, packet) ∈ (cyclicSeamBadEvent Ξ) I W s z t} =
        {packet | absoluteLogDeviation (t + (subgaussianSeamCost Ξ) I W z)
          (outsideExteriorPressure (intervalClearingFactor W s z outside)
            (intervalTransferProduct W s z outside))
          (intervalClearingFactor W s z outside * physicalBoundaryExpression W 3 z packet
            (intervalTransferProduct W s z outside))} := by
      ext packet
      simp only [(cyclicSeamBadEvent Ξ), Set.mem_setOf_eq, cyclicFockValue_terminalPacket W s z
        outside packet hB, cyclicSeamDifference, intervalRestriction_concat_prefix,
        densityCyclicLogDet_terminalPacket W s z outside packet hB, hp, absoluteLogDeviation]
    rw [heq]
    exact (subgaussianSeam_packet_probability_le Ξ) cook I hI W z hW hWI _ hrep.1 _ hrep.2.1 ht
  have hnonneg : 0 ≤ (subgaussianBoundaryBadProbability Ξ) cook W +
      (subgaussianBoundaryBaseLoss Ξ) cook W z / t + Real.exp (-(2 * t)) +
      9 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
    have h1 := (subgaussianBoundaryBadProbability_nonneg Ξ) cook W
    have h2 := (subgaussianBoundaryBaseLoss_nonneg Ξ) cook W z
    positivity
  have h := prod_probability_le_of_good_fibers
    (intervalRowsLaw W s Ξ.law) (intervalRowsLaw W 3 Ξ.law)
    (hE.preimage hmp.measurable) ((measurableSet_subgaussianInterfaceGoodEvent Ξ) I W s).compl
    hnonneg hprob
  rw [hmp.measureReal_preimage hE.nullMeasurableSet] at h
  have hb := (subgaussianInterfaceGoodEvent_compl_probability_le Ξ) I hI W s hWI
  nlinarith

end SubgaussianSection8
