import BernoulliSection8.ConditionalCappedReset
import BernoulliSection8.CappedAveraging
import BernoulliSection8.RademacherEndpointInterface
import BernoulliSection10.ResetSandwichLaw

/-!
# Integrating the complete physical reset loss

The two endpoint blocks and the seven fresh blocks together carry exactly
the physical three-site law. Bad endpoint, core, and past events are
charged the cap using Nguyen's exponential bound. Cook's slower error is
used only inside the averaged loss.
-/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem physicalCappedResetLoss_reset_integral_le
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput)
    (hI : 1 ≤ I.subgaussianBound) (W p q : ℕ) (z : ℂ)
    (hW : rademacherBoundaryWidthThreshold cook z ≤ W)
    (hWI : interfaceCanonicalLargeWThreshold I ≤ W)
    (core : IntervalRows W p) (past : IntervalRows W q)
    (hcoreB : ∀ j, IsUnit (intervalSiteBlocks z core j).B.det)
    (hcoreC : ∀ j, IsUnit (intervalSiteBlocks z core j).C.det)
    (hpastB : ∀ j, IsUnit (intervalSiteBlocks z past j).B.det)
    (hpastC : ∀ j, IsUnit (intervalSiteBlocks z past j).C.det)
    (r : Fin (2 * W + 1)) {T D : ℝ} (hT : 0 < T) (hD : 0 ≤ D)
    (hGamma : ∀ ep ∈ rademacherEndpointGoodEvent I W,
      -Real.log (rademacherBoundaryInverseGamma W z
        (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)) ≤ D) :
    (∫ reset, physicalCappedResetLoss W p q z r T core past reset
      ∂intervalRowsLaw W 3 rademacherLaw) ≤
        D + rademacherBoundaryBaseLoss cook W z + T *
          (rademacherBoundaryBadProbability cook W +
            9 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ))) := by
  letI : IsProbabilityMeasure (endpointBlockPairLaw W rademacherLaw) := by
    dsimp [endpointBlockPairLaw, blockAtomRowsLaw]
    infer_instance
  have hmp := packetPhysicalRows_measurePreserving (μ := rademacherLaw) W
  have hm := measurable_physicalCappedResetLoss W p q z r T core past
  rw [← real_integral_comp_measurePreserving hmp hm]
  have hg : ∀ ep ∉ (rademacherEndpointGoodEvent I W)ᶜ,
      (∫ x, physicalCappedResetLoss W p q z r T core past
        (packetPhysicalRows W (ep, x)) ∂packetAtomRowsLaw W rademacherLaw) ≤
        D + rademacherBoundaryBaseLoss cook W z + rademacherBoundaryBadProbability cook W * T := by
    intro ep hep
    have hepg : ep ∈ rademacherEndpointGoodEvent I W := by simpa using hep
    have hspec := rademacherEndpointGoodEvent_spec I W ep hepg
    apply physicalCappedResetLoss_fresh_integral_le cook W p q z hW core past
      hcoreB hcoreC hpastB hpastC ep _ _ r hT hD (hGamma ep hepg)
    · exact isUnit_iff_ne_zero.mpr
        (norm_pos_iff.mp (hspec.delta_pos.trans_le hspec.delta_le_norm_det_CL))
    · exact isUnit_iff_ne_zero.mpr
        (norm_pos_iff.mp (hspec.delta_pos.trans_le hspec.delta_le_norm_det_BR))
  have h := integral_prod_le_of_good_fibers
    (endpointBlockPairLaw W rademacherLaw) (packetAtomRowsLaw W rademacherLaw)
    (hm.comp hmp.measurable) hT.le
    (add_nonneg (add_nonneg hD (rademacherBoundaryBaseLoss_nonneg cook W z))
      (mul_nonneg (rademacherBoundaryBadProbability_nonneg cook W) hT.le))
    (fun x => physicalCappedResetLoss_nonneg W p q z r hT.le core past _)
    (fun x => physicalCappedResetLoss_le_cap W p q z r T core past _)
    (measurableSet_rademacherEndpointGoodEvent I W).compl hg
  have hp := rademacherEndpointGoodEvent_compl_probability_le I hI W hWI
  have hmul := mul_le_mul_of_nonneg_left hp hT.le
  dsimp only [Function.comp_def] at h
  linarith

def resetLossFlat (W p q : ℕ) (z : ℂ) (r : Fin (2 * W + 1)) (T : ℝ)
    (x : (IntervalRows W p × IntervalRows W q) × IntervalRows W 3) : ℝ :=
  physicalCappedResetLoss W p q z r T x.1.1 x.1.2 x.2

theorem measurable_resetLossFlat (W p q : ℕ) (z : ℂ) (r : Fin (2 * W + 1)) (T : ℝ) :
    Measurable (resetLossFlat W p q z r T) := by
  have hA : Continuous (fun x : (IntervalRows W p × IntervalRows W q) × IntervalRows W 3 =>
      intervalClearedProduct W p z x.1.1 r) :=
    (continuous_intervalClearedProduct W p z r).comp (continuous_fst.comp continuous_fst)
  have hB : Continuous (fun x : (IntervalRows W p × IntervalRows W q) × IntervalRows W 3 =>
      intervalClearedProduct W q z x.1.2 r) :=
    (continuous_intervalClearedProduct W q z r).comp (continuous_snd.comp continuous_fst)
  have hR : Continuous (fun x : (IntervalRows W p × IntervalRows W q) × IntervalRows W 3 =>
      intervalClearedProduct W 3 z x.2 r) :=
    (continuous_intervalClearedProduct W 3 z r).comp continuous_snd
  exact measurable_cappedSpliceLoss T hA.norm.measurable hB.norm.measurable
    ((hA.matrix_mul hR).matrix_mul hB).norm.measurable

theorem product_good_compl_probability_le
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set Ω) (B : Set Ξ) :
    (μ.prod ν).real (A ×ˢ B)ᶜ ≤ μ.real Aᶜ + ν.real Bᶜ := by
  have heq : (A ×ˢ B)ᶜ = (Aᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ Bᶜ) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_prod, Set.mem_union, Set.mem_univ, and_true, true_and]
    tauto
  rw [heq]
  exact (measureReal_union_le _ _).trans_eq (by simp [measureReal_prod_prod])

/-- The actual complete reset expectation, including all outside bad
fibers. The coefficient estimate will be instantiated with the proved
endpoint constant; no measurable frame selection occurs in this theorem. -/
theorem resetLossFlat_integral_le
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput)
    (hI : 1 ≤ I.subgaussianBound) (W p q : ℕ) (z : ℂ)
    (hW : rademacherBoundaryWidthThreshold cook z ≤ W)
    (hWI : interfaceCanonicalLargeWThreshold I ≤ W)
    (r : Fin (2 * W + 1)) {T D : ℝ} (hT : 0 < T) (hD : 0 ≤ D)
    (hGamma : ∀ ep ∈ rademacherEndpointGoodEvent I W,
      -Real.log (rademacherBoundaryInverseGamma W z
        (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)) ≤ D) :
    (∫ x, resetLossFlat W p q z r T x
      ∂((intervalRowsLaw W p rademacherLaw).prod (intervalRowsLaw W q rademacherLaw)).prod
        (intervalRowsLaw W 3 rademacherLaw)) ≤
      D + rademacherBoundaryBaseLoss cook W z + T *
        (rademacherBoundaryBadProbability cook W + (9 + 3 * ((p : ℝ) + q)) *
          Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ))) := by
  let E := (rademacherInterfaceGoodEvent I W p ×ˢ rademacherInterfaceGoodEvent I W q)ᶜ
  have hE : MeasurableSet E :=
    ((measurableSet_rademacherInterfaceGoodEvent I W p).prod
      (measurableSet_rademacherInterfaceGoodEvent I W q)).compl
  let B := D + rademacherBoundaryBaseLoss cook W z + T *
    (rademacherBoundaryBadProbability cook W +
      9 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)))
  have hB : 0 ≤ B := by
    exact add_nonneg (add_nonneg hD (rademacherBoundaryBaseLoss_nonneg cook W z))
      (mul_nonneg hT.le (add_nonneg (rademacherBoundaryBadProbability_nonneg cook W)
        (mul_nonneg (by norm_num) (Real.exp_pos _).le)))
  have hg : ∀ x ∉ E, (∫ reset, resetLossFlat W p q z r T (x, reset)
      ∂intervalRowsLaw W 3 rademacherLaw) ≤ B := by
    intro x hx
    have hxg : x.1 ∈ rademacherInterfaceGoodEvent I W p ∧
        x.2 ∈ rademacherInterfaceGoodEvent I W q := by simpa [E] using hx
    have hcore := rademacherInterface_dets_isUnit_of_good I hI W p hWI x.1 hxg.1.2 z
    have hpast := rademacherInterface_dets_isUnit_of_good I hI W q hWI x.2 hxg.2.2 z
    exact physicalCappedResetLoss_reset_integral_le cook I hI W p q z hW hWI x.1 x.2
      (fun j => (hcore j).1) (fun j => (hcore j).2)
      (fun j => (hpast j).1) (fun j => (hpast j).2) r hT hD hGamma
  have h := integral_prod_le_of_good_fibers
    ((intervalRowsLaw W p rademacherLaw).prod (intervalRowsLaw W q rademacherLaw))
    (intervalRowsLaw W 3 rademacherLaw) (measurable_resetLossFlat W p q z r T) hT.le hB
    (fun x => physicalCappedResetLoss_nonneg W p q z r hT.le _ _ _)
    (fun x => physicalCappedResetLoss_le_cap W p q z r T _ _ _) hE hg
  have hp := (product_good_compl_probability_le
    (intervalRowsLaw W p rademacherLaw) (intervalRowsLaw W q rademacherLaw)
    (rademacherInterfaceGoodEvent I W p) (rademacherInterfaceGoodEvent I W q)).trans
    (add_le_add
      (rademacherInterfaceGoodEvent_compl_probability_le I hI W p hWI)
      (rademacherInterfaceGoodEvent_compl_probability_le I hI W q hWI))
  have hmul := mul_le_mul_of_nonneg_left hp hT.le
  dsimp [B, E] at h
  nlinarith

end BernoulliSection8
