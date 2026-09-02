import BernoulliSection10.PhysicalBoundaryExpression
import BernoulliSection10.SeamProbability
import BernoulliSection10.PhysicalPacketReset

/-! # The periodic seam estimate on a literal three-site interval -/

open MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace BernoulliSection10

open BernoulliLinearAlgebra Matrix

set_option maxHeartbeats 800000

def physicalSeamLoss (W : ℕ) (z c : ℂ)
    (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) (x : IntervalRows W 3) : ℝ :=
  |Real.log ‖c * physicalBoundaryExpression W 3 z x R‖ - outsideExteriorPressure c R|

theorem measurable_physicalSeamLoss (W : ℕ) (z c : ℂ)
    (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    Measurable (physicalSeamLoss W z c R) := by
  have hc : Continuous (fun x : IntervalRows W 3 => c * physicalBoundaryExpression W 3 z x R) :=
    continuous_const.mul (continuous_physicalBoundaryExpression W 3 z R)
  have hm := (Real.measurable_log.comp
    hc.norm.measurable).sub_const
      (outsideExteriorPressure c R)
  change Measurable (fun x : IntervalRows W 3 =>
    |Real.log ‖c * physicalBoundaryExpression W 3 z x R‖ - outsideExteriorPressure c R|)
  exact hm.norm

theorem physicalBoundaryExpression_ne_zero_ae
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ)
    (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) (hR : IsUnit R.det) :
    ∀ᵐ x ∂intervalRowsLaw W 3 μ, physicalBoundaryExpression W 3 z x R ≠ 0 := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (packetAtomRowsLaw W μ) := by
    unfold packetAtomRowsLaw
    infer_instance
  have hmp := packetPhysicalRows_measurePreserving (μ := μ) W
  have hm := (continuous_physicalBoundaryExpression W 3 z R).measurable
  rw [← hmp.map_eq]
  apply (ae_map_iff hmp.measurable.aemeasurable (hm isClosed_singleton.measurableSet).compl).2
  apply (Measure.ae_prod_iff_ae_ae
    ((hm.comp hmp.measurable) isClosed_singleton.measurableSet).compl).2
  filter_upwards [normalizedEndpointFactor_det_isUnit_ae hμ W hW] with ep hep
  have hprod : IsUnit (normalizedBlockDet W ep.1 * normalizedBlockDet W ep.2) := by
    simpa only [normalizedEndpointFactor_det] using hep
  have hparts := mul_ne_zero_iff.mp (isUnit_iff_ne_zero.mp hprod)
  have heval := (proposition_10_9 hμ W hW z
    (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
    (isUnit_iff_ne_zero.mpr hparts.1) (isUnit_iff_ne_zero.mpr hparts.2) R hR).2
  change ∀ᵐ x ∂packetAtomRowsLaw W μ,
    physicalBoundaryExpression W 3 z (packetPhysicalRows W (ep, x)) R ≠ 0
  simpa only [packetBoundaryEval_eq_physical] using heval

theorem physicalSeamLoss_lintegral_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z c : ℂ) (hc : c ≠ 0)
    (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) (hR : IsUnit R.det) :
    (∫⁻ x, ENNReal.ofReal (physicalSeamLoss W z c R x) ∂intervalRowsLaw W 3 μ) ≤
      packetProposition107WLogConstant L z * oneSiteWLogScale W := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (packetAtomRowsLaw W μ) := by
    unfold packetAtomRowsLaw
    infer_instance
  have hmp := packetPhysicalRows_measurePreserving (μ := μ) W
  have hm := (measurable_physicalSeamLoss W z c R).ennreal_ofReal
  rw [← hmp.lintegral_comp hm]
  have heq := lintegral_prod (μ := endpointBlockPairLaw W μ)
    (ν := packetAtomRowsLaw W μ) _ (hm.comp hmp.measurable).aemeasurable
  simp only [Function.comp_def] at heq
  rw [heq]
  simpa only [physicalSeamLoss, ← packetBoundaryEval_eq_physical] using
    proposition_10_7_periodic_seam hμ W hW z c hc R hR

theorem packetProposition107WLogConstant_ne_top (L : ℝ) (z : ℂ) :
    packetProposition107WLogConstant L z ≠ ⊤ := by
  unfold packetProposition107WLogConstant packetProposition108WLogConstant
    endpointExteriorWLogConstant
  finiteness

def physicalSeamConstant (L : ℝ) (z : ℂ) : ℝ :=
  (packetProposition107WLogConstant L z).toReal

theorem physicalSeamConstant_nonneg (L : ℝ) (z : ℂ) :
    0 ≤ physicalSeamConstant L z := ENNReal.toReal_nonneg

theorem physicalSeamLoss_integrable
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z c : ℂ) (hc : c ≠ 0)
    (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) (hR : IsUnit R.det) :
    Integrable (physicalSeamLoss W z c R) (intervalRowsLaw W 3 μ) := by
  refine ⟨(measurable_physicalSeamLoss W z c R).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [physicalSeamLoss, Real.norm_eq_abs, abs_abs]
  exact lt_of_le_of_lt (physicalSeamLoss_lintegral_le hμ W hW z c hc R hR)
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top
      (packetProposition107WLogConstant_ne_top L z) ENNReal.ofReal_ne_top))

theorem physicalSeamLoss_integral_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z c : ℂ) (hc : c ≠ 0)
    (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) (hR : IsUnit R.det) :
    (∫ x, physicalSeamLoss W z c R x ∂intervalRowsLaw W 3 μ) ≤
      physicalSeamConstant L z * W * densityLogScale W := by
  have hn0 : ∀ᵐ x ∂intervalRowsLaw W 3 μ, 0 ≤ physicalSeamLoss W z c R x :=
    Filter.Eventually.of_forall fun _ => abs_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae hn0
    (measurable_physicalSeamLoss W z c R).aestronglyMeasurable]
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top
    (packetProposition107WLogConstant_ne_top L z) ENNReal.ofReal_ne_top)
    (physicalSeamLoss_lintegral_le hμ W hW z c hc R hR)
  have hn : 0 ≤ (W : ℝ) * densityLogScale W :=
    mul_nonneg (Nat.cast_nonneg _) (densityLogScale_nonneg hW)
  dsimp only [densityLogScale] at hn
  simpa only [ENNReal.toReal_mul, oneSiteWLogScale, densityLogScale,
    ENNReal.toReal_ofReal hn, physicalSeamConstant, mul_assoc] using h

end BernoulliSection10
