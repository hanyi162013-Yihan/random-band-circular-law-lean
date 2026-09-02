import BernoulliSection10.PacketPhysicalIdentification
import BernoulliSection10.PacketReset
import BernoulliSection10.PhysicalAffinity
import BernoulliSection10.AsymptoticScales

/-!
# Reset on the literal three-site interval

Both nonvanishing and the inverse-log estimate are transported from the
proved padded packet model. All source coordinates and their independence
have already been constructed by `packetPhysicalRows_measurePreserving`.
-/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator ENNReal

noncomputable section

namespace BernoulliSection10

open BernoulliLinearAlgebra Matrix Set Set.powersetCard

set_option maxHeartbeats 800000

local instance physicalPacketSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  BernoulliLinearAlgebra.clearedStepCompoundSumLinearOrder

def physicalPacketCoefficient (W : ℕ) (z : ℂ) (r : Fin (2 * W + 1))
    (U V : unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : powersetCard (Fin W ⊕ Fin W) r.1) (x : IntervalRows W 3) : ℂ :=
  ((compound r.1 (U : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ))ᴴ *
    intervalClearedProduct W 3 z x r *
    compound r.1 (V : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)) s s

theorem continuous_physicalPacketCoefficient
    (W : ℕ) (z : ℂ) (r : Fin (2 * W + 1))
    (U V : unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : powersetCard (Fin W ⊕ Fin W) r.1) :
    Continuous (physicalPacketCoefficient W z r U V s) := by
  have h : Continuous (fun x : IntervalRows W 3 =>
      (compound r.1 (U : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ))ᴴ *
        intervalClearedProduct W 3 z x r *
        compound r.1 (V : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)) :=
    (continuous_const.matrix_mul
      (continuous_intervalClearedProduct W 3 z r)).matrix_mul continuous_const
  exact (continuous_apply s).comp ((continuous_apply s).comp h)

def physicalPacketResetLoss (W : ℕ) (z : ℂ) (r : Fin (2 * W + 1))
    (U V : unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : powersetCard (Fin W ⊕ Fin W) r.1) (x : IntervalRows W 3) : ℝ :=
  Real.posLog ‖physicalPacketCoefficient W z r U V s x‖⁻¹

theorem measurable_physicalPacketResetLoss
    (W : ℕ) (z : ℂ) (r : Fin (2 * W + 1))
    (U V : unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : powersetCard (Fin W ⊕ Fin W) r.1) :
    Measurable (physicalPacketResetLoss W z r U V s) :=
  Real.continuous_posLog.measurable.comp
    (continuous_physicalPacketCoefficient W z r U V s).measurable.norm.inv

/-- Nonvanishing is proved separately from integrability, since the
totalized logarithm at zero alone cannot express this obligation. -/
theorem physicalPacketCoefficient_ne_zero_ae
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1))
    (U V : unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : powersetCard (Fin W ⊕ Fin W) r.1) :
    ∀ᵐ x ∂intervalRowsLaw W 3 μ, physicalPacketCoefficient W z r U V s x ≠ 0 := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (packetAtomRowsLaw W μ) := by
    unfold packetAtomRowsLaw
    infer_instance
  have hmp := packetPhysicalRows_measurePreserving (μ := μ) W
  have hm := (continuous_physicalPacketCoefficient W z r U V s).measurable
  rw [← hmp.map_eq]
  apply (ae_map_iff hmp.measurable.aemeasurable (hm (isClosed_singleton.measurableSet)).compl).2
  apply (Measure.ae_prod_iff_ae_ae ((hm.comp hmp.measurable)
    (isClosed_singleton.measurableSet)).compl).2
  filter_upwards [normalizedEndpointFactor_det_isUnit_ae hμ W hW] with ep hep
  have hprod : IsUnit (normalizedBlockDet W ep.1 * normalizedBlockDet W ep.2) := by
    simpa only [normalizedEndpointFactor_det] using hep
  have hparts := mul_ne_zero_iff.mp (isUnit_iff_ne_zero.mp hprod)
  have heval := (proposition_10_10_scalar_evaluation hμ W hW r.1 z
    (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
    (isUnit_iff_ne_zero.mpr hparts.1) (isUnit_iff_ne_zero.mpr hparts.2) U V s).2
  change ∀ᵐ x ∂packetAtomRowsLaw W μ,
    physicalPacketCoefficient W z r U V s (packetPhysicalRows W (ep, x)) ≠ 0
  simpa only [physicalPacketCoefficient, packetScalarCoefficientEval_eq_physical] using heval

theorem physicalPacketResetLoss_lintegral_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1))
    (U V : unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : powersetCard (Fin W ⊕ Fin W) r.1) :
    (∫⁻ x, ENNReal.ofReal (physicalPacketResetLoss W z r U V s x)
      ∂intervalRowsLaw W 3 μ) ≤
        packetProposition1010WLogConstant L z * oneSiteWLogScale W := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (packetAtomRowsLaw W μ) := by
    unfold packetAtomRowsLaw
    infer_instance
  have hmp := packetPhysicalRows_measurePreserving (μ := μ) W
  have hm := (measurable_physicalPacketResetLoss W z r U V s).ennreal_ofReal
  rw [← hmp.lintegral_comp hm]
  have heq := lintegral_prod (μ := endpointBlockPairLaw W μ)
    (ν := packetAtomRowsLaw W μ) _ (hm.comp hmp.measurable).aemeasurable
  simp only [Function.comp_def] at heq
  rw [heq]
  simpa only [physicalPacketResetLoss, physicalPacketCoefficient,
    ← packetScalarCoefficientEval_eq_physical] using
      proposition_10_10_packet_reset hμ W hW r.1 z U V s

theorem packetProposition1010WLogConstant_ne_top (L : ℝ) (z : ℂ) :
    packetProposition1010WLogConstant L z ≠ ⊤ := by
  unfold packetProposition1010WLogConstant packetTensorEndpointWLogConstant
    endpointExteriorWLogConstant
  finiteness

def physicalPacketResetConstant (L : ℝ) (z : ℂ) : ℝ :=
  (packetProposition1010WLogConstant L z).toReal

theorem physicalPacketResetConstant_nonneg (L : ℝ) (z : ℂ) :
    0 ≤ physicalPacketResetConstant L z := ENNReal.toReal_nonneg

theorem physicalPacketResetLoss_integrable
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1))
    (U V : unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : powersetCard (Fin W ⊕ Fin W) r.1) :
    Integrable (physicalPacketResetLoss W z r U V s) (intervalRowsLaw W 3 μ) := by
  refine ⟨(measurable_physicalPacketResetLoss W z r U V s).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [physicalPacketResetLoss, Real.norm_eq_abs,
    abs_of_nonneg (Real.posLog_nonneg (x := _))]
  exact lt_of_le_of_lt (physicalPacketResetLoss_lintegral_le hμ W hW z r U V s)
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top
      (packetProposition1010WLogConstant_ne_top L z) ENNReal.ofReal_ne_top))

theorem physicalPacketResetLoss_integral_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1))
    (U V : unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : powersetCard (Fin W ⊕ Fin W) r.1) :
    (∫ x, physicalPacketResetLoss W z r U V s x ∂intervalRowsLaw W 3 μ) ≤
      physicalPacketResetConstant L z * W * densityLogScale W := by
  have hnonneg : ∀ᵐ x ∂intervalRowsLaw W 3 μ,
      0 ≤ physicalPacketResetLoss W z r U V s x :=
    Filter.Eventually.of_forall fun _ => Real.posLog_nonneg
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg
    (measurable_physicalPacketResetLoss W z r U V s).aestronglyMeasurable]
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top
    (packetProposition1010WLogConstant_ne_top L z) ENNReal.ofReal_ne_top)
    (physicalPacketResetLoss_lintegral_le hμ W hW z r U V s)
  have hn : 0 ≤ (W : ℝ) * densityLogScale W :=
    mul_nonneg (Nat.cast_nonneg _) (densityLogScale_nonneg hW)
  dsimp only [densityLogScale] at hn
  simpa only [ENNReal.toReal_mul, oneSiteWLogScale, densityLogScale,
    ENNReal.toReal_ofReal hn, physicalPacketResetConstant, mul_assoc] using h

end BernoulliSection10
