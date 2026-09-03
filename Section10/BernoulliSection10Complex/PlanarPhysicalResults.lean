import BernoulliSection10Complex.PlanarAnalyticResults
import BernoulliSection10Complex.MeanStitching
import BernoulliSection10Complex.CyclicPressureComparison
import BernoulliSection10Complex.DensityEnergyLimit

/-!
# Public planar-density estimates before the Section 3 assembly

Only the original atom hypotheses appear here. The numerical enlargement
of the density bound is discharged internally. Physical packet, frame,
Hodge and resampling estimates are proved for the literal complex laws.
The high-band Section 3 connection is intentionally kept out of this
front-end build target.
-/

open MeasureTheory
open scoped ENNReal BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10 BernoulliLinearAlgebra Matrix Set Set.powersetCard

theorem planar_lemma_10_5
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫ x, maxCenteredDeviation (intervalDegreeLogs W s z)
          (intervalRowsLaw W s μ) x ∂intervalRowsLaw W s μ) ≤
      Real.sqrt
        (∑ _r : Fin (2 * W + 1), (1 / 2 : ℝ) *
          ∑ _i : Fin (s * W), physicalRowResamplingEnergy W (max 1 L)) := by
  exact lemma_10_5 hμ.normalized W s hW z

theorem planar_intervalMaxHodgeEnvelope_memLp_two
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    MemLp (intervalMaxHodgeEnvelope W s z) 2
      (intervalRowsLaw W s μ) := by
  exact intervalMaxHodgeEnvelope_memLp_two hμ.normalized W s hW z

theorem planar_intervalMaxHodgeEnvelope_lintegral_le_W_log_eW
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (intervalMaxHodgeEnvelope W s z x)
        ∂intervalRowsLaw W s μ) ≤
      (s : ℝ≥0∞) * oneSiteMaxHodgeWLogConstant (max 1 L) z *
        oneSiteWLogScale W := by
  exact intervalMaxHodgeEnvelope_lintegral_le_W_log_eW hμ.normalized W s hW z

theorem planar_proposition_10_7_periodic_seam
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z c : ℂ) (hc : c ≠ 0)
    (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hR : IsUnit R.det) :
    (∫⁻ ep, ∫⁻ x, ENNReal.ofReal
        |Real.log ‖c * packetBoundaryEval W z
            (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
            R x‖ - outsideExteriorPressure c R|
          ∂packetAtomRowsLaw W μ ∂endpointBlockPairLaw W μ) ≤
      packetProposition107WLogConstant (max 1 L) z * oneSiteWLogScale W := by
  exact proposition_10_7_periodic_seam hμ.normalized W hW z c hc R hR

theorem planar_proposition_10_8_integrated_endpoint_comparison
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hTheta : IsUnit Theta.det) :
    (∫⁻ x, ENNReal.ofReal
        |Real.log (packetBoundaryCoefficientNorm z
            (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)
            Theta) -
          (1 / 2 : ℝ) * Real.log (gramEnergy Theta)|
        ∂endpointBlockPairLaw W μ) ≤
      packetProposition108WLogConstant (max 1 L) z * oneSiteWLogScale W := by
  exact proposition_10_8_integrated_endpoint_comparison hμ.normalized W hW z Theta hTheta

theorem planar_proposition_10_9
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hTheta : IsUnit Theta.det) :
    (∫⁻ x, ENNReal.ofReal
        |Real.log ‖packetBoundaryEval W z CL BR Theta x‖ -
          Real.log ‖packetBoundaryCoefficientTensor W z CL BR Theta‖|
        ∂packetAtomRowsLaw W μ) ≤
        multiAffineLogCost (max 1 L)
          (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) ∧
      ∀ᵐ x ∂packetAtomRowsLaw W μ,
        packetBoundaryEval W z CL BR Theta x ≠ 0 := by
  exact proposition_10_9 hμ.normalized W hW z CL BR hCL hBR Theta hTheta

theorem planar_proposition_10_10_packet_reset
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (r : ℕ) (z : ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    (∫⁻ ep, ∫⁻ x, ENNReal.ofReal (Real.posLog
        ‖packetScalarCoefficientEval W r z
          (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
          U V s x‖⁻¹) ∂packetAtomRowsLaw W μ
        ∂endpointBlockPairLaw W μ) ≤
      packetProposition1010WLogConstant (max 1 L) z * oneSiteWLogScale W := by
  exact proposition_10_10_packet_reset hμ.normalized W hW r z U V s

theorem planar_physicalPacketCoefficient_ne_zero_ae
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1))
    (U V : unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : powersetCard (Fin W ⊕ Fin W) r.1) :
    ∀ᵐ x ∂intervalRowsLaw W 3 μ, physicalPacketCoefficient W z r U V s x ≠ 0 := by
  exact physicalPacketCoefficient_ne_zero_ae hμ.normalized W hW z r U V s

theorem planar_physicalPacketResetLoss_integrable
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1))
    (U V : unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : powersetCard (Fin W ⊕ Fin W) r.1) :
    Integrable (physicalPacketResetLoss W z r U V s) (intervalRowsLaw W 3 μ) := by
  exact physicalPacketResetLoss_integrable hμ.normalized W hW z r U V s

theorem planar_physicalPacketResetLoss_integral_le
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1))
    (U V : unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : powersetCard (Fin W ⊕ Fin W) r.1) :
    (∫ x, physicalPacketResetLoss W z r U V s x ∂intervalRowsLaw W 3 μ) ≤
      physicalPacketResetConstant (max 1 L) z * W * densityLogScale W := by
  exact physicalPacketResetLoss_integral_le hμ.normalized W hW z r U V s

theorem planar_intervalPressure_reset_increment
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    (W p q : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1)) :
    |intervalPressure μ W (q + 3 + p) z r -
      (intervalPressure μ W p z r + intervalPressure μ W q z r)| ≤
        densityCellMeanErrorConstant (max 1 L) z * W * densityLogScale W := by
  exact intervalPressure_reset_increment hμ.normalized W p q hW z r

theorem planar_cyclicPressure_normalized_L1_bound
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫ x, |densityCyclicLogDet W s z x / (((s + 3) * W : ℕ) : ℝ) -
      intervalMaxPressure μ W s z / (((s + 3) * W : ℕ) : ℝ)|
        ∂intervalRowsLaw W (s + 3) μ) ≤
      cyclicPressureErrorBound (max 1 L) W s z / (((s + 3) * W : ℕ) : ℝ) := by
  exact cyclicPressure_normalized_L1_bound hμ.normalized W s hW z

end BernoulliSection10Complex
