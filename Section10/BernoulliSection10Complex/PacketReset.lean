import BernoulliSection10Complex.PacketFrameProbability
import BernoulliSection10Complex.PacketTensorScaling

/-!
# The packet reset estimate

This module closes Proposition 10.10.  It first integrates the inverse norm of
the concrete normalized coefficient tensor over the two endpoint blocks and
then combines that estimate with Corollary 10.3 for the `3W` packet rows.
-/

open scoped BigOperators Matrix ENNReal NNReal
open MeasureTheory

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open Matrix
open BernoulliLinearAlgebra

set_option maxHeartbeats 800000

local instance packetResetSumLinearOrder (W : ℕ) :
    LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W ↦ (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h ↦ toLex.injective h)

/-- The endpoint part of the `W log(eW)` constant in Proposition 10.10. -/
def packetTensorEndpointWLogConstant (L : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal packetTensorLogConstant +
    ENNReal.ofReal (packetDeterministicLogConstant z) +
      endpointExteriorWLogConstant L

/-- After the endpoint blocks have been sampled, the inverse norm of the
literal normalized packet coefficient tensor has integrable logarithmic
loss of order `W log(eW)`.  Endpoint nonsingularity is discharged almost
surely from the concrete determinant polynomials. -/
theorem packetScalarCoefficientTensor_posLog_inv_lintegral_le_W_log_eW
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (r : ℕ) (z : ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    (∫⁻ x, ENNReal.ofReal (Real.posLog
        ‖packetScalarCoefficientTensor W r z
          (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)
          U V s‖⁻¹) ∂endpointBlockPairLaw W μ) ≤
      packetTensorEndpointWLogConstant L z * oneSiteWLogScale W := by
  letI := hμ.toIsProbabilityMeasure
  let m := endpointBlockPairLaw W μ
  let f : ℝ≥0∞ := ENNReal.ofReal
    (Real.posLog (packetTensorEvaluationFactor W))
  let c : ℝ≥0∞ := ENNReal.ofReal
    (Real.log (threeBlockConcreteComparisonConstant (W := Fin W) z))
  let g : EndpointBlockPair W → ℝ≥0∞ := fun x ↦
    ENNReal.ofReal (Real.log (exactExteriorConditioningConstant
      (normalizedEndpointFactor W x)))
  haveI : IsProbabilityMeasure m := by
    dsimp only [m, endpointBlockPairLaw, blockAtomRowsLaw]
    infer_instance
  have hunit := normalizedEndpointFactor_det_isUnit_ae hμ W hW
  have hpoint : ∀ᵐ x ∂m,
      ENNReal.ofReal (Real.posLog
          ‖packetScalarCoefficientTensor W r z
            (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)
            U V s‖⁻¹) ≤
        f + c + g x := by
    filter_upwards [hunit] with x hx
    have hprod : IsUnit
        (normalizedBlockDet W x.1 * normalizedBlockDet W x.2) := by
      simpa only [normalizedEndpointFactor_det] using hx
    have hprodNe : normalizedBlockDet W x.1 * normalizedBlockDet W x.2 ≠ 0 :=
      isUnit_iff_ne_zero.mp hprod
    have hparts := mul_ne_zero_iff.mp hprodNe
    have hCL : IsUnit (normalizedBlockMatrix W x.1).det := by
      exact isUnit_iff_ne_zero.mpr hparts.1
    have hBR : IsUnit (normalizedBlockMatrix W x.2).det := by
      exact isUnit_iff_ne_zero.mpr hparts.2
    have htensor := posLog_inv_packetScalarCoefficientTensor_le
      W hW r z (normalizedBlockMatrix W x.1)
        (normalizedBlockMatrix W x.2) hCL hBR U V s
    have hthreeOne : 1 ≤
        threeBlockConcreteComparisonConstant (W := Fin W) z :=
      one_le_threeBlockConcreteComparisonConstant (W := Fin W) z
    have hextOne : 1 ≤ exactExteriorConditioningConstant
        (normalizedEndpointFactor W x) :=
      one_le_exactExteriorConditioningConstant _
    have hthreePos : 0 <
        threeBlockConcreteComparisonConstant (W := Fin W) z :=
      zero_lt_one.trans_le hthreeOne
    have hextPos : 0 < exactExteriorConditioningConstant
        (normalizedEndpointFactor W x) := zero_lt_one.trans_le hextOne
    have hKPosLog : Real.posLog (packetEndpointComparisonConstant z
          (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)) =
        Real.log (packetEndpointComparisonConstant z
          (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)) := by
      apply Real.posLog_eq_log
      rw [abs_of_nonneg (packetEndpointComparisonConstant_pos z
        (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)).le]
      exact one_le_packetEndpointComparisonConstant z
        (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)
    have hsplit : Real.log (packetEndpointComparisonConstant z
          (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)) =
        Real.log (threeBlockConcreteComparisonConstant (W := Fin W) z) +
          Real.log (exactExteriorConditioningConstant
            (normalizedEndpointFactor W x)) := by
      have hextPos' : 0 < exactExteriorConditioningConstant
          (endpointFactor (normalizedBlockMatrix W x.1)
            (normalizedBlockMatrix W x.2)) := by
        simpa only [normalizedEndpointFactor] using hextPos
      unfold packetEndpointComparisonConstant endpointExteriorConstant
        normalizedEndpointFactor
      exact Real.log_mul hthreePos.ne' hextPos'.ne'
    calc
      ENNReal.ofReal (Real.posLog
          ‖packetScalarCoefficientTensor W r z
            (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)
            U V s‖⁻¹) ≤
          ENNReal.ofReal
            (Real.posLog (packetTensorEvaluationFactor W) +
              Real.posLog (packetEndpointComparisonConstant z
                (normalizedBlockMatrix W x.1)
                (normalizedBlockMatrix W x.2))) :=
        ENNReal.ofReal_le_ofReal htensor
      _ = f + c + g x := by
        rw [hKPosLog, hsplit,
          ENNReal.ofReal_add Real.posLog_nonneg
            (add_nonneg (Real.log_nonneg hthreeOne)
              (Real.log_nonneg hextOne)),
          ENNReal.ofReal_add (Real.log_nonneg hthreeOne)
            (Real.log_nonneg hextOne)]
        simp only [f, c, g, add_assoc]
  have hfactor : f ≤ ENNReal.ofReal packetTensorLogConstant *
      oneSiteWLogScale W := by
    have h := ENNReal.ofReal_le_ofReal
      (posLog_packetTensorEvaluationFactor_le_W_log_eW W hW)
    rw [show packetTensorLogConstant * (W : ℝ) *
        Real.log (Real.exp 1 * W) = packetTensorLogConstant *
          ((W : ℝ) * Real.log (Real.exp 1 * W)) by ring,
      ENNReal.ofReal_mul packetTensorLogConstant_nonneg] at h
    exact h
  have hdeterministic : c ≤
      ENNReal.ofReal (packetDeterministicLogConstant z) *
        oneSiteWLogScale W := by
    have h := ENNReal.ofReal_le_ofReal
      (log_threeBlockConcreteComparisonConstant_fin_le_W_log_eW W hW z)
    rw [show packetDeterministicLogConstant z * (W : ℝ) *
        Real.log (Real.exp 1 * W) = packetDeterministicLogConstant z *
          ((W : ℝ) * Real.log (Real.exp 1 * W)) by ring,
      ENNReal.ofReal_mul (packetDeterministicLogConstant_nonneg z)] at h
    exact h
  have hexterior := endpointExteriorConstant_log_lintegral_le_W_log_eW
    hμ W hW
  calc
    (∫⁻ x, ENNReal.ofReal (Real.posLog
        ‖packetScalarCoefficientTensor W r z
          (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)
          U V s‖⁻¹) ∂m) ≤
        ∫⁻ x, (f + c) + g x ∂m := by
      apply lintegral_mono_ae
      filter_upwards [hpoint] with x hx
      simpa only [add_assoc] using hx
    _ = (f + c) + ∫⁻ x, g x ∂m := by
      rw [lintegral_add_left measurable_const]
      simp
    _ ≤ (ENNReal.ofReal packetTensorLogConstant +
          ENNReal.ofReal (packetDeterministicLogConstant z)) *
          oneSiteWLogScale W +
        endpointExteriorWLogConstant L * oneSiteWLogScale W := by
      exact add_le_add
        (by rw [add_mul]; exact add_le_add hfactor hdeterministic)
        (by simpa only [g, m] using hexterior)
    _ = packetTensorEndpointWLogConstant L z * oneSiteWLogScale W := by
      unfold packetTensorEndpointWLogConstant
      rw [add_mul, add_mul]
      ring

/-- The complete constant in the caller-facing packet reset estimate. -/
def packetProposition1010WLogConstant (L : ℝ) (z : ℂ) : ℝ≥0∞ :=
  3 * ENNReal.ofReal (oneSiteRowLogConstant L) +
    packetTensorEndpointWLogConstant L z

/-- Proposition 10.10 in its literal iterated-expectation form.  The inner
integral samples the `3W` normalized packet rows and the outer integral
samples the two independent endpoint blocks.  The only inputs are the
paper's density hypothesis and its concrete deterministic frame data. -/
theorem proposition_10_10_packet_reset
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (r : ℕ) (z : ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    (∫⁻ ep, ∫⁻ x, ENNReal.ofReal (Real.posLog
        ‖packetScalarCoefficientEval W r z
          (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
          U V s x‖⁻¹) ∂packetAtomRowsLaw W μ
        ∂endpointBlockPairLaw W μ) ≤
      packetProposition1010WLogConstant L z * oneSiteWLogScale W := by
  letI := hμ.toIsProbabilityMeasure
  let m := endpointBlockPairLaw W μ
  let R : ℝ≥0∞ := multiAffineLogCost L
    (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W))
  let T : EndpointBlockPair W → ℝ≥0∞ := fun ep ↦
    ENNReal.ofReal (Real.posLog
      ‖packetScalarCoefficientTensor W r z
        (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
        U V s‖⁻¹)
  haveI : IsProbabilityMeasure m := by
    dsimp only [m, endpointBlockPairLaw, blockAtomRowsLaw]
    infer_instance
  have hunit := normalizedEndpointFactor_det_isUnit_ae hμ W hW
  have hpoint : ∀ᵐ ep ∂m,
      (∫⁻ x, ENNReal.ofReal (Real.posLog
          ‖packetScalarCoefficientEval W r z
            (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
            U V s x‖⁻¹) ∂packetAtomRowsLaw W μ) ≤
        R + T ep := by
    filter_upwards [hunit] with ep hep
    have hprod : IsUnit
        (normalizedBlockDet W ep.1 * normalizedBlockDet W ep.2) := by
      simpa only [normalizedEndpointFactor_det] using hep
    have hparts := mul_ne_zero_iff.mp (isUnit_iff_ne_zero.mp hprod)
    have hCL : IsUnit (normalizedBlockMatrix W ep.1).det :=
      isUnit_iff_ne_zero.mpr hparts.1
    have hBR : IsUnit (normalizedBlockMatrix W ep.2).det :=
      isUnit_iff_ne_zero.mpr hparts.2
    simpa only [R, T] using proposition_10_10_log_inv_le_tensor_loss
      hμ W hW r z (normalizedBlockMatrix W ep.1)
        (normalizedBlockMatrix W ep.2) hCL hBR U V s
  have hrows := packetThreeRowCost_le_W_log_eW L W hW
  have htensor :=
    packetScalarCoefficientTensor_posLog_inv_lintegral_le_W_log_eW
      hμ W hW r z U V s
  calc
    (∫⁻ ep, ∫⁻ x, ENNReal.ofReal (Real.posLog
        ‖packetScalarCoefficientEval W r z
          (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
          U V s x‖⁻¹) ∂packetAtomRowsLaw W μ ∂m) ≤
        ∫⁻ ep, R + T ep ∂m := lintegral_mono_ae hpoint
    _ = R + ∫⁻ ep, T ep ∂m := by
      rw [lintegral_add_left measurable_const]
      simp
    _ ≤ 3 * ENNReal.ofReal (oneSiteRowLogConstant L) *
          oneSiteWLogScale W +
        packetTensorEndpointWLogConstant L z * oneSiteWLogScale W :=
      add_le_add (by simpa only [R] using hrows)
        (by simpa only [T, m] using htensor)
    _ = packetProposition1010WLogConstant L z * oneSiteWLogScale W := by
      unfold packetProposition1010WLogConstant
      rw [add_mul]

end BernoulliSection10Complex
