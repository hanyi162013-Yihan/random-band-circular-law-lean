import BernoulliSection10.SeamComparison
import BernoulliSection10Complex.PacketTensorReverse
import BernoulliSection10Complex.PacketReset

/-!
# Proposition 10.7: the periodic seam

For fixed outside data, this module integrates over the nine packet blocks:
the seven polynomial blocks and the two endpoint blocks.  The Floquet sign
does not appear because its complex norm is one.
-/

open scoped BigOperators Matrix ENNReal NNReal
open MeasureTheory

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open Matrix
open BernoulliLinearAlgebra

set_option maxHeartbeats 800000

local instance seamProbabilitySumLinearOrder (W : ℕ) :
    LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W ↦ (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h ↦ toLex.injective h)

def packetTensorNormComparisonCost (W : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.posLog (packetTensorEvaluationFactor W)) +
    ENNReal.ofReal (Real.posLog (packetTensorReverseFactor W))

theorem packetTensorNormComparisonCost_le_W_log_eW
    (W : ℕ) (hW : 0 < W) :
    packetTensorNormComparisonCost W ≤
      (ENNReal.ofReal packetTensorLogConstant +
        ENNReal.ofReal packetTensorReverseLogConstant) *
          oneSiteWLogScale W := by
  have hforward := ENNReal.ofReal_le_ofReal
    (posLog_packetTensorEvaluationFactor_le_W_log_eW W hW)
  rw [show packetTensorLogConstant * (W : ℝ) *
      Real.log (Real.exp 1 * W) = packetTensorLogConstant *
        ((W : ℝ) * Real.log (Real.exp 1 * W)) by ring,
    ENNReal.ofReal_mul packetTensorLogConstant_nonneg] at hforward
  have hreverse := ENNReal.ofReal_le_ofReal
    (posLog_packetTensorReverseFactor_le_W_log_eW W hW)
  rw [show packetTensorReverseLogConstant * (W : ℝ) *
      Real.log (Real.exp 1 * W) = packetTensorReverseLogConstant *
        ((W : ℝ) * Real.log (Real.exp 1 * W)) by ring,
    ENNReal.ofReal_mul packetTensorReverseLogConstant_nonneg] at hreverse
  unfold packetTensorNormComparisonCost
  rw [add_mul]
  exact add_le_add hforward hreverse

theorem seamExteriorCost_le_W_log_eW (W : ℕ) (hW : 0 < W) :
    ENNReal.ofReal ((W : ℝ) * Real.log 2) ≤
      ENNReal.ofReal (Real.posLog 2) * oneSiteWLogScale W := by
  have hlog2 : Real.log (2 : ℝ) = Real.posLog 2 := by
    rw [Real.posLog_eq_log (by norm_num)]
  have hscale : 1 ≤ Real.log (Real.exp 1 * W) := by
    rw [← one_add_posLog_nat_eq_log_e_mul W hW]
    exact le_add_of_nonneg_right Real.posLog_nonneg
  have hreal : (W : ℝ) * Real.log 2 ≤
      Real.posLog 2 * ((W : ℝ) * Real.log (Real.exp 1 * W)) := by
    rw [hlog2]
    have hnonneg : 0 ≤ Real.posLog 2 * (W : ℝ) :=
      mul_nonneg Real.posLog_nonneg (by positivity)
    calc
      (W : ℝ) * Real.posLog 2 = Real.posLog 2 * W * 1 := by ring
      _ ≤ Real.posLog 2 * W * Real.log (Real.exp 1 * W) :=
        mul_le_mul_of_nonneg_left hscale hnonneg
      _ = _ := by ring
  have h := ENNReal.ofReal_le_ofReal hreal
  unfold oneSiteWLogScale
  rw [ENNReal.ofReal_mul Real.posLog_nonneg] at h
  exact h

/-- The fixed-endpoint packet estimate.  It is the conditional inner step
of Proposition 10.7, before the two endpoint blocks are averaged. -/
theorem packetSeam_fixed_endpoints
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z c : ℂ) (hc : c ≠ 0)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hR : IsUnit R.det) :
    (∫⁻ x, ENNReal.ofReal
        |Real.log ‖c * packetBoundaryEval W z CL BR R x‖ -
          outsideExteriorPressure c R|
        ∂packetAtomRowsLaw W μ) ≤
      multiAffineLogCost L
          (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) +
        packetTensorNormComparisonCost W +
        ENNReal.ofReal ((W : ℝ) * Real.log 2) +
        ENNReal.ofReal
          |Real.log (packetBoundaryCoefficientNorm z CL BR R) -
            Real.log (gramVolume R)| := by
  letI := hμ.toIsProbabilityMeasure
  let m := packetAtomRowsLaw W μ
  let T := ‖packetBoundaryCoefficientTensor W z CL BR R‖
  let C := packetBoundaryCoefficientNorm z CL BR R
  let K : ℝ≥0∞ := packetTensorNormComparisonCost W +
    ENNReal.ofReal ((W : ℝ) * Real.log 2) +
      ENNReal.ofReal |Real.log C - Real.log (gramVolume R)|
  haveI : IsProbabilityMeasure m := by
    dsimp only [m, packetAtomRowsLaw]
    infer_instance
  have heval := proposition_10_9 hμ W hW z CL BR hCL hBR R hR
  have hC : 0 < C := by
    exact globalBoundaryCoefficientNorm_pos_fullyInstantiated
      z CL BR hCL hBR R hR
  have hFC := packetBoundaryCoefficientNorm_le_evaluationFactor_mul_tensor
    W hW z CL BR R
  have hT : 0 < T := by
    by_contra h
    have hzT : T = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    have hbound : C ≤ packetTensorEvaluationFactor W * T := by
      simpa only [C, T] using hFC
    rw [hzT, mul_zero] at hbound
    exact (not_le_of_gt hC) hbound
  have hTensorRaw := abs_log_packetBoundaryCoefficientTensor_sub_raw_le
    W hW z CL BR hCL hBR R hR
  have hGramGrowth :=
    abs_log_gramVolume_sub_log_maxExteriorOperatorGrowth_le R
  have hpoint : ∀ᵐ x ∂m,
      ENNReal.ofReal
          |Real.log ‖c * packetBoundaryEval W z CL BR R x‖ -
            outsideExteriorPressure c R| ≤
        ENNReal.ofReal
          |Real.log ‖packetBoundaryEval W z CL BR R x‖ - Real.log T| +
          K := by
    filter_upwards [heval.2] with x hx
    have hxpos : 0 < ‖packetBoundaryEval W z CL BR R x‖ :=
      norm_pos_iff.mpr hx
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hCoeffGram :
        |Real.log T - Real.log (gramVolume R)| ≤
          (Real.posLog (packetTensorEvaluationFactor W) +
            Real.posLog (packetTensorReverseFactor W)) +
          |Real.log C - Real.log (gramVolume R)| := by
      calc
        |Real.log T - Real.log (gramVolume R)| =
            |(Real.log T - Real.log C) +
              (Real.log C - Real.log (gramVolume R))| := by ring_nf
        _ ≤ |Real.log T - Real.log C| +
            |Real.log C - Real.log (gramVolume R)| := abs_add_le _ _
        _ ≤ _ := add_le_add hTensorRaw le_rfl
    have hGramGrowth' :
        |Real.log (gramVolume R) -
          Real.log (maxExteriorOperatorGrowth R)| ≤
            (W : ℝ) * Real.log 2 := by
      simpa only [Fintype.card_fin] using hGramGrowth
    have hreal := seam_log_triangle
      (c := ‖c‖) (eval := ‖packetBoundaryEval W z CL BR R x‖)
      (coeff := T) (gram := gramVolume R)
      (growth := maxExteriorOperatorGrowth R)
      (A := |Real.log ‖packetBoundaryEval W z CL BR R x‖ - Real.log T|)
      (B := (Real.posLog (packetTensorEvaluationFactor W) +
          Real.posLog (packetTensorReverseFactor W)) +
        |Real.log C - Real.log (gramVolume R)|)
      (C := (W : ℝ) * Real.log 2)
      hcpos hxpos hT (gramVolume_pos R)
      (maxExteriorOperatorGrowth_pos_twoBlock R)
      le_rfl hCoeffGram hGramGrowth'
    have hreal' :
        |Real.log ‖c * packetBoundaryEval W z CL BR R x‖ -
            outsideExteriorPressure c R| ≤
          |Real.log ‖packetBoundaryEval W z CL BR R x‖ - Real.log T| +
          ((Real.posLog (packetTensorEvaluationFactor W) +
              Real.posLog (packetTensorReverseFactor W)) +
            (W : ℝ) * Real.log 2 +
            |Real.log C - Real.log (gramVolume R)|) := by
      calc
        |Real.log ‖c * packetBoundaryEval W z CL BR R x‖ -
            outsideExteriorPressure c R| ≤
          |Real.log ‖packetBoundaryEval W z CL BR R x‖ - Real.log T| +
            (((Real.posLog (packetTensorEvaluationFactor W) +
                Real.posLog (packetTensorReverseFactor W)) +
              |Real.log C - Real.log (gramVolume R)|) +
              (W : ℝ) * Real.log 2) := by
          simpa only [norm_mul, outsideExteriorPressure, add_assoc] using hreal
        _ = _ := by ring
    calc
      ENNReal.ofReal
          |Real.log ‖c * packetBoundaryEval W z CL BR R x‖ -
            outsideExteriorPressure c R| ≤
          ENNReal.ofReal
            (|Real.log ‖packetBoundaryEval W z CL BR R x‖ - Real.log T| +
              ((Real.posLog (packetTensorEvaluationFactor W) +
                  Real.posLog (packetTensorReverseFactor W)) +
                (W : ℝ) * Real.log 2 +
                |Real.log C - Real.log (gramVolume R)|)) :=
        ENNReal.ofReal_le_ofReal hreal'
      _ = ENNReal.ofReal
          |Real.log ‖packetBoundaryEval W z CL BR R x‖ - Real.log T| +
          K := by
        rw [ENNReal.ofReal_add (abs_nonneg _)
          (add_nonneg
            (add_nonneg
              (add_nonneg Real.posLog_nonneg Real.posLog_nonneg)
              (mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))))
            (abs_nonneg _))]
        rw [show
          (Real.posLog (packetTensorEvaluationFactor W) +
              Real.posLog (packetTensorReverseFactor W)) +
              (W : ℝ) * Real.log 2 +
              |Real.log C - Real.log (gramVolume R)| =
            (Real.posLog (packetTensorEvaluationFactor W) +
              Real.posLog (packetTensorReverseFactor W)) +
            ((W : ℝ) * Real.log 2 +
              |Real.log C - Real.log (gramVolume R)|) by ring,
          ENNReal.ofReal_add
            (add_nonneg Real.posLog_nonneg Real.posLog_nonneg)
            (add_nonneg
              (mul_nonneg (by positivity) (Real.log_nonneg (by norm_num)))
              (abs_nonneg _)),
          ENNReal.ofReal_add Real.posLog_nonneg Real.posLog_nonneg,
          ENNReal.ofReal_add
            (mul_nonneg (by positivity) (Real.log_nonneg (by norm_num)))
            (abs_nonneg _)]
        simp only [K, packetTensorNormComparisonCost, C, add_assoc]
  calc
    (∫⁻ x, ENNReal.ofReal
        |Real.log ‖c * packetBoundaryEval W z CL BR R x‖ -
          outsideExteriorPressure c R| ∂m) ≤
        ∫⁻ x, ENNReal.ofReal
          |Real.log ‖packetBoundaryEval W z CL BR R x‖ - Real.log T| + K
          ∂m := lintegral_mono_ae hpoint
    _ = (∫⁻ x, ENNReal.ofReal
          |Real.log ‖packetBoundaryEval W z CL BR R x‖ - Real.log T| ∂m) +
        K := by
      rw [lintegral_add_right _ measurable_const]
      simp
    _ ≤ multiAffineLogCost L
          (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) +
        K := by
      exact add_le_add (by simpa only [T, m] using heval.1) le_rfl
    _ = _ := by
      simp only [K, C, add_assoc]

/-- One explicit choice of the manuscript constant in Proposition 10.7. -/
def packetProposition107WLogConstant (L : ℝ) (z : ℂ) : ℝ≥0∞ :=
  3 * ENNReal.ofReal (oneSiteRowLogConstant L) +
    (ENNReal.ofReal packetTensorLogConstant +
      ENNReal.ofReal packetTensorReverseLogConstant) +
    ENNReal.ofReal (Real.posLog 2) +
    packetProposition108WLogConstant L z

/-- Proposition 10.7 in conditional form: `c` and `R` are the fixed
outside scalar and outside transfer after conditioning on the complementary
arc; both are exactly the outside objects appearing in the manuscript. -/
theorem proposition_10_7_periodic_seam
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z c : ℂ) (hc : c ≠ 0)
    (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hR : IsUnit R.det) :
    (∫⁻ ep, ∫⁻ x, ENNReal.ofReal
        |Real.log ‖c * packetBoundaryEval W z
            (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
            R x‖ - outsideExteriorPressure c R|
          ∂packetAtomRowsLaw W μ ∂endpointBlockPairLaw W μ) ≤
      packetProposition107WLogConstant L z * oneSiteWLogScale W := by
  letI := hμ.toIsProbabilityMeasure
  let m := endpointBlockPairLaw W μ
  let Q : ℝ≥0∞ :=
    multiAffineLogCost L
        (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) +
      packetTensorNormComparisonCost W +
      ENNReal.ofReal ((W : ℝ) * Real.log 2)
  let g : EndpointBlockPair W → ℝ≥0∞ := fun ep ↦
    ENNReal.ofReal
      |Real.log (packetBoundaryCoefficientNorm z
          (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2) R) -
        Real.log (gramVolume R)|
  haveI : IsProbabilityMeasure m := by
    dsimp only [m, endpointBlockPairLaw, blockAtomRowsLaw]
    infer_instance
  have hunit := normalizedEndpointFactor_det_isUnit_ae hμ W hW
  have hpoint : ∀ᵐ ep ∂m,
      (∫⁻ x, ENNReal.ofReal
        |Real.log ‖c * packetBoundaryEval W z
            (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
            R x‖ - outsideExteriorPressure c R|
          ∂packetAtomRowsLaw W μ) ≤ Q + g ep := by
    filter_upwards [hunit] with ep hep
    have hprod : IsUnit
        (normalizedBlockDet W ep.1 * normalizedBlockDet W ep.2) := by
      simpa only [normalizedEndpointFactor_det] using hep
    have hparts := mul_ne_zero_iff.mp (isUnit_iff_ne_zero.mp hprod)
    have hCL : IsUnit (normalizedBlockMatrix W ep.1).det :=
      isUnit_iff_ne_zero.mpr hparts.1
    have hBR : IsUnit (normalizedBlockMatrix W ep.2).det :=
      isUnit_iff_ne_zero.mpr hparts.2
    simpa only [Q, g, add_assoc] using packetSeam_fixed_endpoints
      hμ W hW z c hc (normalizedBlockMatrix W ep.1)
        (normalizedBlockMatrix W ep.2) hCL hBR R hR
  have hrows := packetThreeRowCost_le_W_log_eW L W hW
  have hscale := packetTensorNormComparisonCost_le_W_log_eW W hW
  have hseam := seamExteriorCost_le_W_log_eW W hW
  have hgram := proposition_10_8_integrated_endpoint_comparison
    hμ W hW z R hR
  rw [← log_gramVolume_eq_half_log_gramEnergy R] at hgram
  calc
    (∫⁻ ep, ∫⁻ x, ENNReal.ofReal
        |Real.log ‖c * packetBoundaryEval W z
            (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
            R x‖ - outsideExteriorPressure c R|
          ∂packetAtomRowsLaw W μ ∂m) ≤
        ∫⁻ ep, Q + g ep ∂m := lintegral_mono_ae hpoint
    _ = Q + ∫⁻ ep, g ep ∂m := by
      rw [lintegral_add_left measurable_const]
      simp
    _ ≤ (3 * ENNReal.ofReal (oneSiteRowLogConstant L) +
          (ENNReal.ofReal packetTensorLogConstant +
            ENNReal.ofReal packetTensorReverseLogConstant) +
          ENNReal.ofReal (Real.posLog 2)) * oneSiteWLogScale W +
        packetProposition108WLogConstant L z * oneSiteWLogScale W := by
      apply add_le_add
      · simpa only [Q, add_mul, add_assoc] using
          add_le_add (add_le_add hrows hscale) hseam
      · simpa only [g, m] using hgram
    _ = packetProposition107WLogConstant L z * oneSiteWLogScale W := by
      unfold packetProposition107WLogConstant
      ring

end BernoulliSection10Complex
