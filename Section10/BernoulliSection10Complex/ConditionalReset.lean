import BernoulliSection10Complex.PhysicalPacketReset
import BernoulliSection10Complex.ClearedSingularTest
import BernoulliSection10Complex.SandwichIntegrability
import BernoulliSection10Complex.IntervalMeanHodge

/-!
# Integrating the reset after freezing the core and the past

The singular frames are chosen only inside a fixed-fiber proof. The
resulting integrand is the actual matrix-product logarithm; no measurable
frame selection, decomposable-wedge certificate, or independence premise
is left to the caller.
-/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open BernoulliLinearAlgebra Matrix Set Set.powersetCard

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def resetSandwichDegreeLog (W p q : ℕ) (z : ℂ) (r : Fin (2 * W + 1))
    (core : IntervalRows W p) (past : IntervalRows W q) (reset : IntervalRows W 3) : ℝ :=
  Real.log ‖intervalClearedProduct W p z core r *
    intervalClearedProduct W 3 z reset r * intervalClearedProduct W q z past r‖

def densityCellMeanErrorConstant (L : ℝ) (z : ℂ) : ℝ :=
  physicalPacketResetConstant L z + 3 * remainderHodgeConstant L z

theorem densityCellMeanErrorConstant_nonneg (L : ℝ) (z : ℂ) :
    0 ≤ densityCellMeanErrorConstant L z := by
  unfold densityCellMeanErrorConstant
  exact add_nonneg (physicalPacketResetConstant_nonneg L z)
    (mul_nonneg (by norm_num) (remainderHodgeConstant_nonneg L z))

/-- The integrated, certificate-free form of (10.38)--(10.39). It is
slightly stronger than the recursive-wedge presentation: it controls the
operator norm of the whole past sandwich directly. -/
theorem resetSandwichDegreeLog_integral_bounds_ae
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W p q : ℕ) (hW : 0 < W) (z : ℂ) :
    ∀ᵐ core ∂intervalRowsLaw W p μ, ∀ᵐ past ∂intervalRowsLaw W q μ,
      ∀ r : Fin (2 * W + 1),
        intervalDegreeLog W p z r core + intervalDegreeLog W q z r past -
            densityCellMeanErrorConstant L z * W * densityLogScale W ≤
          ∫ reset, resetSandwichDegreeLog W p q z r core past reset
            ∂intervalRowsLaw W 3 μ ∧
        (∫ reset, resetSandwichDegreeLog W p q z r core past reset
            ∂intervalRowsLaw W 3 μ) ≤
          intervalDegreeLog W p z r core + intervalDegreeLog W q z r past +
            densityCellMeanErrorConstant L z * W * densityLogScale W := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W 3 μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  filter_upwards [intervalClearedProduct_det_isUnit_ae hμ W p hW z,
    interval_product_scalar_test_ae hμ W p q hW z] with core hc hs
  filter_upwards [intervalClearedProduct_det_isUnit_ae hμ W q hW z, hs] with past hp hs
  intro r
  letI : Nonempty (powersetCard (Fin W ⊕ Fin W) r.1) := by
    rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
    apply Nat.choose_pos
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  let A := intervalClearedProduct W p z core r
  let B := intervalClearedProduct W q z past r
  have hA : IsUnit A.det := hc r
  have hB : IsUnit B.det := hp r
  have hA0 : A ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).mpr hA).ne_zero
  have hB0 : B ≠ 0 := ((Matrix.isUnit_iff_isUnit_det B).mpr hB).ne_zero
  have hfi := fixed_interval_sandwich_log_integrable hμ W 3 hW z r A B hA hB
  have hscale : 0 ≤ (W : ℝ) * densityLogScale W :=
    mul_nonneg (Nat.cast_nonneg _) (densityLogScale_nonneg hW)
  have hreset : physicalPacketResetConstant L z ≤ densityCellMeanErrorConstant L z := by
    unfold densityCellMeanErrorConstant
    linarith [remainderHodgeConstant_nonneg L z]
  have hhodge : 3 * remainderHodgeConstant L z ≤ densityCellMeanErrorConstant L z := by
    unfold densityCellMeanErrorConstant
    linarith [physicalPacketResetConstant_nonneg L z]
  constructor
  · obtain ⟨U, V, s, htest⟩ := hs r
    have hli := physicalPacketResetLoss_integrable hμ W hW z r U V s
    have hpoint : ∀ᵐ reset ∂intervalRowsLaw W 3 μ,
        Real.log ‖A‖ + Real.log ‖B‖ - physicalPacketResetLoss W z r U V s reset ≤
          Real.log ‖A * intervalClearedProduct W 3 z reset r * B‖ := by
      filter_upwards [physicalPacketCoefficient_ne_zero_ae hμ W hW z r U V s] with reset hr
      exact log_product_lower_of_scalar_test (norm_pos_iff.mpr hA0)
        (norm_pos_iff.mpr hB0) (norm_pos_iff.mpr hr)
        (htest (intervalClearedProduct W 3 z reset r))
    have hle := integral_mono_ae ((integrable_const _).sub hli) hfi hpoint
    simp only [Pi.sub_apply] at hle
    rw [integral_sub (integrable_const _) hli, integral_const] at hle
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hle
    have hcost := (physicalPacketResetLoss_integral_le hμ W hW z r U V s).trans
      (show physicalPacketResetConstant L z * W * densityLogScale W ≤
        densityCellMeanErrorConstant L z * W * densityLogScale W by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hreset hscale)
    change Real.log ‖A‖ + Real.log ‖B‖ - _ ≤ _
    change _ ≤ ∫ reset, resetSandwichDegreeLog W p q z r core past reset
      ∂intervalRowsLaw W 3 μ at hle
    linarith only [hle, hcost]
  · have hqi := intervalDegreeLog_integrable hμ W 3 hW z r
    have hai : Integrable (fun x => Real.log ‖A‖ + intervalDegreeLog W 3 z r x)
        (intervalRowsLaw W 3 μ) := (integrable_const _).add hqi
    have hpoint : ∀ᵐ reset ∂intervalRowsLaw W 3 μ,
        Real.log ‖A * intervalClearedProduct W 3 z reset r * B‖ ≤
          Real.log ‖A‖ + intervalDegreeLog W 3 z r reset + Real.log ‖B‖ := by
      filter_upwards [intervalClearedProduct_det_isUnit_ae hμ W 3 hW z] with reset hr
      exact log_norm_sandwich_upper A _ B hA (hr r) hB
    have hle := integral_mono_ae hfi (((integrable_const _).add hqi).add
      (integrable_const _)) hpoint
    simp only [Pi.add_apply] at hle
    rw [integral_add hai (integrable_const (Real.log ‖B‖)),
      integral_add (integrable_const _) hqi, integral_const, integral_const] at hle
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hle
    have hcost := (le_abs_self (intervalPressure μ W 3 z r)).trans
      ((abs_intervalPressure_le hμ W 3 hW z r).trans
        (show (3 : ℝ) * remainderHodgeConstant L z * W * densityLogScale W ≤
          densityCellMeanErrorConstant L z * W * densityLogScale W by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hhodge hscale))
    change (∫ reset, resetSandwichDegreeLog W p q z r core past reset
      ∂intervalRowsLaw W 3 μ) ≤ _ at hle
    change _ ≤ Real.log ‖A‖ + Real.log ‖B‖ + _
    change (∫ reset, intervalDegreeLog W 3 z r reset ∂intervalRowsLaw W 3 μ) ≤ _ at hcost
    linarith only [hle, hcost]

end BernoulliSection10Complex

