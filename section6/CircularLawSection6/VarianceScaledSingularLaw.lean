import CircularLawSection6.HardEdgeScaling
import CircularLawSection6.GinibreLimitingLogPotential
import CircularLawSection6.FixedScaleCoreBridge

/-! # Variance-scaled limiting singular laws

The variance-v law is the explicit pushforward by multiplication by sqrt(v).
Its hard-edge and cutoff constants are uniform for v >= 1/4. The logarithmic
potential is identified from the actual Ginibre sources after transporting the
almost-everywhere spectral parameter; no uncountable intersection is used.
-/

open MeasureTheory Set Filter Topology
open CircularLawSections56.Section5 CircularLawSections56.Section6
noncomputable section
set_option autoImplicit false

namespace CircularLawSection6

def varianceScaledSingularLaw (v : ℝ) (σ : Measure ℝ) : Measure ℝ :=
  scaledSingularLaw (Real.sqrt v) σ

instance varianceScaledSingularLaw_isProbability (v : ℝ) (σ : Measure ℝ)
    [IsProbabilityMeasure σ] : IsProbabilityMeasure (varianceScaledSingularLaw v σ) :=
  scaledSingularLaw_isProbability _ _

theorem sqrt_ge_half_of_variance_ge_quarter {v : ℝ} (hv : (1 / 4 : ℝ) ≤ v) :
    (1 / 2 : ℝ) ≤ Real.sqrt v := by
  have hv0 : 0 ≤ v := by linarith
  nlinarith [Real.sq_sqrt hv0, Real.sqrt_nonneg v]

theorem varianceScaledSingularLaw_uniformHardEdge (σ : Measure ℝ)
    (hCDF : ∀ t, 0 < t → σ.real (Iic t) ≤ 2 * t)
    {v : ℝ} (hv : (1 / 4 : ℝ) ≤ v) :
    ∀ t, 0 < t → (varianceScaledSingularLaw v σ).real (Iic t) ≤ 4 * t := by
  simpa only [varianceScaledSingularLaw, show (2 : ℝ) / (1 / 2) = 4 by norm_num] using
    scaledSingularLaw_uniformHardEdge σ (by norm_num : (0 : ℝ) < 1 / 2)
      (sqrt_ge_half_of_variance_ge_quarter hv) (by norm_num : (0 : ℝ) ≤ 2) hCDF

theorem varianceScaledSingularLaw_uniformLogCutoff (σ : Measure ℝ)
    [IsProbabilityMeasure σ] (hsecond : Integrable (fun s : ℝ => s ^ 2) σ)
    (hCDF : ∀ t, 0 < t → σ.real (Iic t) ≤ 2 * t)
    {v a : ℝ} (hv : (1 / 4 : ℝ) ≤ v) (ha : 0 < a) :
    0 ≤ (∫ s, Real.log (max s a) ∂varianceScaledSingularLaw v σ) -
      (∫ s, Real.log s ∂varianceScaledSingularLaw v σ) ∧
    (∫ s, Real.log (max s a) ∂varianceScaledSingularLaw v σ) -
      (∫ s, Real.log s ∂varianceScaledSingularLaw v σ) ≤ 4 * a := by
  simpa only [varianceScaledSingularLaw, show (2 : ℝ) / (1 / 2) = 4 by norm_num] using
    scaledSingularLaw_logCutoff_error σ hsecond (by norm_num : (0 : ℝ) < 1 / 2)
      (sqrt_ge_half_of_variance_ge_quarter hv) (by norm_num : (0 : ℝ) ≤ 2) hCDF ha

theorem varianceScaledSingularLaw_logPotential (σ : Measure ℝ) [IsProbabilityMeasure σ]
    {v : ℝ} (hv : 0 < v) (z : ℂ)
    (hpos : ∀ᵐ s ∂σ, 0 < s) (hlog : Integrable Real.log σ)
    (htarget : (∫ s, Real.log s ∂σ) = circularRadialPotential ‖z / (Real.sqrt v : ℂ)‖) :
    (∫ s, Real.log s ∂varianceScaledSingularLaw v σ) =
      varianceScaledRadialPotential v ‖z‖ := by
  rw [varianceScaledSingularLaw, scaledSingularLaw_log σ (Real.sqrt_pos.2 hv) hpos hlog,
    htarget, varianceScaledRadialPotential, Real.log_sqrt hv.le,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 hv)]
  ring

theorem ginibre_varianceScaled_logPotential_ae (M : ℕ → ℕ+)
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop) {v : ℝ} (hv : 0 < v) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ σ : Measure ℝ, IsProbabilityMeasure σ →
      (∀ᵐ s ∂σ, 0 ≤ s) → Integrable (fun s : ℝ => s ^ 2) σ →
      GinibreSquaredTestInput M (z / (Real.sqrt v : ℂ)) σ → ∀ comparisonConstant : ℝ,
      GinibreBBVInput M (z / (Real.sqrt v : ℂ)) comparisonConstant →
      TendstoInProbabilityTri (fun n => cyclicAtomLaw (M n) circularComplexGaussian)
        (fun n ω => matrixRawPotential (ginibreMatrix (M n) ω - (z / (Real.sqrt v : ℂ)) • 1))
        (circularRadialPotential ‖z / (Real.sqrt v : ℂ)‖) →
      ∀ p : ℝ, 0 < p →
        BC12GinibreNegativeMomentTightnessTri (fun n => (M n : ℕ)) (z / (Real.sqrt v : ℂ)) p →
        (∫ s, Real.log s ∂varianceScaledSingularLaw v σ) =
          varianceScaledRadialPotential v ‖z‖ := by
  filter_upwards [ae_div_real (Real.sqrt_pos.2 hv).ne'
    (ginibre_limiting_logPotential_eq_raw_limit_ae M hM)] with z hz
  intro σ hσ hpos hsecond hweak comparisonConstant hBBV hraw p hp hnegative
  let : IsProbabilityMeasure σ := hσ
  have hCDF := ginibre_limiting_linearHardEdge M hM (z / (Real.sqrt v : ℂ)) σ hpos hweak hBBV
  apply varianceScaledSingularLaw_logPotential σ hv z
    (hardEdge_positive_ae σ (a := 1) (by norm_num) (fun t ht _ => hCDF t ht))
    (ginibre_limiting_log_integrable M hM (z / (Real.sqrt v : ℂ)) σ hpos hsecond hweak hBBV)
  exact hz σ hσ hpos hsecond hweak comparisonConstant hBBV _ hraw p hp hnegative

end CircularLawSection6
