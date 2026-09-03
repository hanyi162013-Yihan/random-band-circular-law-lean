import CircularLawSection6.HardEdgeLogIdentity
import CircularLawSection6.ClippedCutoffTail

/-! # Removing the logarithmic cutoff from second moments and a linear hard edge

The second moment controls the upper tail; the hard edge controls the lower
tail. Thus neither integrability of the full logarithm nor convergence of its
cutoffs is an independent premise.
-/

open MeasureTheory Set Filter Topology
noncomputable section

namespace CircularLawSection6

theorem integrable_logCutoff_of_secondMoment (σ : Measure ℝ) [IsFiniteMeasure σ]
    (hpos : ∀ᵐ s ∂σ, 0 ≤ s) (hsecond : Integrable (fun s : ℝ => s ^ 2) σ)
    {a : ℝ} (ha : 0 < a) : Integrable (fun s => Real.log (max s a)) σ :=
  (expected_cutoffLog_clipped_error σ id measurable_id hpos hsecond ha
    (le_max_left a 1) (le_max_right a 1)).1

theorem integrable_log_of_hardEdge_secondMoment (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a₀ C : ℝ} (ha₀ : 0 < a₀) (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → t ≤ a₀ → σ.real (Iic t) ≤ C * t)
    (hsecond : Integrable (fun s : ℝ => s ^ 2) σ) : Integrable Real.log σ := by
  have hpos := (hardEdge_positive_ae σ ha₀ hCDF).mono fun _ hs => hs.le
  exact integrable_log_of_hardEdge σ ha₀ hC hCDF
    (integrable_logCutoff_of_secondMoment σ hpos hsecond ha₀)

theorem logCutoff_error_of_hardEdge_secondMoment (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a₀ C : ℝ} (ha₀ : 0 < a₀) (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → t ≤ a₀ → σ.real (Iic t) ≤ C * t)
    (hsecond : Integrable (fun s : ℝ => s ^ 2) σ)
    {a : ℝ} (ha : 0 < a) (haa₀ : a ≤ a₀) :
    0 ≤ (∫ s, Real.log (max s a) ∂σ) - (∫ s, Real.log s ∂σ) ∧
      (∫ s, Real.log (max s a) ∂σ) - (∫ s, Real.log s ∂σ) ≤ C * a := by
  have hlocal (t : ℝ) (ht : 0 < t) (hta : t ≤ a) := hCDF t ht (hta.trans haa₀)
  have hpos := (hardEdge_positive_ae σ ha₀ hCDF).mono fun _ hs => hs.le
  rw [← integral_sub (integrable_logCutoff_of_secondMoment σ hpos hsecond ha)
    (integrable_log_of_hardEdge_secondMoment σ ha₀ hC hCDF hsecond)]
  exact ⟨integral_lowerLogError_nonneg σ ha hC hlocal,
    integral_lowerLogError_le σ ha hC hlocal⟩

theorem logCutoff_identity_of_hardEdge_secondMoment (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a₀ C : ℝ} (ha₀ : 0 < a₀) (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → t ≤ a₀ → σ.real (Iic t) ≤ C * t)
    (hsecond : Integrable (fun s : ℝ => s ^ 2) σ)
    {a : ℝ} (ha : 0 < a) (haa₀ : a ≤ a₀) :
    (∫ s, Real.log (max s a) ∂σ) - (∫ s, Real.log s ∂σ) =
      ∫ t in Ioc 0 a, σ.real (Iic t) / t := by
  have hpos := (hardEdge_positive_ae σ ha₀ hCDF).mono fun _ hs => hs.le
  exact integral_logCutoff_sub_log_eq_cdf σ ha hC
    (fun t ht hta => hCDF t ht (hta.trans haa₀))
    (integrable_logCutoff_of_secondMoment σ hpos hsecond ha)

theorem logCutoff_tendsto_of_hardEdge (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a₀ C : ℝ} (ha₀ : 0 < a₀) (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → t ≤ a₀ → σ.real (Iic t) ≤ C * t)
    (hsecond : Integrable (fun s : ℝ => s ^ 2) σ)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (halim : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s, Real.log (max s (a n)) ∂σ)
      atTop (𝓝 (∫ s, Real.log s ∂σ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun n => C * a n) atTop (𝓝 0) := by
    simpa only [mul_zero] using halim.const_mul C
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [halim.eventually (Iio_mem_nhds ha₀)] with n hn
  have hb := logCutoff_error_of_hardEdge_secondMoment σ ha₀ hC hCDF hsecond (ha n) hn.le
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

end CircularLawSection6
