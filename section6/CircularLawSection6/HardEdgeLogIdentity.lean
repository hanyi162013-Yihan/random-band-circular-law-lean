import CircularLawSection6.HardEdgeLogFubini
import ShortRingAnchor.ClippedLog

/-! # Exact lower logarithmic cutoff identity

The linear hard-edge bound proves the Fubini hypotheses, absence of mass at
zero, integrability of the cutoff error, and its exact CDF integral. Only the
upper logarithmic tail still needs a separate integrability argument.
-/

open MeasureTheory Set Filter Topology
noncomputable section

namespace CircularLawSection6

theorem integral_lowerLogKernel_right {s : ℝ} (hs : 0 < s) (a : ℝ) :
    (∫ t in Ioc 0 a, lowerLogKernel s t) =
      Real.log (max s a) - Real.log s := by
  by_cases hsa : s ≤ a
  · rw [max_eq_right hsa]
    unfold lowerLogKernel
    rw [setIntegral_indicator measurableSet_Ici]
    have hset : Ioc 0 a ∩ Ici s = Icc s a := by
      ext t
      constructor
      · intro ht
        exact ⟨ht.2, ht.1.2⟩
      · intro ht
        exact ⟨⟨hs.trans_le ht.1, ht.2⟩, ht.1⟩
    rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsa]
    simpa only [one_div] using
      ShortRingAnchor.intervalIntegral_one_div_eq_log_sub hs hsa
  · rw [max_eq_left (le_of_not_ge hsa), sub_self]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    have hts : t < s := ht.2.trans_lt (lt_of_not_ge hsa)
    simp only [lowerLogKernel, indicator_of_notMem (not_le_of_gt hts)]

theorem integrable_lowerLogError (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → t ≤ a → σ.real (Iic t) ≤ C * t) :
    Integrable (fun s => Real.log (max s a) - Real.log s) σ := by
  apply (lowerLogKernel_integrable_prod σ hC hCDF).integral_prod_left.congr
  filter_upwards [hardEdge_positive_ae σ ha hCDF] with s hs
  exact integral_lowerLogKernel_right hs a

theorem integrable_lowerLogCdf (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a C : ℝ} (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → t ≤ a → σ.real (Iic t) ≤ C * t) :
    Integrable (fun t => σ.real (Iic t) / t) (volume.restrict (Ioc 0 a)) := by
  apply (lowerLogKernel_integrable_prod σ hC hCDF).integral_prod_right.congr
  exact ae_of_all _ (integral_lowerLogKernel_left σ)

theorem integral_lowerLogError_eq_cdf (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → t ≤ a → σ.real (Iic t) ≤ C * t) :
    (∫ s, Real.log (max s a) - Real.log s ∂σ) =
      ∫ t in Ioc 0 a, σ.real (Iic t) / t := by
  calc
    _ = ∫ s, (∫ t in Ioc 0 a, lowerLogKernel s t) ∂σ := by
      apply integral_congr_ae
      filter_upwards [hardEdge_positive_ae σ ha hCDF] with s hs
      exact (integral_lowerLogKernel_right hs a).symm
    _ = _ := integral_lowerLogKernel_swap σ hC hCDF

theorem integral_lowerLogError_nonneg (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → t ≤ a → σ.real (Iic t) ≤ C * t) :
    0 ≤ ∫ s, Real.log (max s a) - Real.log s ∂σ := by
  rw [integral_lowerLogError_eq_cdf σ ha hC hCDF]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact div_nonneg measureReal_nonneg ht.1.le

theorem integral_lowerLogError_le (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → t ≤ a → σ.real (Iic t) ≤ C * t) :
    (∫ s, Real.log (max s a) - Real.log s ∂σ) ≤ C * a := by
  have : IsFiniteMeasure (volume.restrict (Ioc 0 a)) := ⟨by simp⟩
  rw [integral_lowerLogError_eq_cdf σ ha hC hCDF]
  calc
    _ ≤ ∫ _t in Ioc 0 a, C := by
      apply integral_mono_ae (integrable_lowerLogCdf σ hC hCDF) (integrable_const C)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (div_le_iff₀ ht.1).2 (hCDF t ht.1 ht.2)
    _ = C * a := by
      rw [setIntegral_const, Real.volume_real_Ioc_of_le ha.le]
      simp only [sub_zero, smul_eq_mul, mul_comm]

theorem integrable_log_of_hardEdge (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → t ≤ a → σ.real (Iic t) ≤ C * t)
    (hcut : Integrable (fun s => Real.log (max s a)) σ) :
    Integrable Real.log σ := by
  apply (hcut.sub (integrable_lowerLogError σ ha hC hCDF)).congr
  filter_upwards with s
  exact sub_sub_cancel _ _

theorem integral_logCutoff_sub_log_eq_cdf (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → t ≤ a → σ.real (Iic t) ≤ C * t)
    (hcut : Integrable (fun s => Real.log (max s a)) σ) :
    (∫ s, Real.log (max s a) ∂σ) - (∫ s, Real.log s ∂σ) =
      ∫ t in Ioc 0 a, σ.real (Iic t) / t := by
  rw [← integral_sub hcut (integrable_log_of_hardEdge σ ha hC hCDF hcut)]
  exact integral_lowerLogError_eq_cdf σ ha hC hCDF

end CircularLawSection6
