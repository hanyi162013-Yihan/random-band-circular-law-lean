import CircularLawSection6.StieltjesTransformIdentification
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Integrable logarithmic layer-cake kernel from a linear hard edge

A CDF bound supplies both the null exceptional set at zero and the Fubini
integrability needed for the logarithmic cutoff identity. Neither is an input.
-/

open MeasureTheory Set Filter Topology
noncomputable section

namespace CircularLawSection6

theorem hardEdge_nonpositive_null (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a C : ℝ} (ha : 0 < a)
    (hCDF : ∀ t, 0 < t → t ≤ a → σ.real (Iic t) ≤ C * t) :
    σ (Iic 0) = 0 := by
  have hseq : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmall := hseq.eventually (Iio_mem_nhds ha)
  have hlim : Tendsto (fun n : ℕ => C * (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hseq
  have hzero : σ.real (Iic 0) ≤ 0 := ge_of_tendsto hlim (by
    filter_upwards [hsmall] with n hn
    have ht : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    exact (measureReal_mono (Iic_subset_Iic.mpr ht.le)).trans
      (hCDF _ ht hn.le))
  exact (measureReal_eq_zero_iff (by finiteness)).mp
    (le_antisymm hzero measureReal_nonneg)

theorem hardEdge_positive_ae (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a C : ℝ} (ha : 0 < a)
    (hCDF : ∀ t, 0 < t → t ≤ a → σ.real (Iic t) ≤ C * t) :
    ∀ᵐ s ∂σ, 0 < s := by
  rw [ae_iff]
  simpa only [not_lt, Iic_def] using hardEdge_nonpositive_null σ ha hCDF

def lowerLogKernel (s t : ℝ) : ℝ := (Ici s).indicator (fun t => t⁻¹) t

theorem lowerLogKernel_measurable : Measurable (Function.uncurry lowerLogKernel) := by
  change Measurable ({p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p => p.2⁻¹))
  exact measurable_snd.inv.indicator (measurableSet_le measurable_fst measurable_snd)

theorem lowerLogKernel_nonneg (s : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ lowerLogKernel s t := by
  simp only [lowerLogKernel, indicator]
  split_ifs <;> positivity

theorem lowerLogKernel_left (s t : ℝ) :
    lowerLogKernel s t = (Iic t).indicator (fun _ => t⁻¹) s := by
  simp only [lowerLogKernel, indicator, mem_Ici, mem_Iic]

theorem lowerLogKernel_integrable_left (σ : Measure ℝ) [IsFiniteMeasure σ] (t : ℝ) :
    Integrable (fun s => lowerLogKernel s t) σ := by
  simp_rw [lowerLogKernel_left]
  exact (integrable_const _).indicator measurableSet_Iic

theorem integral_lowerLogKernel_left (σ : Measure ℝ) [IsFiniteMeasure σ] (t : ℝ) :
    (∫ s, lowerLogKernel s t ∂σ) = σ.real (Iic t) / t := by
  simp_rw [lowerLogKernel_left]
  rw [integral_indicator measurableSet_Iic, setIntegral_const]
  simp only [smul_eq_mul, div_eq_mul_inv]

theorem integral_norm_lowerLogKernel_left (σ : Measure ℝ) [IsFiniteMeasure σ]
    {t : ℝ} (ht : 0 < t) :
    (∫ s, ‖lowerLogKernel s t‖ ∂σ) = σ.real (Iic t) / t := by
  have hn (s : ℝ) : ‖lowerLogKernel s t‖ = lowerLogKernel s t :=
    Real.norm_of_nonneg (lowerLogKernel_nonneg s ht)
  simp_rw [hn]
  exact integral_lowerLogKernel_left σ t

theorem lowerLogKernel_integrable_prod (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a C : ℝ} (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → t ≤ a → σ.real (Iic t) ≤ C * t) :
    Integrable (Function.uncurry lowerLogKernel) (σ.prod (volume.restrict (Ioc 0 a))) := by
  have : IsFiniteMeasure (volume.restrict (Ioc 0 a)) := ⟨by simp⟩
  apply (integrable_prod_iff' lowerLogKernel_measurable.stronglyMeasurable.aestronglyMeasurable).2
  refine ⟨ae_of_all _ (lowerLogKernel_integrable_left σ), ?_⟩
  apply (integrable_const |C|).mono'
  · exact lowerLogKernel_measurable.stronglyMeasurable.norm.integral_prod_left.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    change ‖∫ s, ‖lowerLogKernel s t‖ ∂σ‖ ≤ |C|
    rw [integral_norm_lowerLogKernel_left σ ht.1, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg measureReal_nonneg ht.1.le), abs_of_nonneg hC]
    exact (div_le_iff₀ ht.1).2 (hCDF t ht.1 ht.2)

theorem integral_lowerLogKernel_swap (σ : Measure ℝ) [IsFiniteMeasure σ]
    {a C : ℝ} (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → t ≤ a → σ.real (Iic t) ≤ C * t) :
    (∫ s, (∫ t in Ioc 0 a, lowerLogKernel s t) ∂σ) =
      ∫ t in Ioc 0 a, σ.real (Iic t) / t := by
  rw [integral_integral_swap (lowerLogKernel_integrable_prod σ hC hCDF)]
  exact integral_congr_ae (ae_of_all _ (integral_lowerLogKernel_left σ))

end CircularLawSection6
