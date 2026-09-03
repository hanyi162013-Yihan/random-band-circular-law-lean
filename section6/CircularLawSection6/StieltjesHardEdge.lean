import CircularLawSection6.CutoffIntegrability

/-! # A bounded imaginary Stieltjes transform gives linear hard-edge mass

For a nonnegative singular-value law, the imaginary transform on the
imaginary axis is the integral of t/(s^2+t^2). Its bound C implies
sigma([0,t]) <= 2*C*t. This is a source-level adapter for the separate
hard-edge route; no density or log-cutoff identity is assumed or inferred.
-/

open MeasureTheory Set

noncomputable section

namespace CircularLawSection6

def singularPoissonKernel (t s : ℝ) : ℝ := t / (s ^ 2 + t ^ 2)

theorem singularPoissonKernel_nonneg {t : ℝ} (ht : 0 < t) (s : ℝ) :
    0 ≤ singularPoissonKernel t s := by
  unfold singularPoissonKernel
  positivity

theorem singularPoissonKernel_le {t : ℝ} (ht : 0 < t) (s : ℝ) :
    singularPoissonKernel t s ≤ 1 / t := by
  unfold singularPoissonKernel
  apply (div_le_div_iff₀ (by positivity) ht).2
  nlinarith [sq_nonneg s]

theorem singularPoissonKernel_integrable (σ : Measure ℝ) [IsFiniteMeasure σ]
    {t : ℝ} (ht : 0 < t) : Integrable (singularPoissonKernel t) σ := by
  apply (integrable_const (1 / t)).mono'
  · have hc : Continuous (singularPoissonKernel t) := by
      unfold singularPoissonKernel
      apply Continuous.div continuous_const (by fun_prop)
      intro s
      exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg s) (sq_pos_of_pos ht))
    exact hc.measurable.aestronglyMeasurable
  · filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (singularPoissonKernel_nonneg ht s)]
    exact singularPoissonKernel_le ht s

theorem hardEdge_mass_le_of_poisson_bound (σ : Measure ℝ) [IsFiniteMeasure σ]
    {t C : ℝ} (ht : 0 < t)
    (hbound : (∫ s, singularPoissonKernel t s ∂σ) ≤ C) :
    σ.real (Icc 0 t) ≤ 2 * C * t := by
  have hset : Icc 0 t ⊆ {s | 1 / (2 * t) ≤ singularPoissonKernel t s} := by
    intro s hs
    change 1 / (2 * t) ≤ t / (s ^ 2 + t ^ 2)
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hsq := (sq_le_sq₀ hs.1 ht.le).2 hs.2
    nlinarith
  have hm := ENNReal.toReal_mono (measure_ne_top σ _) (measure_mono hset)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all σ fun s => singularPoissonKernel_nonneg ht s)
    (singularPoissonKernel_integrable σ ht) (1 / (2 * t))
  have h : (1 / (2 * t)) * σ.real (Icc 0 t) ≤ C :=
    (mul_le_mul_of_nonneg_left hm (by positivity)).trans (hmark.trans hbound)
  have hdiv : σ.real (Icc 0 t) / (2 * t) ≤ C := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using h
  exact ((div_le_iff₀ (by positivity : 0 < 2 * t)).mp hdiv).trans_eq (by ring)

theorem hardEdge_cdf_le_of_poisson_bound (σ : Measure ℝ) [IsFiniteMeasure σ]
    (hpos : ∀ᵐ s ∂σ, 0 ≤ s) {t C : ℝ} (ht : 0 < t)
    (hbound : (∫ s, singularPoissonKernel t s ∂σ) ≤ C) :
    σ.real (Iic t) ≤ 2 * C * t := by
  have heq : σ (Iic t) = σ (Icc 0 t) := by
    apply measure_congr
    filter_upwards [hpos] with s hs
    change (s ≤ t) = (0 ≤ s ∧ s ≤ t)
    exact propext ⟨fun h => ⟨hs, h⟩, fun h => h.2⟩
  change (σ (Iic t)).toReal ≤ _
  rw [heq]
  exact hardEdge_mass_le_of_poisson_bound σ ht hbound

end CircularLawSection6
