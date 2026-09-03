import CircularLawSection6.HardEdgeLogLimit
import CircularLawSection6.SingularBasisCutoff

/-! # Exact scaling of singular laws and uniform lower-cutoff errors

Scaling a nonnegative singular law by r changes F(t) to F(t/r). Consequently
the constant is uniform whenever r is bounded away from zero. The map and
its logarithmic normalization are explicit, not source assumptions.
-/

open MeasureTheory Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

def scaledSingularLaw (r : ℝ) (σ : Measure ℝ) : Measure ℝ :=
  Measure.map (fun s => r * s) σ

instance scaledSingularLaw_isProbability (r : ℝ) (σ : Measure ℝ) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (scaledSingularLaw r σ) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

theorem scaledSingularLaw_cdf (σ : Measure ℝ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (scaledSingularLaw r σ).real (Iic t) = σ.real (Iic (t / r)) := by
  unfold scaledSingularLaw Measure.real
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hset : (fun s : ℝ => r * s) ⁻¹' Iic t = Iic (t / r) := by
    ext s
    change r * s ≤ t ↔ s ≤ t / r
    simpa only [mul_comm] using (le_div_iff₀ hr).symm
  rw [hset]

theorem scaledSingularLaw_linearHardEdge (σ : Measure ℝ) {r C : ℝ} (hr : 0 < r)
    (hCDF : ∀ t, 0 < t → σ.real (Iic t) ≤ C * t) :
    ∀ t, 0 < t → (scaledSingularLaw r σ).real (Iic t) ≤ (C / r) * t := by
  intro t ht
  rw [scaledSingularLaw_cdf σ hr]
  exact (hCDF (t / r) (div_pos ht hr)).trans_eq (by ring)

theorem scaledSingularLaw_uniformHardEdge (σ : Measure ℝ) {r r₀ C : ℝ}
    (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → σ.real (Iic t) ≤ C * t) :
    ∀ t, 0 < t → (scaledSingularLaw r σ).real (Iic t) ≤ (C / r₀) * t := by
  intro t ht
  exact (scaledSingularLaw_linearHardEdge σ (hr₀.trans_le hr) hCDF t ht).trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hC hr₀ hr) ht.le)

theorem scaledSingularLaw_secondMoment (σ : Measure ℝ) (r : ℝ)
    (hsecond : Integrable (fun s : ℝ => s ^ 2) σ) :
    Integrable (fun s : ℝ => s ^ 2) (scaledSingularLaw r σ) := by
  unfold scaledSingularLaw
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
  change Integrable (fun s : ℝ => (r * s) ^ 2) σ
  simpa only [mul_pow] using hsecond.const_mul (r ^ 2)

theorem scaledSingularLaw_log (σ : Measure ℝ) [IsProbabilityMeasure σ]
    {r : ℝ} (hr : 0 < r) (hpos : ∀ᵐ s ∂σ, 0 < s) (hlog : Integrable Real.log σ) :
    (∫ s, Real.log s ∂scaledSingularLaw r σ) = Real.log r + ∫ s, Real.log s ∂σ := by
  rw [scaledSingularLaw, integral_map (by fun_prop) Real.measurable_log.aestronglyMeasurable]
  calc
    (∫ s, Real.log (r * s) ∂σ) = ∫ s, Real.log r + Real.log s ∂σ := by
      apply integral_congr_ae
      filter_upwards [hpos] with s hs
      exact Real.log_mul hr.ne' hs.ne'
    _ = _ := by rw [integral_add (integrable_const _) hlog, integral_const]; simp

theorem scaledSingularLaw_logCutoff (σ : Measure ℝ) [IsProbabilityMeasure σ]
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hcut : Integrable (fun s => Real.log (max s (a / r))) σ) :
    (∫ s, Real.log (max s a) ∂scaledSingularLaw r σ) =
      Real.log r + ∫ s, Real.log (max s (a / r)) ∂σ := by
  have hm : Measurable (fun s : ℝ => Real.log (max s a)) :=
    Real.measurable_log.comp (measurable_id.max measurable_const)
  rw [scaledSingularLaw, integral_map (by fun_prop) hm.aestronglyMeasurable]
  simp_rw [log_max_positive_scale hr ha]
  rw [integral_add (integrable_const _) hcut, integral_const]
  simp

theorem scaledSingularLaw_logCutoff_error (σ : Measure ℝ) [IsProbabilityMeasure σ]
    (hsecond : Integrable (fun s : ℝ => s ^ 2) σ)
    {r r₀ C : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hC : 0 ≤ C)
    (hCDF : ∀ t, 0 < t → σ.real (Iic t) ≤ C * t) {a : ℝ} (ha : 0 < a) :
    0 ≤ (∫ s, Real.log (max s a) ∂scaledSingularLaw r σ) -
      (∫ s, Real.log s ∂scaledSingularLaw r σ) ∧
    (∫ s, Real.log (max s a) ∂scaledSingularLaw r σ) -
      (∫ s, Real.log s ∂scaledSingularLaw r σ) ≤ (C / r₀) * a :=
  logCutoff_error_of_hardEdge_secondMoment (scaledSingularLaw r σ) ha
    (div_nonneg hC hr₀.le)
    (fun t ht _ => scaledSingularLaw_uniformHardEdge σ hr₀ hr hC hCDF t ht)
    (scaledSingularLaw_secondMoment σ r hsecond) ha le_rfl

end CircularLawSection6
