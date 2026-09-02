import ShortRingAnchor.BC12.DiskPotential
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# An elementary reference ensemble for Section 5

The comparison law is normalized area on the open unit disk.  Its potential
formula is the already proved Section 3 calculation, not a Ginibre limit
hypothesis.  IID samples from this law will be the diagonal of the reference
matrix.  Their empirical averages converge by the strong law.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal BigOperators

noncomputable section

namespace CircularLawSections56.Section5

open ShortRingAnchor ShortRingAnchor.BC12

/-- Normalized planar area on the unit disk. -/
def circularMeasure : Measure ℂ :=
  ENNReal.ofReal (1 / Real.pi) • (volume : Measure ℂ).restrict (Metric.ball 0 1)

instance circularMeasure_isProbabilityMeasure : IsProbabilityMeasure circularMeasure := by
  constructor
  simp only [circularMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Complex.volume_ball, ENNReal.ofReal_one, pow_two, mul_one, smul_eq_mul,
    one_div]
  rw [ENNReal.ofReal_inv_of_pos Real.pi_pos,
    show ENNReal.ofReal Real.pi = (NNReal.pi : ℝ≥0∞) by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]]
  simpa only [one_mul] using
    ENNReal.inv_mul_cancel (by exact_mod_cast NNReal.pi_ne_zero) ENNReal.coe_ne_top

theorem integral_circularMeasure (f : ℂ → ℝ) :
    (∫ w, f w ∂circularMeasure) = ∫ w, f w * circularDensity w := by
  rw [circularMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
  rw [smul_eq_mul, ← integral_const_mul, ← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards with w
  by_cases hw : ‖w‖ < 1 <;> simp [circularDensity, Metric.mem_ball, dist_zero_right, hw,
    mul_comm]

theorem integrable_circularMeasure_iff (f : ℂ → ℝ) :
    Integrable f circularMeasure ↔ Integrable (fun w => f w * circularDensity w) := by
  rw [circularMeasure, integrable_smul_measure
    (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top]
  have heq : (fun w => f w * circularDensity w) =
      (Metric.ball (0 : ℂ) 1).indicator (fun w => (1 / Real.pi) * f w) := by
    funext w
    by_cases hw : ‖w‖ < 1 <;> simp [circularDensity, Metric.mem_ball, dist_zero_right, hw,
      mul_comm]
  rw [heq, integrable_indicator_iff measurableSet_ball]
  exact (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (by positivity : (1 / Real.pi : ℝ) ≠ 0)) f).symm

theorem circularMeasure_log_integrable (z : ℂ) :
    Integrable (fun w : ℂ => Real.log ‖w - z‖) circularMeasure :=
  (integrable_circularMeasure_iff _).2 (integrable_log_mul_circularDensity z)

theorem circularMeasure_log_potential (z : ℂ) :
    (∫ w : ℂ, Real.log ‖w - z‖ ∂circularMeasure) = circularLogPotential z := by
  rw [integral_circularMeasure, integral_log_mul_circularDensity]

theorem circularMeasure_norm_lt_one : ∀ᵐ w ∂circularMeasure, ‖w‖ < 1 := by
  apply Measure.ae_smul_measure
  simpa only [Metric.mem_ball, dist_zero_right] using
    (ae_restrict_mem measurableSet_ball : ∀ᵐ w ∂(volume : Measure ℂ).restrict
      (Metric.ball 0 1), w ∈ Metric.ball 0 1)

instance circularMeasure_noAtoms : NullSingletonClass circularMeasure := by
  constructor
  intro z
  simp [circularMeasure, Measure.smul_apply]

/-- One fixed probability space for all reference matrix sizes. -/
def circularSampleMeasure : Measure (ℕ → ℂ) :=
  Measure.infinitePi (fun _ : ℕ => circularMeasure)

instance circularSampleMeasure_isProbabilityMeasure :
    IsProbabilityMeasure circularSampleMeasure := by
  unfold circularSampleMeasure
  infer_instance

theorem circularSample_eval (i : ℕ) :
    MeasurePreserving (Function.eval i) circularSampleMeasure circularMeasure :=
  measurePreserving_eval_infinitePi (fun _ : ℕ => circularMeasure) i

/-- This applies to the unbounded logarithmic kernel as well as bounded tests. -/
theorem circularSample_average_tendsto (f : ℂ → ℝ) (hf : Measurable f)
    (hInt : Integrable f circularMeasure) :
    ∀ᵐ ω ∂circularSampleMeasure,
      Tendsto (fun k : ℕ => (∑ i : Fin (k + 1), f (ω i)) / (k + 1 : ℝ))
        atTop (𝓝 (∫ w, f w ∂circularMeasure)) := by
  have hind : iIndepFun (fun i : ℕ => fun ω : ℕ → ℂ => f (ω i))
      circularSampleMeasure := iIndepFun_infinitePi (fun _ => hf)
  have hident : ∀ i : ℕ, IdentDistrib (fun ω : ℕ → ℂ => f (ω i))
      (fun ω => f (ω 0)) circularSampleMeasure circularSampleMeasure := by
    intro i
    constructor
    · exact (hf.comp (measurable_pi_apply i)).aemeasurable
    · exact (hf.comp (measurable_pi_apply 0)).aemeasurable
    · change Measure.map (f ∘ Function.eval i) circularSampleMeasure =
        Measure.map (f ∘ Function.eval 0) circularSampleMeasure
      rw [← Measure.map_map hf (measurable_pi_apply i),
        ← Measure.map_map hf (measurable_pi_apply 0),
        (circularSample_eval i).map_eq, (circularSample_eval 0).map_eq]
  have h := strong_law_ae_real (fun i : ℕ => fun ω : ℕ → ℂ => f (ω i))
    ((circularSample_eval 0).integrable_comp_of_integrable hInt)
    (fun _ _ hij => hind.indepFun hij) hident
  have hmean : (∫ ω, f (ω 0) ∂circularSampleMeasure) = ∫ w, f w ∂circularMeasure := by
    have hp := circularSample_eval 0
    rw [← hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable
      (by rw [hp.map_eq]; exact hInt.aestronglyMeasurable)).symm
  filter_upwards [h] with ω hω
  simpa only [Function.comp_def, ← Fin.sum_univ_eq_sum_range, Nat.cast_add, Nat.cast_one,
    hmean] using hω.comp (tendsto_add_atTop_nat 1)

end CircularLawSections56.Section5
