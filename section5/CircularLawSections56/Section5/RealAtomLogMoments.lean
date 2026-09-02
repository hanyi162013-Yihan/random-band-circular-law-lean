import CircularLawSections56.Section5.LiteralRowLogMoments
import CircularLawSection4.IIDCoordinateFacts

/-! # Real atoms and distribution-independent weighted logarithmic costs

Real atoms are embedded in the complex plane without imposing a planar density.
The weighted estimate separates the deterministic endpoint loss from the atom
loss, and therefore also applies to polynomially vanishing taper weights.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5

open CircularLawSection4

def realComplexAtomLaw (ν : Measure ℝ) : Measure ℂ := ν.map Complex.ofReal

instance realComplexAtomLaw_probability (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (realComplexAtomLaw ν) :=
  Measure.isProbabilityMeasure_map Complex.continuous_ofReal.measurable.aemeasurable

theorem realComplexAtomLaw_measurePreserving (ν : Measure ℝ) :
    MeasurePreserving Complex.ofReal ν (realComplexAtomLaw ν) :=
  ⟨Complex.continuous_ofReal.measurable, rfl⟩

theorem realComplexAtomLaw_secondMoment (ν : Measure ℝ)
    (hInt : Integrable (fun u : ℝ => u ^ 2) ν) :
    Integrable (fun u : ℂ => ‖u‖ ^ 2) (realComplexAtomLaw ν) ∧
      (∫ u : ℂ, ‖u‖ ^ 2 ∂realComplexAtomLaw ν) = ∫ u : ℝ, u ^ 2 ∂ν := by
  have hm : Measurable (fun u : ℂ => ‖u‖ ^ 2) := continuous_norm.measurable.pow_const 2
  have hi : Integrable (fun u : ℂ => ‖u‖ ^ 2) (realComplexAtomLaw ν) := by
    apply (integrable_map_measure hm.aestronglyMeasurable
      Complex.continuous_ofReal.measurable.aemeasurable).2
    simpa only [Function.comp_def, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hInt
  refine ⟨hi, ?_⟩
  rw [realComplexAtomLaw, integral_map Complex.continuous_ofReal.measurable.aemeasurable
    hm.aestronglyMeasurable]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem real_negativeLog_norm_integrable_and_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (L : ℝ) (hL : 0 ≤ L)
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) :
    Integrable (fun u : ℝ => negativeLog ‖u‖) ν ∧
      ∫ u : ℝ, negativeLog ‖u‖ ∂ν ≤ Real.log (max 1 (2 * L)) + 1 := by
  have hsmall : ∀ ρ : ℝ, 0 < ρ →
      ν {u : ℝ | ‖u‖ ≤ (1 : ℝ) * ρ ^ 1} ≤ ENNReal.ofReal ((2 * L) * ρ ^ 1) := by
    intro ρ hρ
    have h := hν (-ρ) ρ (by linarith)
    have heq : {u : ℝ | ‖u‖ ≤ (1 : ℝ) * ρ ^ 1} = Set.Icc (-ρ) ρ := by
      ext u
      simp only [Set.mem_ofPred_eq, one_mul, pow_one, Real.norm_eq_abs, abs_le, Set.mem_Icc]
    rw [heq]
    calc
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal (ρ - -ρ) := h
      _ = ENNReal.ofReal ((2 * L) * ρ ^ 1) := by
        rw [← ENNReal.ofReal_mul hL]
        congr 1
        ring
  obtain ⟨_, _, hi, hb⟩ := zeroSet_aeLog_and_integrable_positiveLogLoss_of_power_smallBall
    ν (fun u : ℝ => ‖u‖) continuous_norm.measurable norm_nonneg 1 (2 * L)
      zero_lt_one 1 1 (by decide) (by decide) hsmall
  simpa only [positiveLogLoss, Real.log_one, zero_sub, negativeLog,
    Nat.cast_one, div_one] using And.intro hi hb

theorem realComplexAtomLaw_ae_ne_zero
    (ν : Measure ℝ) {L : ℝ} (hν : RealIntervalBound ν (ENNReal.ofReal L)) :
    ∀ᵐ u : ℂ ∂realComplexAtomLaw ν, u ≠ 0 := by
  have hm : MeasurableSet {u : ℂ | u ≠ 0} := (measurableSet_singleton 0).compl
  rw [realComplexAtomLaw, ae_map_iff Complex.continuous_ofReal.measurable.aemeasurable
    hm]
  have hzero : ∀ᵐ u : ℝ ∂ν, u ≠ 0 := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using
      measure_singleton_zero_eq_zero_of_realIntervalBound hν
  simpa only [Complex.ofReal_ne_zero] using hzero

theorem realComplexAtomLaw_negativeLog
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (L : ℝ) (hL : 0 ≤ L)
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) :
    Integrable (fun u : ℂ => negativeLog ‖u‖) (realComplexAtomLaw ν) ∧
      ∫ u : ℂ, negativeLog ‖u‖ ∂realComplexAtomLaw ν ≤ Real.log (max 1 (2 * L)) + 1 := by
  have h := real_negativeLog_norm_integrable_and_bound ν L hL hν
  have hm : Measurable (fun u : ℂ => negativeLog ‖u‖) :=
    measurable_const.max (Real.measurable_log.comp continuous_norm.measurable).neg
  constructor
  · apply (integrable_map_measure hm.aestronglyMeasurable
      Complex.continuous_ofReal.measurable.aemeasurable).2
    simpa only [Function.comp_def, Complex.norm_real] using h.1
  · rw [realComplexAtomLaw, integral_map Complex.continuous_ofReal.measurable.aemeasurable
      hm.aestronglyMeasurable]
    simpa only [Complex.norm_real] using h.2

/-- No density or fixed indicator lower bound is needed for this weighted cost. -/
theorem negativeLog_weighted_of_atom_cost
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (b : ℂ) (hb : b ≠ 0) (K : ℝ)
    (hzero : ∀ᵐ u : ℂ ∂ν, u ≠ 0)
    (hInt : Integrable (fun u : ℂ => negativeLog ‖u‖) ν)
    (hBound : ∫ u : ℂ, negativeLog ‖u‖ ∂ν ≤ K) :
    Integrable (fun u : ℂ => negativeLog ‖b * u‖) ν ∧
      ∫ u : ℂ, negativeLog ‖b * u‖ ∂ν ≤ negativeLog ‖b‖ + K := by
  have hdom : ∀ᵐ u : ℂ ∂ν, negativeLog ‖b * u‖ ≤ negativeLog ‖b‖ + negativeLog ‖u‖ := by
    filter_upwards [hzero] with u hu
    rw [norm_mul]
    exact negativeLog_mul_le _ _ (norm_pos_iff.2 hb) (norm_pos_iff.2 hu)
  have hmeas : Measurable (fun u : ℂ => negativeLog ‖b * u‖) :=
    measurable_const.max (Real.measurable_log.comp (measurable_const.mul measurable_id).norm).neg
  have hi : Integrable (fun u : ℂ => negativeLog ‖b * u‖) ν :=
    ((integrable_const (negativeLog ‖b‖)).add hInt).mono' hmeas.aestronglyMeasurable (by
      filter_upwards [hdom] with u hu
      have hn : 0 ≤ negativeLog ‖b * u‖ := le_max_left _ _
      simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg hn] using hu)
  refine ⟨hi, ?_⟩
  have h := integral_mono_ae hi ((integrable_const (negativeLog ‖b‖)).add hInt) hdom
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) hInt] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  exact h.trans (add_le_add le_rfl hBound)

end CircularLawSections56.Section5
