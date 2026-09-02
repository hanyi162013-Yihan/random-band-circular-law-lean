import BernoulliSection8.TwoSidedTerminal

/-! # Moving the terminal center from coefficients to exterior pressure -/

open MeasureTheory

noncomputable section

namespace BernoulliSection8

open BernoulliSection9

def absoluteLogDeviation (T center : ℝ) (w : ℂ) : Prop :=
  w = 0 ∨ T ≤ |Real.log ‖w‖ - center|

theorem measurableSet_absoluteLogDeviation
    {Ω : Type*} [MeasurableSpace Ω] (T : ℝ)
    {value : Ω → ℂ} (hv : Measurable value) {center : Ω → ℝ} (hc : Measurable center) :
    MeasurableSet {x | absoluteLogDeviation T (center x) (value x)} :=
  (hv (measurableSet_singleton 0)).union
    (measurableSet_le measurable_const (((Real.measurable_log.comp hv.norm).sub hc).norm))

theorem absoluteLogDeviation_commonScale (T center : ℝ) (w a : ℂ) (ha : a ≠ 0) :
    absoluteLogDeviation T (Real.log ‖a‖ + center) (a * w) ↔
      absoluteLogDeviation T center w := by
  by_cases hw : w = 0
  · simp [hw, absoluteLogDeviation]
  · simp only [absoluteLogDeviation, mul_ne_zero ha hw, hw, false_or, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr ha)
      (norm_ne_zero_iff.mpr hw)]
    congr 2
    ring

theorem absoluteLogDeviation_subset_coefficientTail
    {T D c center : ℝ} (value : ℂ) (hcenter : |Real.log c - center| ≤ D) :
    absoluteLogDeviation (T + D) center value → logDeviation T c value := by
  intro h
  rcases h with hzero | hdev
  · exact Or.inl hzero
  · right
    have htriangle := abs_sub_le (Real.log ‖value‖) (Real.log c) center
    linarith

theorem centered_terminal_probability_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T c A p D center : ℝ} (hT : 0 < T) {value : Ω → ℂ} (hv : Measurable value)
    (h : TerminalSmallBallConclusion μ c value A p)
    (hcenter : |Real.log c - center| ≤ D) :
    μ.real {x | absoluteLogDeviation (T + D) center (value x)} ≤
      p + A / T + Real.exp (-(2 * T)) := by
  exact (measureReal_mono (fun x hx =>
    absoluteLogDeviation_subset_coefficientTail (value x) hcenter hx)).trans
    (terminal_logDeviation_probability_le_parseval μ hT hv h)

theorem scaled_centered_terminal_probability_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T c A p D center : ℝ} (hT : 0 < T) {value : Ω → ℂ} (hv : Measurable value)
    (h : TerminalSmallBallConclusion μ c value A p)
    (hcenter : |Real.log c - center| ≤ D) (a : ℂ) (ha : a ≠ 0) :
    μ.real {x | absoluteLogDeviation (T + D) (Real.log ‖a‖ + center) (a * value x)} ≤
      p + A / T + Real.exp (-(2 * T)) := by
  simp_rw [absoluteLogDeviation_commonScale _ _ _ _ ha]
  exact centered_terminal_probability_le μ hT hv h hcenter

end BernoulliSection8
