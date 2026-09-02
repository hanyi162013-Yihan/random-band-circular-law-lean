import BernoulliSection9.TerminalSmallBall

/-!
# Capped estimates give honest logarithmic tail bounds

The events here explicitly contain a zero value. They therefore express the
paper's `log 0 = -infinity` convention even though the finite logarithms are
real-valued. A cap estimate controls that event without an almost-everywhere
invertibility premise. This is the Markov step in (8.54) and (8.63).
-/

open MeasureTheory

noncomputable section

namespace BernoulliSection8

open BernoulliSection9

def logLowerTail (T c : ℝ) (w : ℂ) : Prop :=
  w = 0 ∨ T ≤ Real.log c - Real.log ‖w‖

def logDeviation (T c : ℝ) (w : ℂ) : Prop :=
  w = 0 ∨ T ≤ |Real.log ‖w‖ - Real.log c|

theorem le_cappedLogLoss_iff {T c : ℝ} (hT : 0 < T) (hc : 0 < c) (w : ℂ) :
    T ≤ cappedLogLoss T c w ↔ logLowerTail T c w := by
  by_cases hw : w = 0
  · simp [hw, logLowerTail]
  · have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    simp [cappedLogLoss, hw, logLowerTail, Real.posLog, le_min_iff,
      le_max_iff, not_le.mpr hT, Real.log_div hc.ne' hn]

theorem measurable_cappedLoss {Ω : Type*} [MeasurableSpace Ω]
    (T c : ℝ) {value : Ω → ℂ} (hv : Measurable value) :
    Measurable (fun ω => cappedLogLoss T c (value ω)) := by
  unfold cappedLogLoss
  exact Measurable.ite (hv (measurableSet_singleton 0)) measurable_const
    (measurable_const.min (Real.continuous_posLog.measurable.comp
      (measurable_const.div hv.norm)))

theorem integrable_cappedLoss {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {T : ℝ} (hT : 0 ≤ T)
    (c : ℝ) {value : Ω → ℂ} (hv : Measurable value) :
    Integrable (fun ω => cappedLogLoss T c (value ω)) μ := by
  apply (integrable_const T).mono' (measurable_cappedLoss T c hv).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_of_nonneg (cappedLogLoss_nonneg hT)]
    exact cappedLogLoss_le_cap

theorem logLowerTail_probability_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T c A p : ℝ} (hT : 0 < T) (hc : 0 < c)
    {value : Ω → ℂ} (hv : Measurable value)
    (hcap : (∫ ω, cappedLogLoss T c (value ω) ∂μ) ≤ A + p * T) :
    μ.real {ω | logLowerTail T c (value ω)} ≤ p + A / T := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun ω => cappedLogLoss_nonneg (c := c) (w := value ω) hT.le)
    (integrable_cappedLoss μ hT.le c hv) T
  simp only [le_cappedLogLoss_iff hT hc] at hm
  have h := hm.trans hcap
  have heq : (A + p * T) / T = p + A / T := by field_simp; ring
  rw [← heq]
  exact (le_div_iff₀ hT).mpr (by simpa only [mul_comm] using h)

theorem logDeviation_subset_lowerTail_union_reverse {Ω : Type*}
    {T c A : ℝ} (hTA : A < T) (hc : 0 < c)
    (value : Ω → ℂ) (good : Set Ω)
    (hgood : ∀ ω ∈ good, Real.posLog (‖value ω‖ / c) ≤ A) :
    {ω | logDeviation T c (value ω)} ⊆
      {ω | logLowerTail T c (value ω)} ∪ goodᶜ := by
  intro ω hω
  by_cases hg : ω ∈ good
  · left
    rcases hω with hz | hdev
    · exact Or.inl hz
    · by_cases hz : value ω = 0
      · exact Or.inl hz
      · right
        have hnorm : ‖value ω‖ ≠ 0 := norm_ne_zero_iff.mpr hz
        have hu : Real.log ‖value ω‖ - Real.log c ≤ A := by
          calc
            _ = Real.log (‖value ω‖ / c) := (Real.log_div hnorm hc.ne').symm
            _ ≤ Real.posLog (‖value ω‖ / c) := le_max_right _ _
            _ ≤ A := hgood ω hg
        rcases le_abs.mp hdev with h | h
        · linarith
        · linarith
  · exact Or.inr hg

/-- Both tails, including the atom at zero, follow from the already proved
terminal conclusion and its separately controlled reverse-event failure. -/
theorem terminal_logDeviation_probability_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T c A p q : ℝ} (hT : 0 < T) (hTA : A < T)
    {value : Ω → ℂ} (hv : Measurable value)
    (h : TerminalSmallBallConclusion μ c value A p)
    (hreverse : μ.real h.reverse_eventᶜ ≤ q) :
    μ.real {ω | logDeviation T c (value ω)} ≤ p + A / T + q := by
  apply (measureReal_mono
    (logDeviation_subset_lowerTail_union_reverse hTA h.coefficientNorm_pos
      value h.reverse_event h.reverse)).trans
  exact (measureReal_union_le _ _).trans
    (add_le_add (logLowerTail_probability_le μ hT h.coefficientNorm_pos hv
      (h.capped T hT)) hreverse)

end BernoulliSection8
