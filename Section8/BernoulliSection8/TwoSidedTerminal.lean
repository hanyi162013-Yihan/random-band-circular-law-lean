import BernoulliSection8.CappedProbability

/-!
# Two-sided logarithmic control from capped loss and Parseval

The atom at zero belongs to the lower tail. The upper tail follows from
the actual second moment, so no unspecified reverse good event is used.
-/

open MeasureTheory

noncomputable section

namespace BernoulliSection8

open BernoulliSection9

def logUpperTail (T c : ℝ) (w : ℂ) : Prop :=
  w ≠ 0 ∧ T ≤ Real.log ‖w‖ - Real.log c

theorem logUpperTail_sq_bound {T c : ℝ} (hc : 0 < c) {w : ℂ}
    (h : logUpperTail T c w) : Real.exp (2 * T) * c ^ 2 ≤ ‖w‖ ^ 2 := by
  have hw := norm_pos_iff.mpr h.1
  have he := Real.exp_le_exp.mpr (show T + Real.log c ≤ Real.log ‖w‖ by linarith [h.2])
  rw [Real.exp_add, Real.exp_log hc, Real.exp_log hw] at he
  rw [show 2 * T = T + T by ring, Real.exp_add]
  have hproduct : 0 ≤ (‖w‖ - Real.exp T * c) * (‖w‖ + Real.exp T * c) :=
    mul_nonneg (sub_nonneg.mpr he) (by positivity)
  nlinarith

theorem logUpperTail_probability_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T c : ℝ} (hc : 0 < c)
    {value : Ω → ℂ} (hparseval : c ^ 2 = ∫ x, ‖value x‖ ^ 2 ∂μ) :
    μ.real {x | logUpperTail T c (value x)} ≤ Real.exp (-(2 * T)) := by
  have hi : Integrable (fun x => ‖value x‖ ^ 2) μ := by
    by_contra h
    rw [integral_undef h] at hparseval
    exact (sq_pos_of_pos hc).ne' hparseval
  have hthreshold : 0 < Real.exp (2 * T) * c ^ 2 := mul_pos (Real.exp_pos _) (sq_pos_of_pos hc)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun x => sq_nonneg ‖value x‖) hi (Real.exp (2 * T) * c ^ 2)
  rw [← hparseval] at hm
  have hMarkov : μ.real {x | Real.exp (2 * T) * c ^ 2 ≤ ‖value x‖ ^ 2} ≤
      c ^ 2 / (Real.exp (2 * T) * c ^ 2) := by
    apply (le_div_iff₀ hthreshold).mpr
    simpa only [mul_comm] using hm
  have hid : c ^ 2 / (Real.exp (2 * T) * c ^ 2) = Real.exp (-(2 * T)) := by
    rw [Real.exp_neg]
    field_simp
  rw [hid] at hMarkov
  exact (measureReal_mono (fun x hx => logUpperTail_sq_bound hc hx)).trans hMarkov

theorem logDeviation_subset_two_tails {Ω : Type*} (T c : ℝ) (value : Ω → ℂ) :
    {x | logDeviation T c (value x)} ⊆
      {x | logLowerTail T c (value x)} ∪ {x | logUpperTail T c (value x)} := by
  intro x hx
  by_cases hz : value x = 0
  · exact Or.inl (Or.inl hz)
  · rcases hx with hzero | hdev
    · exact (hz hzero).elim
    · rcases le_abs.mp hdev with h | h
      · exact Or.inr ⟨hz, h⟩
      · exact Or.inl (Or.inr (by linarith))

/-- The complete terminal deviation bound, including the zero atom.
The upper-tail exponent could be relaxed to any convenient source rate. -/
theorem terminal_logDeviation_probability_le_parseval
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T c A p : ℝ} (hT : 0 < T) {value : Ω → ℂ} (hv : Measurable value)
    (h : TerminalSmallBallConclusion μ c value A p) :
    μ.real {x | logDeviation T c (value x)} ≤ p + A / T + Real.exp (-(2 * T)) := by
  apply (measureReal_mono (logDeviation_subset_two_tails T c value)).trans
  exact (measureReal_union_le _ _).trans (add_le_add
    (logLowerTail_probability_le μ hT h.coefficientNorm_pos hv (h.capped T hT))
    (logUpperTail_probability_le μ h.coefficientNorm_pos h.parseval))

end BernoulliSection8
