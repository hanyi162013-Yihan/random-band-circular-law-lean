import BernoulliSection8.CappedAveraging

/-! # Probability bounds after exposing actual product coordinates -/

open MeasureTheory

noncomputable section

namespace BernoulliSection8

theorem prod_probability_le_of_good_fibers
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set (Ω × Ξ)} (hE : MeasurableSet E)
    {bad : Set Ω} (hbad : MeasurableSet bad) {B : ℝ} (hB : 0 ≤ B)
    (hgood : ∀ x ∉ bad, ν.real {y | (x, y) ∈ E} ≤ B) :
    (μ.prod ν).real E ≤ B + μ.real bad := by
  let f : Ω × Ξ → ℝ := E.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hE
  have hn : ∀ x, 0 ≤ f x := by
    intro x
    by_cases hx : x ∈ E <;> simp [f, hx]
  have hc : ∀ x, f x ≤ 1 := by
    intro x
    by_cases hx : x ∈ E <;> simp [f, hx]
  have hg : ∀ x ∉ bad, (∫ y, f (x, y) ∂ν) ≤ B := by
    intro x hx
    have hEx : MeasurableSet {y | (x, y) ∈ E} :=
      hE.preimage (measurable_const.prodMk measurable_id)
    have heq : (fun y => f (x, y)) = ({y | (x, y) ∈ E}).indicator (fun _ => (1 : ℝ)) := by
      funext y
      by_cases hy : (x, y) ∈ E <;> simp [f, hy]
    rw [heq, integral_indicator_const (1 : ℝ) hEx]
    simpa only [smul_eq_mul, mul_one] using hgood x hx
  have h := integral_prod_le_of_good_fibers μ ν hf (by norm_num) hB hn hc hbad hg
  rw [show (∫ x, f x ∂μ.prod ν) = (μ.prod ν).real E by
    simpa only [f, smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := μ.prod ν) (1 : ℝ) hE)] at h
  simpa only [one_mul] using h

end BernoulliSection8
