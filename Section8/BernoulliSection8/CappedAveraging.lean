import BernoulliSection8.CappedProbability
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Averaging bounded reset losses

Fubini integrates a fresh reset after freezing all outside coordinates.
An exceptional outside fiber is charged the cap. Markov is then applied
to the sum of actual losses; independence of the losses is unnecessary.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace BernoulliSection8

theorem integral_le_of_good_fibers {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) {E : Set Ω} (hE : MeasurableSet E)
    {B T : ℝ} (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hcap : ∀ᵐ x ∂μ, f x ≤ T) (hgood : ∀ᵐ x ∂μ, x ∉ E → f x ≤ B) :
    (∫ x, f x ∂μ) ≤ B + T * μ.real E := by
  have hi : Integrable (E.indicator (fun _ : Ω => T)) μ :=
    (integrable_const T).indicator hE
  have hpoint : ∀ᵐ x ∂μ, f x ≤ B + E.indicator (fun _ : Ω => T) x := by
    filter_upwards [hcap, hgood] with x hx hg
    by_cases he : x ∈ E
    · simp only [Set.indicator_of_mem he]
      linarith
    · simpa only [Set.indicator_of_notMem he, add_zero] using hg he
  have h := integral_mono_ae hf ((integrable_const B).add hi) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const B) hi, integral_const, integral_indicator_const T hE] at h
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul,
    smul_eq_mul, mul_comm, mul_one] using h

/-- The only exceptional probability here is that of the frozen outside
coordinates. The fresh Cook failure remains in the averaged bound `B`. -/
theorem integral_prod_le_of_good_fibers
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω × Ξ → ℝ} (hf : Measurable f)
    {T B : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hnonneg : ∀ x, 0 ≤ f x) (hcap : ∀ x, f x ≤ T)
    {E : Set Ω} (hE : MeasurableSet E)
    (hgood : ∀ x ∉ E, (∫ y, f (x, y) ∂ν) ≤ B) :
    (∫ x, f x ∂μ.prod ν) ≤ B + T * μ.real E := by
  have hi : Integrable f (μ.prod ν) := by
    apply (integrable_const T).mono' hf.aestronglyMeasurable
    exact ae_of_all _ fun x => by rw [Real.norm_of_nonneg (hnonneg x)]; exact hcap x
  rw [integral_prod f hi]
  apply integral_le_of_good_fibers μ hi.integral_prod_left hE hB hT
  · apply ae_of_all
    intro x
    have hix : Integrable (fun y => f (x, y)) ν := by
      apply (integrable_const T).mono' (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      exact ae_of_all _ fun y => by
        change ‖f (x, y)‖ ≤ T
        rw [Real.norm_of_nonneg (hnonneg _)]
        exact hcap _
    have h := integral_mono hix (integrable_const T) (fun y => hcap (x, y))
    simpa using h
  · exact ae_of_all _ hgood

/-- Markov applied after summing expectations. The individual losses may
share their entire past; there is no independence assumption. -/
theorem summed_loss_probability_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (loss : ι → Ω → ℝ) (bound : ι → ℝ)
    (hi : ∀ j, Integrable (loss j) μ)
    (hn : ∀ j, ∀ᵐ x ∂μ, 0 ≤ loss j x)
    (hb : ∀ j, (∫ x, loss j x ∂μ) ≤ bound j)
    {t : ℝ} (ht : 0 < t) :
    μ.real {x | t ≤ ∑ j, loss j x} ≤ (∑ j, bound j) / t := by
  have hsum : Integrable (fun x => ∑ j, loss j x) μ :=
    integrable_finsetSum _ (fun j _ => hi j)
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ ∑ j, loss j x := by
    filter_upwards [ae_all_iff.mpr hn] with x hx
    exact Finset.sum_nonneg (fun j _ => hx j)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hsum t
  rw [integral_finsetSum _ (fun j _ => hi j)] at hmarkov
  apply (le_div_iff₀ ht).mpr
  simpa only [mul_comm] using hmarkov.trans (Finset.sum_le_sum (fun j _ => hb j))

end BernoulliSection8
