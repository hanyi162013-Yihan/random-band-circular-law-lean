import BernoulliSection10.FiniteIIDCoordinates
import BernoulliSection10.FiniteIIDLawOfLargeNumbers
import BernoulliSection10Complex.ResetSandwichLaw

/-! # The normalized square average of the actual independent physical atoms -/

open MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

set_option backward.isDefEq.respectTransparency false

def intervalMeanAtomSquare (W s : ℕ) (x : IntervalRows W s) : ℝ :=
  (∑ i, ∑ a, ‖x i a‖ ^ 2) / ((s * W * (3 * W) : ℕ) : ℝ)

def flattenIntervalAtoms (W s : ℕ) (x : IntervalRows W s) :
    Fin (s * W * (3 * W)) → ℂ :=
  fun i => x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

theorem flattenIntervalAtoms_measurePreserving
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (W s : ℕ) :
    MeasurePreserving (flattenIntervalAtoms W s) (intervalRowsLaw W s μ)
      (Measure.pi fun _ : Fin (s * W * (3 * W)) => μ) := by
  exact (measurePreserving_iid_reindex μ
    (finProdFinEquiv : Fin (s * W) × Fin (3 * W) ≃ Fin (s * W * (3 * W))).symm).comp
      (measurePreserving_iid_uncurry μ)

theorem intervalMeanAtomSquare_eq_flat (W s : ℕ) (x : IntervalRows W s) :
    intervalMeanAtomSquare W s x =
      (∑ i, ‖flattenIntervalAtoms W s x i‖ ^ 2) / ((s * W * (3 * W) : ℕ) : ℝ) := by
  unfold intervalMeanAtomSquare
  congr 1
  rw [← (finProdFinEquiv : Fin (s * W) × Fin (3 * W) ≃
    Fin (s * W * (3 * W))).sum_comp (fun i => ‖flattenIntervalAtoms W s x i‖ ^ 2)]
  simp only [flattenIntervalAtoms, Equiv.symm_apply_apply, Fintype.sum_prod_type]

theorem intervalAtom_measurePreserving
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (W s : ℕ)
    (i : Fin (s * W)) (a : Fin (3 * W)) :
    MeasurePreserving (fun x : IntervalRows W s => x i a) (intervalRowsLaw W s μ) μ := by
  letI : IsProbabilityMeasure (physicalRowLaw W μ) := by
    unfold physicalRowLaw
    infer_instance
  have hr : MeasurePreserving (fun x : IntervalRows W s => x i)
      (intervalRowsLaw W s μ) (physicalRowLaw W μ) := by
    simpa only [intervalRowsLaw, Measure.infinitePi_eq_pi] using
      measurePreserving_eval_infinitePi (fun _ : Fin (s * W) => physicalRowLaw W μ) i
  have ha : MeasurePreserving (fun x : PhysicalRowAtoms W => x a) (physicalRowLaw W μ) μ := by
    simpa only [physicalRowLaw, Measure.infinitePi_eq_pi] using
      measurePreserving_eval_infinitePi (fun _ : Fin (3 * W) => μ) a
  exact ha.comp hr

theorem intervalMeanAtomSquare_integrable
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L) (W s : ℕ) :
    Integrable (intervalMeanAtomSquare W s) (intervalRowsLaw W s μ) := by
  letI := hμ.toIsProbabilityMeasure
  apply Integrable.div_const
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro a _
  exact (intervalAtom_measurePreserving μ W s i a).integrable_comp_of_integrable hμ.integrable_sq

theorem intervalMeanAtomSquare_integral
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (hs : 0 < s) :
    (∫ x, intervalMeanAtomSquare W s x ∂intervalRowsLaw W s μ) = 1 := by
  letI := hμ.toIsProbabilityMeasure
  have hi (i : Fin (s * W)) (a : Fin (3 * W)) :
      Integrable (fun x : IntervalRows W s => ‖x i a‖ ^ 2) (intervalRowsLaw W s μ) :=
    (intervalAtom_measurePreserving μ W s i a).integrable_comp_of_integrable hμ.integrable_sq
  have he (i : Fin (s * W)) (a : Fin (3 * W)) :
      (∫ x : IntervalRows W s, ‖x i a‖ ^ 2 ∂intervalRowsLaw W s μ) = 1 := by
    exact (real_integral_comp_measurePreserving (intervalAtom_measurePreserving μ W s i a)
      (by fun_prop : Measurable (fun x : ℂ => ‖x‖ ^ 2))).trans hμ.variance_one
  unfold intervalMeanAtomSquare
  rw [integral_div, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun a _ => hi i a))]
  simp_rw [integral_finsetSum _ (fun a _ => hi _ a), he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, Nat.cast_mul]
  field_simp

theorem intervalMeanAtomSquare_tendsto_in_probability
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ → ℕ) (hd : Tendsto (fun n => s n * W n * (3 * W n)) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (intervalRowsLaw (W n) (s n) μ).real
      {x | ε ≤ |intervalMeanAtomSquare (W n) (s n) x - 1|}) atTop (𝓝 0) := by
  letI := hμ.toIsProbabilityMeasure
  have h := finiteIID_average_tendsto_in_probability μ (fun x : ℂ => ‖x‖ ^ 2)
    (by fun_prop) hμ.integrable_sq _ hd hε
  rw [hμ.variance_one] at h
  have he (n : ℕ) : (intervalRowsLaw (W n) (s n) μ).real
      {x | ε ≤ |intervalMeanAtomSquare (W n) (s n) x - 1|} =
      (Measure.pi fun _ : Fin (s n * W n * (3 * W n)) => μ).real
        {x | ε ≤ |(∑ i, ‖x i‖ ^ 2) / ((s n * W n * (3 * W n) : ℕ) : ℝ) - 1|} := by
    have hp := flattenIntervalAtoms_measurePreserving μ (W n) (s n)
    have hm : Measurable (fun x : Fin (s n * W n * (3 * W n)) → ℂ =>
        (∑ i, ‖x i‖ ^ 2) / ((s n * W n * (3 * W n) : ℕ) : ℝ)) := by fun_prop
    have hs : MeasurableSet {x : Fin (s n * W n * (3 * W n)) → ℂ |
        ε ≤ |(∑ i, ‖x i‖ ^ 2) / ((s n * W n * (3 * W n) : ℕ) : ℝ) - 1|} :=
      measurableSet_le measurable_const (hm.sub_const 1).norm
    simp only [measureReal_def]
    rw [← hp.map_eq, Measure.map_apply hp.measurable hs]
    apply congrArg ENNReal.toReal
    apply congrArg (intervalRowsLaw (W n) (s n) μ)
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, intervalMeanAtomSquare_eq_flat]
  simp_rw [he]
  exact h

end BernoulliSection10Complex

