import CircularLawSection4.IIDFiberOuterIntegrable
import CircularLawSection4.UnboundedRawContinuousMemLp

/-! # Section 4 closes row resampling without global moment assumptions

Uniform centered row-fiber L² bounds imply both global square integrability
and the variance estimate. The fiber centers need not be measurable or
integrable; they cancel in the resampling difference.
-/

open MeasureTheory ProbabilityTheory CircularLawSection4
open scoped BigOperators ENNReal

noncomputable section

namespace CircularLawSection6

theorem memLp_and_variance_le_of_uniform_fibers
    {K : Type*} [MeasurableSpace K] (ν : Measure K) [IsProbabilityMeasure ν]
    {n : ℕ} (f : (Fin (n + 1) → K) → ℝ) (hf : Measurable f)
    (center : Fin (n + 1) → (Fin n → K) → ℝ) (V : ℝ)
    (hfiber : ∀ i y, MemLp (fun a => f (i.insertNth a y) - center i y) 2 ν)
    (hbound : ∀ i y, (∫ a, (f (i.insertNth a y) - center i y) ^ 2 ∂ν) ≤ V) :
    MemLp f 2 (iidMeasure ν (n + 1)) ∧
      variance f (iidMeasure ν (n + 1)) ≤ 2 * (n + 1 : ℝ) * V := by
  have hinner (i : Fin (n + 1)) (x : Fin (n + 1) → K) :
      Integrable (fun a => (f x - f (Function.update x i a)) ^ 2) ν := by
    have h := ((memLp_const (f x - center i (i.removeNth x))).sub
      (hfiber i (i.removeNth x))).integrable_sq
    convert h using 1
    funext a
    simp only [Pi.sub_apply, Fin.insertNth_removeNth]
    ring
  have houter (i : Fin (n + 1)) : Integrable
      (fun x => ∫ a, (f x - f (Function.update x i a)) ^ 2 ∂ν)
      (iidMeasure ν (n + 1)) :=
    iidRawResamplingOuter_integrable_of_fiber_memLp ν f hf i (center i) (hfiber i) (hbound i)
  have hglobal := memLp_two_of_iid_raw_replacement_integrable ν f hf hinner houter
  refine ⟨hglobal, ?_⟩
  calc
    variance f (iidMeasure ν (n + 1)) ≤
        (1 / 2 : ℝ) * ∑ i, iidRawResamplingEnergy ν f i :=
      variance_iidMeasure_le_half_sum_raw_memLp ν f hf hglobal hinner houter
    _ ≤ (1 / 2 : ℝ) * ∑ _i : Fin (n + 1), 4 * V := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun i _ =>
        iidRawResamplingEnergy_le_four_mul_of_fiber_memLp_auto ν f hf i
          (center i) (hfiber i) (hbound i))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      ring

end CircularLawSection6
