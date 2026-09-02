import CircularLawSection4.UnboundedRawContinuousEfronStein

/-!
# Unbounded continuous common-center replacement bridge

The continuous common-center estimate is extended from pointwise bounded
observables to measurable `L²` observables.  All inner and outer Bochner
integrability assumptions used to compare the raw replacement energy are
kept explicit.
-/

open scoped BigOperators MeasureTheory
open MeasureTheory ProbabilityTheory

namespace CircularLawSection4

universe u

section UnboundedContinuousCenterBridge

variable {K : Type u} [MeasurableSpace K]
  (ν : Measure K) [SFinite ν] [IsProbabilityMeasure ν]

/-- Two common-center squared-integral bounds control a raw coordinate
replacement energy without any pointwise boundedness hypothesis. -/
theorem iidRawResamplingEnergy_le_four_mul_of_center_sq_integral_le_of_integrable
    {n : ℕ} (f center : (Fin n → K) → ℝ) (i : Fin n) {V : ℝ}
    (hrawInner : ∀ x, Integrable (fun a' =>
      (f x - f (Function.update x i a')) ^ 2) ν)
    (hreplacementInner : ∀ x, Integrable (fun a' =>
      (f (Function.update x i a') - center x) ^ 2) ν)
    (hrawOuter : Integrable (fun x => ∫ a',
      (f x - f (Function.update x i a')) ^ 2 ∂ν) (iidMeasure ν n))
    (holdOuter : Integrable (fun x => (f x - center x) ^ 2)
      (iidMeasure ν n))
    (hreplacementOuter : Integrable (fun x => ∫ a',
      (f (Function.update x i a') - center x) ^ 2 ∂ν)
      (iidMeasure ν n))
    (hold : ∫ x, (f x - center x) ^ 2 ∂iidMeasure ν n ≤ V)
    (hreplacement : ∫ x, ∫ a',
      (f (Function.update x i a') - center x) ^ 2
      ∂ν ∂iidMeasure ν n ≤ V) :
    iidRawResamplingEnergy ν f i ≤ 4 * V := by
  have hpoint (x : Fin n → K) :
      (∫ a', (f x - f (Function.update x i a')) ^ 2 ∂ν) ≤
        2 * (f x - center x) ^ 2 +
          2 * ∫ a',
            (f (Function.update x i a') - center x) ^ 2 ∂ν := by
    calc
      (∫ a', (f x - f (Function.update x i a')) ^ 2 ∂ν) ≤
          ∫ a', (2 * (f x - center x) ^ 2 +
            2 * (f (Function.update x i a') - center x) ^ 2) ∂ν := by
        apply integral_mono (hrawInner x)
          ((integrable_const _).add ((hreplacementInner x).const_mul 2))
        intro a'
        change (f x - f (Function.update x i a')) ^ 2 ≤
          2 * (f x - center x) ^ 2 +
            2 * (f (Function.update x i a') - center x) ^ 2
        nlinarith [sq_nonneg
          ((f x - center x) +
            (f (Function.update x i a') - center x))]
      _ = 2 * (f x - center x) ^ 2 +
          2 * ∫ a',
            (f (Function.update x i a') - center x) ^ 2 ∂ν := by
        rw [integral_add (integrable_const _)
            ((hreplacementInner x).const_mul 2),
          integral_const_mul (μ := ν) 2
            (fun _a' : K => (f x - center x) ^ 2),
          integral_const_mul (μ := ν) 2
            (fun a' => (f (Function.update x i a') - center x) ^ 2)]
        simp
  have hrightOuter : Integrable (fun x =>
      2 * (f x - center x) ^ 2 +
        2 * ∫ a', (f (Function.update x i a') - center x) ^ 2 ∂ν)
      (iidMeasure ν n) :=
    (holdOuter.const_mul 2).add (hreplacementOuter.const_mul 2)
  unfold iidRawResamplingEnergy
  calc
    (∫ x, ∫ a', (f x - f (Function.update x i a')) ^ 2
        ∂ν ∂iidMeasure ν n) ≤
      ∫ x, (2 * (f x - center x) ^ 2 +
        2 * ∫ a', (f (Function.update x i a') - center x) ^ 2 ∂ν)
        ∂iidMeasure ν n :=
      integral_mono hrawOuter hrightOuter hpoint
    _ = 2 * ∫ x, (f x - center x) ^ 2 ∂iidMeasure ν n +
        2 * ∫ x, ∫ a',
          (f (Function.update x i a') - center x) ^ 2
          ∂ν ∂iidMeasure ν n := by
      rw [integral_add (holdOuter.const_mul 2)
          (hreplacementOuter.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 4 * V := by linarith

/-- Continuous-IID pressure concentration for measurable `L²` observables,
driven by explicit common-center inner and outer integrability hypotheses. -/
theorem pressure_maximal_concentration_iid_of_center_sq_integral_le_memLp
    (n W : ℕ) (Y : Fin (2 * W).succ → (Fin n → K) → ℝ)
    (center : Fin (2 * W).succ → Fin n → (Fin n → K) → ℝ)
    (hY : ∀ r, Measurable (Y r))
    (hY2 : ∀ r, MemLp (Y r) 2 (iidMeasure ν n)) {V : ℝ}
    (hrawInner : ∀ r i x, Integrable (fun a' =>
      (Y r x - Y r (Function.update x i a')) ^ 2) ν)
    (hreplacementInner : ∀ r i x, Integrable (fun a' =>
      (Y r (Function.update x i a') - center r i x) ^ 2) ν)
    (hrawOuter : ∀ r i, Integrable (fun x => ∫ a',
      (Y r x - Y r (Function.update x i a')) ^ 2 ∂ν)
      (iidMeasure ν n))
    (holdOuter : ∀ r i, Integrable
      (fun x => (Y r x - center r i x) ^ 2) (iidMeasure ν n))
    (hreplacementOuter : ∀ r i, Integrable (fun x => ∫ a',
      (Y r (Function.update x i a') - center r i x) ^ 2 ∂ν)
      (iidMeasure ν n))
    (hold : ∀ r i,
      ∫ x, (Y r x - center r i x) ^ 2 ∂iidMeasure ν n ≤ V)
    (hreplacement : ∀ r i,
      ∫ x, ∫ a',
        (Y r (Function.update x i a') - center r i x) ^ 2
        ∂ν ∂iidMeasure ν n ≤ V) :
    (∫ ω, maxCenteredAbs (iidMeasure ν n) Y ω ∂iidMeasure ν n) ≤
      Real.sqrt (((2 * W + 1 : ℕ) : ℝ) *
        ((1 / 2 : ℝ) * (n : ℝ) * (4 * V))) := by
  apply pressure_maximal_concentration_iid_raw_memLp
    ν n W Y hY hY2 hrawInner hrawOuter
  intro r i
  exact iidRawResamplingEnergy_le_four_mul_of_center_sq_integral_le_of_integrable
    ν (Y r) (center r i) i (hrawInner r i) (hreplacementInner r i)
    (hrawOuter r i) (holdOuter r i) (hreplacementOuter r i)
    (hold r i) (hreplacement r i)

end UnboundedContinuousCenterBridge

end CircularLawSection4
