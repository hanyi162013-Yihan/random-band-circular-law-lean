import CircularLawSection4.RawContinuousEfronStein

/-!
# Continuous common-center replacement bridge

This module is the continuous-IID analogue of `PressureL2Bridge`.  If an
observable and its one-coordinate replacement both have squared distance at
most `V` from the same frozen center, their raw replacement energy is at most
`4 * V`.  The result then feeds directly into continuous Efron--Stein and the
finite-degree pressure maximum.
-/

open scoped BigOperators MeasureTheory
open MeasureTheory ProbabilityTheory

namespace CircularLawSection4

universe u

section ContinuousCenterBridge

variable {K : Type u} [MeasurableSpace K]
  (ν : Measure K) [SFinite ν] [IsProbabilityMeasure ν]

omit [SFinite ν] in
/-- For a fixed outside sample, the squared distance of the replacement
observation from an arbitrary real center is integrable under the fresh
coordinate law. -/
theorem integrable_replacement_sub_center_sq {n : ℕ}
    (f : (Fin n → K) → ℝ) (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (center : (Fin n → K) → ℝ)
    (i : Fin n) (x : Fin n → K) :
    Integrable (fun a' =>
      (f (Function.update x i a') - center x) ^ 2) ν := by
  have hmeas : Measurable (fun a' =>
      (f (Function.update x i a') - center x) ^ 2) := by
    fun_prop
  have hbound : ∀ a',
      ‖(f (Function.update x i a') - center x) ^ 2‖ ≤
        (|C| + |center x|) ^ 2 := by
    intro a'
    have hlinear :
        ‖f (Function.update x i a') - center x‖ ≤
          |C| + |center x| := by
      calc
        ‖f (Function.update x i a') - center x‖ ≤
            ‖f (Function.update x i a')‖ + ‖center x‖ := norm_sub_le _ _
        _ ≤ C + |center x| := by
          rw [Real.norm_eq_abs]
          exact add_le_add (hC (Function.update x i a')) (le_refl |center x|)
        _ ≤ |C| + |center x| := by linarith [le_abs_self C]
    rw [norm_pow]
    nlinarith [norm_nonneg (f (Function.update x i a') - center x),
      abs_nonneg C, abs_nonneg (center x)]
  exact Integrable.of_bound hmeas.aestronglyMeasurable
    ((|C| + |center x|) ^ 2) (ae_of_all ν hbound)

/-- Two continuous-product `L²` bounds around one frozen center control the
standard raw coordinate-replacement energy. -/
theorem iidRawResamplingEnergy_le_four_mul_of_center_sq_integral_le
    {n : ℕ} (f center : (Fin n → K) → ℝ)
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (i : Fin n) {V : ℝ}
    (holdInt : Integrable (fun x => (f x - center x) ^ 2)
      (iidMeasure ν n))
    (hnewInt : Integrable (fun x => ∫ a',
      (f (Function.update x i a') - center x) ^ 2 ∂ν)
      (iidMeasure ν n))
    (hold : ∫ x, (f x - center x) ^ 2 ∂iidMeasure ν n ≤ V)
    (hnew : ∫ x, ∫ a',
      (f (Function.update x i a') - center x) ^ 2
      ∂ν ∂iidMeasure ν n ≤ V) :
    iidRawResamplingEnergy ν f i ≤ 4 * V := by
  have hleftInner (x : Fin n → K) : Integrable (fun a' =>
      (f x - f (Function.update x i a')) ^ 2) ν := by
    have hmeas : Measurable (fun a' =>
        (f x - f (Function.update x i a')) ^ 2) := by
      fun_prop
    exact Integrable.of_bound hmeas.aestronglyMeasurable
      ((2 * |C|) ^ 2) (ae_of_all ν fun a' =>
        norm_sub_sq_le_bound hC x (Function.update x i a'))
  have hpoint (x : Fin n → K) :
      (∫ a', (f x - f (Function.update x i a')) ^ 2 ∂ν) ≤
        2 * (f x - center x) ^ 2 +
          2 * ∫ a',
            (f (Function.update x i a') - center x) ^ 2 ∂ν := by
    have hreplacement :=
      integrable_replacement_sub_center_sq ν f hf hC center i x
    calc
      (∫ a', (f x - f (Function.update x i a')) ^ 2 ∂ν) ≤
          ∫ a', (2 * (f x - center x) ^ 2 +
            2 * (f (Function.update x i a') - center x) ^ 2) ∂ν := by
        apply integral_mono (hleftInner x)
          ((integrable_const _).add (hreplacement.const_mul 2))
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
        rw [integral_add (integrable_const _) (hreplacement.const_mul 2),
          integral_const_mul (μ := ν) 2
            (fun _a' : K => (f x - center x) ^ 2),
          integral_const_mul (μ := ν) 2
            (fun a' => (f (Function.update x i a') - center x) ^ 2)]
        simp
  have hleftOuter : Integrable (fun x => ∫ a',
      (f x - f (Function.update x i a')) ^ 2 ∂ν)
      (iidMeasure ν n) := integrable_rawInner ν hf hC i
  have hrightOuter : Integrable (fun x =>
      2 * (f x - center x) ^ 2 +
        2 * ∫ a', (f (Function.update x i a') - center x) ^ 2 ∂ν)
      (iidMeasure ν n) :=
    (holdInt.const_mul 2).add (hnewInt.const_mul 2)
  unfold iidRawResamplingEnergy
  calc
    (∫ x, ∫ a', (f x - f (Function.update x i a')) ^ 2
        ∂ν ∂iidMeasure ν n) ≤
      ∫ x, (2 * (f x - center x) ^ 2 +
        2 * ∫ a', (f (Function.update x i a') - center x) ^ 2 ∂ν)
        ∂iidMeasure ν n :=
      integral_mono hleftOuter hrightOuter hpoint
    _ = 2 * ∫ x, (f x - center x) ^ 2 ∂iidMeasure ν n +
        2 * ∫ x, ∫ a',
          (f (Function.update x i a') - center x) ^ 2
          ∂ν ∂iidMeasure ν n := by
      rw [integral_add (holdInt.const_mul 2) (hnewInt.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 4 * V := by linarith

/-- Continuous-IID pressure concentration driven by common-center `L²`
bounds for every degree and every replaced coordinate. -/
theorem pressure_maximal_concentration_iid_of_center_sq_integral_le
    (n W : ℕ) (Y : Fin (2 * W).succ → (Fin n → K) → ℝ)
    (center : Fin (2 * W).succ → Fin n → (Fin n → K) → ℝ)
    (hY : ∀ r, Measurable (Y r)) (C : ℝ)
    (hC : ∀ r x, ‖Y r x‖ ≤ C) {V : ℝ}
    (holdInt : ∀ r i, Integrable
      (fun x => (Y r x - center r i x) ^ 2) (iidMeasure ν n))
    (hnewInt : ∀ r i, Integrable (fun x => ∫ a',
      (Y r (Function.update x i a') - center r i x) ^ 2 ∂ν)
      (iidMeasure ν n))
    (hold : ∀ r i,
      ∫ x, (Y r x - center r i x) ^ 2 ∂iidMeasure ν n ≤ V)
    (hnew : ∀ r i,
      ∫ x, ∫ a',
        (Y r (Function.update x i a') - center r i x) ^ 2
        ∂ν ∂iidMeasure ν n ≤ V) :
    (∫ ω, maxCenteredAbs (iidMeasure ν n) Y ω ∂iidMeasure ν n) ≤
      Real.sqrt (((2 * W + 1 : ℕ) : ℝ) *
        ((1 / 2 : ℝ) * (n : ℝ) * (4 * V))) := by
  apply pressure_maximal_concentration_iid_raw ν n W Y hY C hC
  intro r i
  exact iidRawResamplingEnergy_le_four_mul_of_center_sq_integral_le
    ν (Y r) (center r i) (hY r) (hC r) i
    (holdInt r i) (hnewInt r i) (hold r i) (hnew r i)

end ContinuousCenterBridge

end CircularLawSection4
