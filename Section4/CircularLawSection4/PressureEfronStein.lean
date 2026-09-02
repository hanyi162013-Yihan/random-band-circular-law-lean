import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import CircularLawSection4.PressureProbability

/-!
# Finite uniform Efron--Stein prototype

This file proves the algebraic finite-product core of Efron--Stein for a
uniform product of a nonempty finite type.  It is intentionally independent
of the operator-valued pressure application.
-/

open scoped BigOperators

namespace CircularLawSection4

universe u

/-- Uniform average of a real function on a nonempty finite type. -/
noncomputable def uniformAverage {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

/-- Variance with respect to the uniform probability law on a finite type. -/
noncomputable def uniformVariance {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : ℝ :=
  uniformAverage fun x => (f x - uniformAverage f) ^ 2

theorem uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by
  simp [uniformAverage, Fintype.card_ne_zero]

theorem uniformAverage_add {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → ℝ) :
    uniformAverage (fun x => f x + g x) = uniformAverage f + uniformAverage g := by
  unfold uniformAverage
  rw [Finset.sum_add_distrib]
  ring

theorem uniformAverage_sub {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → ℝ) :
    uniformAverage (fun x => f x - g x) = uniformAverage f - uniformAverage g := by
  unfold uniformAverage
  rw [Finset.sum_sub_distrib]
  ring

theorem uniformAverage_mul_const {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (c : ℝ) :
    uniformAverage (fun x => f x * c) = uniformAverage f * c := by
  unfold uniformAverage
  rw [← Finset.sum_mul]
  ring

theorem uniformAverage_const_mul {α : Type*} [Fintype α] [Nonempty α]
    (c : ℝ) (f : α → ℝ) :
    uniformAverage (fun x => c * f x) = c * uniformAverage f := by
  unfold uniformAverage
  rw [← Finset.mul_sum]
  ring

theorem uniformAverage_mono {α : Type*} [Fintype α] [Nonempty α]
    {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    uniformAverage f ≤ uniformAverage g := by
  unfold uniformAverage
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun x _ => h x
  · positivity

theorem uniformAverage_fintypeSum {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] (f : α → β → ℝ) :
    uniformAverage (fun x => ∑ i, f x i) =
      ∑ i, uniformAverage (fun x => f x i) := by
  classical
  induction (Finset.univ : Finset β) using Finset.induction_on with
  | empty => simp [uniformAverage_const]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [uniformAverage_add, ih]

theorem uniformAverage_prod {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (f : α × β → ℝ) :
    uniformAverage f = uniformAverage (fun a => uniformAverage (fun b => f (a, b))) := by
  classical
  unfold uniformAverage
  rw [Fintype.sum_prod_type]
  simp only [Nat.cast_mul, Fintype.card_prod]
  have hsum :
      (∑ a : α, (∑ b : β, f (a, b)) / (Fintype.card β : ℝ)) =
        (∑ a : α, ∑ b : β, f (a, b)) / (Fintype.card β : ℝ) := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
  rw [hsum]
  field_simp [Fintype.card_ne_zero]

theorem uniformAverage_equiv {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) (f : β → ℝ) :
    uniformAverage (fun x => f (e x)) = uniformAverage f := by
  unfold uniformAverage
  rw [e.sum_comp]
  rw [Fintype.card_congr e]

theorem uniformAverage_comm {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (f : α → β → ℝ) :
    uniformAverage (fun a => uniformAverage (fun b => f a b)) =
      uniformAverage (fun b => uniformAverage (fun a => f a b)) := by
  classical
  unfold uniformAverage
  have hleft :
      (∑ a : α, (∑ b : β, f a b) / (Fintype.card β : ℝ)) =
        (∑ a : α, ∑ b : β, f a b) / (Fintype.card β : ℝ) := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
  have hright :
      (∑ b : β, (∑ a : α, f a b) / (Fintype.card α : ℝ)) =
        (∑ b : β, ∑ a : α, f a b) / (Fintype.card α : ℝ) := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
  rw [hleft, hright, Finset.sum_comm]
  field_simp [Fintype.card_ne_zero]

theorem uniformAverage_sq_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) :
    (uniformAverage f) ^ 2 ≤ uniformAverage (fun x => (f x) ^ 2) := by
  classical
  simpa [uniformAverage] using
    (sum_div_card_sq_le_sum_sq_div_card
      (s := (Finset.univ : Finset α)) (f := f))

theorem uniformVariance_eq_secondMoment_sub {α : Type*}
    [Fintype α] [Nonempty α] (f : α → ℝ) :
    uniformVariance f = uniformAverage (fun x => (f x) ^ 2) - (uniformAverage f) ^ 2 := by
  let m := uniformAverage f
  calc
    uniformVariance f =
        uniformAverage (fun x => (f x) ^ 2 - (2 * m) * f x + m ^ 2) := by
      unfold uniformVariance
      congr 1
      funext x
      dsimp [m]
      ring
    _ = uniformAverage (fun x => (f x) ^ 2) -
          uniformAverage (fun x => (2 * m) * f x) +
          uniformAverage (fun _x : α => m ^ 2) := by
      rw [uniformAverage_add, uniformAverage_sub]
    _ = uniformAverage (fun x => (f x) ^ 2) - (uniformAverage f) ^ 2 := by
      rw [uniformAverage_const_mul, uniformAverage_const]
      dsimp [m]
      ring

theorem uniformVariance_nonneg {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : 0 ≤ uniformVariance f := by
  rw [uniformVariance_eq_secondMoment_sub]
  linarith [uniformAverage_sq_le f]

theorem uniformVariance_eq_half_pairDifference {α : Type*}
    [Fintype α] [Nonempty α] (f : α → ℝ) :
    uniformVariance f =
      (1 / 2 : ℝ) * uniformAverage (fun x =>
        uniformAverage (fun y => (f x - f y) ^ 2)) := by
  let m := uniformAverage f
  let q := uniformAverage (fun x => (f x) ^ 2)
  have hinner (x : α) :
      uniformAverage (fun y => (f x - f y) ^ 2) =
        (f x) ^ 2 - (2 * m) * f x + q := by
    calc
      uniformAverage (fun y => (f x - f y) ^ 2) =
          uniformAverage (fun y => (f x) ^ 2 - (2 * f x) * f y + (f y) ^ 2) := by
        congr 1
        funext y
        ring
      _ = uniformAverage (fun _y : α => (f x) ^ 2) -
            uniformAverage (fun y => (2 * f x) * f y) +
            uniformAverage (fun y => (f y) ^ 2) := by
        rw [uniformAverage_add, uniformAverage_sub]
      _ = (f x) ^ 2 - (2 * m) * f x + q := by
        rw [uniformAverage_const, uniformAverage_const_mul]
        ring
  rw [uniformVariance_eq_secondMoment_sub]
  simp_rw [hinner]
  rw [uniformAverage_add, uniformAverage_sub, uniformAverage_const_mul,
    uniformAverage_const]
  dsimp [m, q]
  ring

/-- A recursive product type with `n` independent coordinates in `α`. -/
def UniformCube (α : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => α × UniformCube α n

instance uniformCubeFintype {α : Type*} [Fintype α] :
    ∀ n, Fintype (UniformCube α n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
      letI : Fintype (UniformCube α n) := uniformCubeFintype n
      exact inferInstanceAs (Fintype (α × UniformCube α n))

instance uniformCubeNonempty {α : Type*} [Nonempty α] :
    ∀ n, Nonempty (UniformCube α n)
  | 0 => inferInstanceAs (Nonempty PUnit)
  | n + 1 =>
      ⟨Classical.choice (inferInstance : Nonempty α),
        Classical.choice (uniformCubeNonempty n)⟩

/-- We use the discrete measurable structure on the finite product cube. -/
instance uniformCubeMeasurableSpace {α : Type*} {n : ℕ} :
    MeasurableSpace (UniformCube α n) := ⊤

instance uniformCubeMeasurableSingletonClass {α : Type*} {n : ℕ} :
    MeasurableSingletonClass (UniformCube α n) := by infer_instance

/-- Uniform probability measure on the finite product cube. -/
noncomputable def uniformCubeMeasure {α : Type*} [Fintype α] [Nonempty α] (n : ℕ) :
    MeasureTheory.Measure (UniformCube α n) :=
  (PMF.uniformOfFintype (UniformCube α n)).toMeasure

instance uniformCubeMeasure_isProbabilityMeasure {α : Type*}
    [Fintype α] [Nonempty α] (n : ℕ) :
    MeasureTheory.IsProbabilityMeasure (uniformCubeMeasure (α := α) n) := by
  unfold uniformCubeMeasure
  infer_instance

theorem integral_uniformOfFintype_eq_uniformAverage {γ : Type*}
    [Fintype γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (f : γ → ℝ) :
    (∫ x, f x ∂(PMF.uniformOfFintype γ).toMeasure) = uniformAverage f := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, uniformAverage]
  rw [← Finset.mul_sum]
  rw [div_eq_mul_inv]
  ring

theorem variance_uniformCubeMeasure_eq_uniformVariance {α : Type*}
    [Fintype α] [Nonempty α] {n : ℕ} (f : UniformCube α n → ℝ) :
    ProbabilityTheory.variance f (uniformCubeMeasure n) = uniformVariance f := by
  rw [ProbabilityTheory.variance_eq_integral (measurable_of_finite f).aemeasurable]
  simp only [uniformCubeMeasure, integral_uniformOfFintype_eq_uniformAverage]
  rfl

/-- Expected squared change caused by independently resampling coordinate `i`.

The recursion is exactly the uniform product expectation: at the head it
averages over the tail, the old head, and an independent new head; in the
tail it additionally averages over the unchanged head.
-/
noncomputable def uniformResamplingEnergy {α : Type*} [Fintype α] [Nonempty α] :
    {n : ℕ} → (UniformCube α n → ℝ) → Fin n → ℝ
  | 0, _, i => Fin.elim0 i
  | n + 1, f, i => Fin.cases
      (uniformAverage fun a : α =>
        uniformAverage fun a' : α =>
          uniformAverage fun tail : UniformCube α n =>
            (f (a, tail) - f (a', tail)) ^ 2)
      (fun j => uniformAverage fun a : α =>
        uniformResamplingEnergy (fun tail => f (a, tail)) j)
      i

/-- Replace coordinate `i` by a new value. -/
def uniformCubeReplace {α : Type*} :
    {n : ℕ} → UniformCube α n → Fin n → α → UniformCube α n
  | 0, _, i, _ => Fin.elim0 i
  | _n + 1, (a, tail), i, a' => Fin.cases
      (a', tail)
      (fun j => (a, uniformCubeReplace tail j a'))
      i

/-- The recursive energy is exactly the expected squared difference after
replacing the indicated coordinate by an independent uniform value. -/
theorem uniformResamplingEnergy_eq_replace_average {α : Type*}
    [Fintype α] [Nonempty α] :
    ∀ {n : ℕ} (f : UniformCube α n → ℝ) (i : Fin n),
      uniformResamplingEnergy f i =
        uniformAverage (fun x => uniformAverage (fun a' : α =>
          (f x - f (uniformCubeReplace x i a')) ^ 2)) := by
  intro n
  induction n with
  | zero =>
      intro f i
      exact Fin.elim0 i
  | succ n ih =>
      intro f i
      refine Fin.cases ?_ (fun j => ?_) i
      · change uniformResamplingEnergy f 0 =
          uniformAverage (fun x : α × UniformCube α n =>
            uniformAverage (fun a' : α =>
              (f x - f (uniformCubeReplace x 0 a')) ^ 2))
        simp only [uniformResamplingEnergy, Fin.cases_zero]
        rw [uniformAverage_prod]
        simp only [uniformCubeReplace]
        congr 1
        funext a
        exact uniformAverage_comm (fun a' tail =>
          (f (a, tail) - f (a', tail)) ^ 2)
      · change uniformResamplingEnergy f j.succ =
          uniformAverage (fun x : α × UniformCube α n =>
            uniformAverage (fun a' : α =>
              (f x - f (uniformCubeReplace x j.succ a')) ^ 2))
        simp only [uniformResamplingEnergy, Fin.cases_succ]
        rw [uniformAverage_prod]
        simp only [uniformCubeReplace]
        congr 1
        funext a
        exact ih (fun tail => f (a, tail)) j

theorem uniformResamplingEnergy_le_of_replace_sq_le {α : Type*}
    [Fintype α] [Nonempty α] {n : ℕ}
    (f : UniformCube α n → ℝ) (i : Fin n) {D : ℝ}
    (hD : ∀ x a', (f x - f (uniformCubeReplace x i a')) ^ 2 ≤ D) :
    uniformResamplingEnergy f i ≤ D := by
  rw [uniformResamplingEnergy_eq_replace_average]
  calc
    uniformAverage (fun x => uniformAverage (fun a' : α =>
        (f x - f (uniformCubeReplace x i a')) ^ 2)) ≤
        uniformAverage (fun _x : UniformCube α n => D) := by
      apply uniformAverage_mono
      intro x
      calc
        uniformAverage (fun a' : α =>
            (f x - f (uniformCubeReplace x i a')) ^ 2) ≤
            uniformAverage (fun _a' : α => D) :=
          uniformAverage_mono fun a' => hD x a'
        _ = D := uniformAverage_const D
    _ = D := uniformAverage_const D

theorem uniformVariance_prod_decomposition {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (f : α × β → ℝ) :
    uniformVariance f =
      uniformAverage (fun a => uniformVariance (fun b => f (a, b))) +
      uniformVariance (fun a => uniformAverage (fun b => f (a, b))) := by
  rw [uniformVariance_eq_secondMoment_sub]
  rw [uniformVariance_eq_secondMoment_sub]
  simp_rw [uniformVariance_eq_secondMoment_sub]
  rw [uniformAverage_prod]
  rw [uniformAverage_prod]
  simp_rw [uniformAverage_sub]
  ring

theorem uniformVariance_average_le_headEnergy {α : Type*}
    [Fintype α] [Nonempty α] {n : ℕ}
    (f : UniformCube α (n + 1) → ℝ) :
    uniformVariance (fun a : α => uniformAverage (fun tail => f (a, tail))) ≤
      (1 / 2 : ℝ) * uniformResamplingEnergy f 0 := by
  rw [uniformVariance_eq_half_pairDifference]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply uniformAverage_mono
  intro a
  apply uniformAverage_mono
  intro a'
  rw [← uniformAverage_sub]
  exact uniformAverage_sq_le (fun tail => f (a, tail) - f (a', tail))

/-- Finite-uniform Efron--Stein inequality.

For `n` independent uniform coordinates, variance is at most one half of the
sum of the expected squared changes obtained by replacing one coordinate by
an independent copy.
-/
theorem uniformVariance_le_half_sum_resampling {α : Type*}
    [Fintype α] [Nonempty α] :
    ∀ {n : ℕ} (f : UniformCube α n → ℝ),
      uniformVariance f ≤
        (1 / 2 : ℝ) * ∑ i, uniformResamplingEnergy f i := by
  intro n
  induction n with
  | zero =>
      intro f
      have hf : f = fun _ => f PUnit.unit := by
        funext x
        cases x
        rfl
      rw [hf]
      simp [uniformVariance, uniformAverage_const]
  | succ n ih =>
      intro f
      have hdecomp :
          uniformVariance f =
            uniformAverage (fun a : α =>
              uniformVariance (fun tail : UniformCube α n => f (a, tail))) +
            uniformVariance (fun a : α =>
              uniformAverage (fun tail : UniformCube α n => f (a, tail))) :=
        uniformVariance_prod_decomposition
          (fun p : α × UniformCube α n => f p)
      rw [hdecomp]
      have htail :
          uniformAverage (fun a : α =>
            uniformVariance (fun tail => f (a, tail))) ≤
          uniformAverage (fun a : α =>
            (1 / 2 : ℝ) * ∑ j,
              uniformResamplingEnergy (fun tail => f (a, tail)) j) :=
        uniformAverage_mono fun a => ih (fun tail => f (a, tail))
      have hhead := uniformVariance_average_le_headEnergy f
      calc
        uniformAverage (fun a : α => uniformVariance (fun tail => f (a, tail))) +
            uniformVariance (fun a : α => uniformAverage (fun tail => f (a, tail))) ≤
          uniformAverage (fun a : α =>
              (1 / 2 : ℝ) * ∑ j,
                uniformResamplingEnergy (fun tail => f (a, tail)) j) +
            (1 / 2 : ℝ) * uniformResamplingEnergy f 0 := add_le_add htail hhead
        _ = (1 / 2 : ℝ) * ∑ i, uniformResamplingEnergy f i := by
          rw [uniformAverage_const_mul, uniformAverage_fintypeSum]
          rw [Fin.sum_univ_succ]
          simp only [uniformResamplingEnergy, Fin.cases_zero, Fin.cases_succ]
          ring

/-- A uniform bound on every coordinate-resampling energy yields the
linear-in-the-number-of-coordinates variance estimate. -/
theorem uniformVariance_le_half_card_mul_of_resampling_le {α : Type*}
    [Fintype α] [Nonempty α] {n : ℕ} (f : UniformCube α n → ℝ)
    {D : ℝ} (hD : ∀ i, uniformResamplingEnergy f i ≤ D) :
    uniformVariance f ≤ (1 / 2 : ℝ) * (n : ℝ) * D := by
  refine (uniformVariance_le_half_sum_resampling f).trans ?_
  calc
    (1 / 2 : ℝ) * ∑ i, uniformResamplingEnergy f i ≤
        (1 / 2 : ℝ) * ∑ _i : Fin n, D := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun i _ => hD i
    _ = (1 / 2 : ℝ) * (n : ℝ) * D := by
      simp
      ring

/-- Pointwise squared replacement bounds imply the Efron--Stein variance
bound. -/
theorem uniformVariance_le_half_card_mul_of_replace_sq_le {α : Type*}
    [Fintype α] [Nonempty α] {n : ℕ} (f : UniformCube α n → ℝ)
    {D : ℝ}
    (hD : ∀ i x a', (f x - f (uniformCubeReplace x i a')) ^ 2 ≤ D) :
    uniformVariance f ≤ (1 / 2 : ℝ) * (n : ℝ) * D := by
  apply uniformVariance_le_half_card_mul_of_resampling_le f
  intro i
  exact uniformResamplingEnergy_le_of_replace_sq_le f i (hD i)

/-- Every real function on a finite discrete probability space belongs to
all finite `Lᵖ` spaces. -/
theorem memLp_uniformCube {α : Type*} [Fintype α] [Nonempty α]
    {n : ℕ} (f : UniformCube α n → ℝ) (p : ENNReal) :
    MeasureTheory.MemLp f p (uniformCubeMeasure n) := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun x : UniformCube α n => ‖f x‖)
  exact MeasureTheory.MemLp.of_bound
    (measurable_of_finite f).aestronglyMeasurable C
    (MeasureTheory.ae_of_all _ hC)

/-- Measure-theoretic form of the uniform finite-product Efron--Stein
corollary, ready for the maximal-concentration closure. -/
theorem variance_uniformCubeMeasure_le_half_card_mul_of_resampling_le
    {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
    (f : UniformCube α n → ℝ) {D : ℝ}
    (hD : ∀ i, uniformResamplingEnergy f i ≤ D) :
    ProbabilityTheory.variance f (uniformCubeMeasure n) ≤
      (1 / 2 : ℝ) * (n : ℝ) * D := by
  rw [variance_uniformCubeMeasure_eq_uniformVariance]
  exact uniformVariance_le_half_card_mul_of_resampling_le f hD

/-- Efron--Stein plus the existing finite-degree maximal closure.

This is the complete finite-uniform probabilistic chain.  The remaining
paper-specific input is a bound on the replacement energy of each pressure
observable `Y r`.
-/
theorem pressure_maximal_concentration_uniform_resampling
    {α : Type*} [Fintype α] [Nonempty α]
    (n W : ℕ) (Y : Fin (2 * W).succ → UniformCube α n → ℝ)
    {D : ℝ} (hD : ∀ r i, uniformResamplingEnergy (Y r) i ≤ D) :
    (∫ ω, maxCenteredAbs (uniformCubeMeasure n) Y ω
        ∂(uniformCubeMeasure n)) ≤
      Real.sqrt (((2 * W + 1 : ℕ) : ℝ) *
        ((1 / 2 : ℝ) * (n : ℝ) * D)) := by
  apply pressure_maximal_concentration_of_variance W
  · intro r
    exact memLp_uniformCube (Y r) 2
  · intro r
    exact variance_uniformCubeMeasure_le_half_card_mul_of_resampling_le
      (Y r) (hD r)

/-- Pointwise bounded-difference specialization of the complete finite
uniform pressure-maximal chain. -/
theorem pressure_maximal_concentration_uniform_replace_sq
    {α : Type*} [Fintype α] [Nonempty α]
    (n W : ℕ) (Y : Fin (2 * W).succ → UniformCube α n → ℝ)
    {D : ℝ}
    (hD : ∀ r i x a',
      (Y r x - Y r (uniformCubeReplace x i a')) ^ 2 ≤ D) :
    (∫ ω, maxCenteredAbs (uniformCubeMeasure n) Y ω
        ∂(uniformCubeMeasure n)) ≤
      Real.sqrt (((2 * W + 1 : ℕ) : ℝ) *
        ((1 / 2 : ℝ) * (n : ℝ) * D)) := by
  apply pressure_maximal_concentration_uniform_resampling n W Y
  intro r i
  exact uniformResamplingEnergy_le_of_replace_sq_le (Y r) i (hD r i)

end CircularLawSection4
