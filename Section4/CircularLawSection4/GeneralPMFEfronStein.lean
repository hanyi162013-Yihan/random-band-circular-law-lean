import CircularLawSection4.PressureEfronStein
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Data.ENNReal.BigOperators

/-!
# Efron--Stein for a finite product of an arbitrary PMF

This extends the uniform finite cube in `PressureEfronStein` to an arbitrary
probability mass function on the coordinate alphabet.  Zero-probability
atoms are allowed.  The product PMF, its coordinate-replacement energy, and
the factor `1/2` Efron--Stein inequality are all explicit.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace CircularLawSection4

universe u

section OneCoordinate

variable {α : Type u} [Fintype α]

/-- Expectation under an arbitrary PMF on a finite type. -/
noncomputable def pmfAverage (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a, (p a).toReal * f a

theorem sum_pmf_toReal (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  have hp : ∑ a, p a = 1 := by
    simpa only [tsum_fintype] using p.tsum_coe
  have hp' := congrArg ENNReal.toReal hp
  rw [ENNReal.toReal_sum (fun a _ => p.apply_ne_top a), ENNReal.toReal_one] at hp'
  exact hp'

theorem pmfAverage_const (p : PMF α) (c : ℝ) :
    pmfAverage p (fun _ : α => c) = c := by
  unfold pmfAverage
  rw [← Finset.sum_mul, sum_pmf_toReal]
  simp

theorem pmfAverage_add (p : PMF α) (f g : α → ℝ) :
    pmfAverage p (fun a => f a + g a) = pmfAverage p f + pmfAverage p g := by
  unfold pmfAverage
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

theorem pmfAverage_sub (p : PMF α) (f g : α → ℝ) :
    pmfAverage p (fun a => f a - g a) = pmfAverage p f - pmfAverage p g := by
  unfold pmfAverage
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

theorem pmfAverage_const_mul (p : PMF α) (c : ℝ) (f : α → ℝ) :
    pmfAverage p (fun a => c * f a) = c * pmfAverage p f := by
  unfold pmfAverage
  calc
    (∑ a, (p a).toReal * (c * f a)) =
        ∑ a, c * ((p a).toReal * f a) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = c * ∑ a, (p a).toReal * f a := by rw [Finset.mul_sum]

theorem pmfAverage_mul_const (p : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfAverage p (fun a => f a * c) = pmfAverage p f * c := by
  unfold pmfAverage
  calc
    (∑ a, (p a).toReal * (f a * c)) =
        ∑ a, ((p a).toReal * f a) * c := by
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = (∑ a, (p a).toReal * f a) * c := by rw [Finset.sum_mul]

theorem pmfAverage_mono (p : PMF α) {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : pmfAverage p f ≤ pmfAverage p g := by
  unfold pmfAverage
  exact Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_left (h a) (ENNReal.toReal_nonneg)

theorem pmfAverage_fintypeSum (p : PMF α) {β : Type*} [Fintype β]
    (f : α → β → ℝ) :
    pmfAverage p (fun a => ∑ i, f a i) = ∑ i, pmfAverage p (fun a => f a i) := by
  classical
  induction (Finset.univ : Finset β) using Finset.induction_on with
  | empty => simp [pmfAverage_const]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [pmfAverage_add, ih]

theorem pmfAverage_comm (p : PMF α) (f : α → α → ℝ) :
    pmfAverage p (fun a => pmfAverage p (fun b => f a b)) =
      pmfAverage p (fun b => pmfAverage p (fun a => f a b)) := by
  classical
  unfold pmfAverage
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end OneCoordinate

section ProductPMF

variable {α : Type u} [Fintype α]

/-- Product weight on the recursive cube. -/
noncomputable def pmfCubeWeight (p : PMF α) :
    (n : ℕ) → UniformCube α n → ℝ≥0∞
  | 0, _ => 1
  | n + 1, x => p x.1 * pmfCubeWeight p n x.2

theorem sum_pmfCubeWeight (p : PMF α) :
    ∀ n, ∑ x : UniformCube α n, pmfCubeWeight p n x = 1 := by
  intro n
  induction n with
  | zero =>
      change (∑ _x : PUnit, (1 : ℝ≥0∞)) = 1
      simp
  | succ n ih =>
      change (∑ x : α × UniformCube α n,
        p x.1 * pmfCubeWeight p n x.2) = 1
      rw [Fintype.sum_prod_type]
      calc
        (∑ a, ∑ tail, p a * pmfCubeWeight p n tail) =
            ∑ a, p a * ∑ tail, pmfCubeWeight p n tail := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
        _ = ∑ a, p a := by rw [ih]; simp
        _ = 1 := by simpa only [tsum_fintype] using p.tsum_coe

/-- The explicit IID product PMF on the recursive finite cube. -/
noncomputable def pmfCubePMF (p : PMF α) (n : ℕ) : PMF (UniformCube α n) :=
  PMF.ofFintype (pmfCubeWeight p n) (sum_pmfCubeWeight p n)

/-- The actual probability measure corresponding to the product PMF. -/
noncomputable def pmfCubeMeasure (p : PMF α) (n : ℕ) :
    Measure (UniformCube α n) :=
  (pmfCubePMF p n).toMeasure

instance pmfCubeMeasure_isProbabilityMeasure (p : PMF α) (n : ℕ) :
    IsProbabilityMeasure (pmfCubeMeasure p n) := by
  unfold pmfCubeMeasure
  infer_instance

/-- Product expectation written as a finite weighted sum. -/
noncomputable def pmfCubeAverage (p : PMF α) {n : ℕ}
    (f : UniformCube α n → ℝ) : ℝ :=
  ∑ x, (pmfCubeWeight p n x).toReal * f x

theorem integral_pmfCubeMeasure_eq_pmfCubeAverage (p : PMF α) {n : ℕ}
    (f : UniformCube α n → ℝ) :
    (∫ x, f x ∂pmfCubeMeasure p n) = pmfCubeAverage p f := by
  rw [pmfCubeMeasure, PMF.integral_eq_sum]
  simp only [pmfCubePMF, PMF.ofFintype_apply, smul_eq_mul, pmfCubeAverage]

theorem pmfCubeAverage_zero (p : PMF α) (f : UniformCube α 0 → ℝ) :
    pmfCubeAverage p f = f PUnit.unit := by
  let g : PUnit → ℝ := fun x => f x
  change (∑ x : PUnit, (1 : ℝ≥0∞).toReal * g x) = g PUnit.unit
  simp only [ENNReal.toReal_one, one_mul]
  classical
  rw [show (Finset.univ : Finset PUnit) = {PUnit.unit} by
    ext x
    simp]
  simp

theorem pmfCubeAverage_succ (p : PMF α) {n : ℕ}
    (f : UniformCube α (n + 1) → ℝ) :
    pmfCubeAverage p f =
      pmfAverage p (fun a => pmfCubeAverage p (fun tail => f (a, tail))) := by
  let g : α × UniformCube α n → ℝ := fun x => f x
  change (∑ x : α × UniformCube α n,
      (p x.1 * pmfCubeWeight p n x.2).toReal * g x) =
    ∑ a, (p a).toReal *
      (∑ tail, (pmfCubeWeight p n tail).toReal * g (a, tail))
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail _
  rw [ENNReal.toReal_mul]
  ring

theorem pmfCubeAverage_const (p : PMF α) {n : ℕ} (c : ℝ) :
    pmfCubeAverage p (fun _ : UniformCube α n => c) = c := by
  rw [← integral_pmfCubeMeasure_eq_pmfCubeAverage]
  simp

theorem pmfCubeAverage_add (p : PMF α) {n : ℕ}
    (f g : UniformCube α n → ℝ) :
    pmfCubeAverage p (fun x => f x + g x) =
      pmfCubeAverage p f + pmfCubeAverage p g := by
  unfold pmfCubeAverage
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

theorem pmfCubeAverage_sub (p : PMF α) {n : ℕ}
    (f g : UniformCube α n → ℝ) :
    pmfCubeAverage p (fun x => f x - g x) =
      pmfCubeAverage p f - pmfCubeAverage p g := by
  unfold pmfCubeAverage
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

theorem pmfCubeAverage_const_mul (p : PMF α) {n : ℕ}
    (c : ℝ) (f : UniformCube α n → ℝ) :
    pmfCubeAverage p (fun x => c * f x) = c * pmfCubeAverage p f := by
  unfold pmfCubeAverage
  calc
    (∑ x, (pmfCubeWeight p n x).toReal * (c * f x)) =
        ∑ x, c * ((pmfCubeWeight p n x).toReal * f x) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = c * ∑ x, (pmfCubeWeight p n x).toReal * f x := by rw [Finset.mul_sum]

theorem pmfCubeAverage_mono (p : PMF α) {n : ℕ}
    {f g : UniformCube α n → ℝ} (h : ∀ x, f x ≤ g x) :
    pmfCubeAverage p f ≤ pmfCubeAverage p g := by
  unfold pmfCubeAverage
  exact Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left (h x) ENNReal.toReal_nonneg

theorem pmfCubeAverage_fintypeSum (p : PMF α) {n : ℕ}
    {β : Type*} [Fintype β] (f : UniformCube α n → β → ℝ) :
    pmfCubeAverage p (fun x => ∑ i, f x i) =
      ∑ i, pmfCubeAverage p (fun x => f x i) := by
  classical
  induction (Finset.univ : Finset β) using Finset.induction_on with
  | empty => simp [pmfCubeAverage_const]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [pmfCubeAverage_add, ih]

/-- Variance with respect to the explicit product PMF. -/
noncomputable def pmfCubeVariance (p : PMF α) {n : ℕ}
    (f : UniformCube α n → ℝ) : ℝ :=
  pmfCubeAverage p fun x => (f x - pmfCubeAverage p f) ^ 2

theorem variance_pmfCubeMeasure_eq_pmfCubeVariance (p : PMF α) {n : ℕ}
    (f : UniformCube α n → ℝ) :
    variance f (pmfCubeMeasure p n) = pmfCubeVariance p f := by
  rw [variance_eq_integral (measurable_of_finite f).aemeasurable]
  simp only [pmfCubeVariance, integral_pmfCubeMeasure_eq_pmfCubeAverage]

theorem memLp_pmfCube (p : PMF α) {n : ℕ}
    (f : UniformCube α n → ℝ) (r : ENNReal) :
    MemLp f r (pmfCubeMeasure p n) := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun x : UniformCube α n => ‖f x‖)
  exact MemLp.of_bound (measurable_of_finite f).aestronglyMeasurable C
    (ae_of_all _ hC)

theorem pmfCubeVariance_eq_secondMoment_sub (p : PMF α) {n : ℕ}
    (f : UniformCube α n → ℝ) :
    pmfCubeVariance p f =
      pmfCubeAverage p (fun x => f x ^ 2) - (pmfCubeAverage p f) ^ 2 := by
  rw [← variance_pmfCubeMeasure_eq_pmfCubeVariance]
  rw [variance_eq_sub (memLp_pmfCube p f 2)]
  simp only [integral_pmfCubeMeasure_eq_pmfCubeAverage, Pi.pow_apply]

theorem pmfCubeAverage_sq_le (p : PMF α) {n : ℕ}
    (f : UniformCube α n → ℝ) :
    (pmfCubeAverage p f) ^ 2 ≤ pmfCubeAverage p (fun x => f x ^ 2) := by
  have hv := variance_nonneg f (pmfCubeMeasure p n)
  rw [variance_pmfCubeMeasure_eq_pmfCubeVariance,
    pmfCubeVariance_eq_secondMoment_sub] at hv
  linarith

theorem pmfCubeVariance_nonneg (p : PMF α) {n : ℕ}
    (f : UniformCube α n → ℝ) : 0 ≤ pmfCubeVariance p f := by
  rw [pmfCubeVariance_eq_secondMoment_sub]
  linarith [pmfCubeAverage_sq_le p f]

end ProductPMF

section EfronStein

variable {α : Type u} [Fintype α]

/-- One-coordinate variance for an arbitrary finite PMF. -/
noncomputable def pmfVariance (p : PMF α) (f : α → ℝ) : ℝ :=
  pmfAverage p fun a => (f a - pmfAverage p f) ^ 2

theorem pmfAverage_sq_le (p : PMF α) (f : α → ℝ) :
    (pmfAverage p f) ^ 2 ≤ pmfAverage p (fun a => f a ^ 2) := by
  let F : UniformCube α 1 → ℝ := fun x => f x.1
  have h := pmfCubeAverage_sq_le p F
  simp_rw [pmfCubeAverage_succ, pmfCubeAverage_zero] at h
  simpa [F] using h

theorem pmfVariance_eq_secondMoment_sub (p : PMF α) (f : α → ℝ) :
    pmfVariance p f = pmfAverage p (fun a => f a ^ 2) - (pmfAverage p f) ^ 2 := by
  let m := pmfAverage p f
  calc
    pmfVariance p f =
        pmfAverage p (fun a => f a ^ 2 - (2 * m) * f a + m ^ 2) := by
          unfold pmfVariance
          congr 1
          funext a
          dsimp [m]
          ring
    _ = pmfAverage p (fun a => f a ^ 2) -
          pmfAverage p (fun a => (2 * m) * f a) +
          pmfAverage p (fun _a : α => m ^ 2) := by
          rw [pmfAverage_add, pmfAverage_sub]
    _ = pmfAverage p (fun a => f a ^ 2) - (pmfAverage p f) ^ 2 := by
          rw [pmfAverage_const_mul, pmfAverage_const]
          dsimp [m]
          ring

theorem pmfVariance_eq_half_pairDifference (p : PMF α) (f : α → ℝ) :
    pmfVariance p f =
      (1 / 2 : ℝ) * pmfAverage p (fun a =>
        pmfAverage p (fun a' => (f a - f a') ^ 2)) := by
  let m := pmfAverage p f
  let q := pmfAverage p (fun a => f a ^ 2)
  have hinner (a : α) :
      pmfAverage p (fun a' => (f a - f a') ^ 2) =
        f a ^ 2 - (2 * m) * f a + q := by
    calc
      pmfAverage p (fun a' => (f a - f a') ^ 2) =
          pmfAverage p (fun a' => f a ^ 2 - (2 * f a) * f a' + f a' ^ 2) := by
            congr 1
            funext a'
            ring
      _ = pmfAverage p (fun _a' : α => f a ^ 2) -
            pmfAverage p (fun a' => (2 * f a) * f a') +
            pmfAverage p (fun a' => f a' ^ 2) := by
            rw [pmfAverage_add, pmfAverage_sub]
      _ = f a ^ 2 - (2 * m) * f a + q := by
            rw [pmfAverage_const, pmfAverage_const_mul]
            ring
  rw [pmfVariance_eq_secondMoment_sub]
  simp_rw [hinner]
  rw [pmfAverage_add, pmfAverage_sub, pmfAverage_const_mul,
    pmfAverage_const]
  dsimp [m, q]
  ring

/-- A PMF average commutes with the product-cube average. -/
theorem pmfAverage_pmfCubeAverage_comm (p : PMF α) {n : ℕ}
    (f : α → UniformCube α n → ℝ) :
    pmfAverage p (fun a => pmfCubeAverage p (fun x => f a x)) =
      pmfCubeAverage p (fun x => pmfAverage p (fun a => f a x)) := by
  classical
  unfold pmfAverage pmfCubeAverage
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Expected squared change after independently replacing coordinate `i`
with another sample from `p`. -/
noncomputable def pmfResamplingEnergy (p : PMF α) :
    {n : ℕ} → (UniformCube α n → ℝ) → Fin n → ℝ
  | 0, _, i => Fin.elim0 i
  | _n + 1, f, i => Fin.cases
      (pmfAverage p fun a =>
        pmfAverage p fun a' =>
          pmfCubeAverage p fun tail => (f (a, tail) - f (a', tail)) ^ 2)
      (fun j => pmfAverage p fun a =>
        pmfResamplingEnergy p (fun tail => f (a, tail)) j)
      i

/-- The recursive energy is exactly the product expectation of the explicit
coordinate-replacement squared difference. -/
theorem pmfResamplingEnergy_eq_replace_average (p : PMF α) :
    ∀ {n : ℕ} (f : UniformCube α n → ℝ) (i : Fin n),
      pmfResamplingEnergy p f i =
        pmfCubeAverage p (fun x => pmfAverage p (fun a' =>
          (f x - f (uniformCubeReplace x i a')) ^ 2)) := by
  intro n
  induction n with
  | zero =>
      intro f i
      exact Fin.elim0 i
  | succ n ih =>
      intro f i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [pmfResamplingEnergy, Fin.cases_zero]
        rw [pmfCubeAverage_succ]
        simp only [uniformCubeReplace]
        congr 1
        funext a
        exact pmfAverage_pmfCubeAverage_comm p
          (fun a' tail => (f (a, tail) - f (a', tail)) ^ 2)
      · simp only [pmfResamplingEnergy, Fin.cases_succ]
        rw [pmfCubeAverage_succ]
        simp only [uniformCubeReplace]
        congr 1
        funext a
        exact ih (fun tail => f (a, tail)) j

theorem pmfResamplingEnergy_le_of_replace_sq_le (p : PMF α)
    {n : ℕ} (f : UniformCube α n → ℝ) (i : Fin n) {D : ℝ}
    (hD : ∀ x a', (f x - f (uniformCubeReplace x i a')) ^ 2 ≤ D) :
    pmfResamplingEnergy p f i ≤ D := by
  rw [pmfResamplingEnergy_eq_replace_average]
  calc
    pmfCubeAverage p (fun x => pmfAverage p (fun a' =>
        (f x - f (uniformCubeReplace x i a')) ^ 2)) ≤
        pmfCubeAverage p (fun _x => D) := by
      apply pmfCubeAverage_mono
      intro x
      calc
        pmfAverage p (fun a' =>
            (f x - f (uniformCubeReplace x i a')) ^ 2) ≤
            pmfAverage p (fun _a' => D) :=
          pmfAverage_mono p fun a' => hD x a'
        _ = D := pmfAverage_const p D
    _ = D := pmfCubeAverage_const p D

theorem pmfCubeVariance_succ_decomposition (p : PMF α) {n : ℕ}
    (f : UniformCube α (n + 1) → ℝ) :
    pmfCubeVariance p f =
      pmfAverage p (fun a =>
        pmfCubeVariance p (fun tail : UniformCube α n => f (a, tail))) +
      pmfVariance p (fun a =>
        pmfCubeAverage p (fun tail : UniformCube α n => f (a, tail))) := by
  rw [pmfCubeVariance_eq_secondMoment_sub]
  rw [pmfVariance_eq_secondMoment_sub]
  simp_rw [pmfCubeVariance_eq_secondMoment_sub]
  rw [pmfCubeAverage_succ]
  rw [pmfCubeAverage_succ]
  simp_rw [pmfAverage_sub]
  ring

theorem pmfCubeVariance_average_le_headEnergy (p : PMF α) {n : ℕ}
    (f : UniformCube α (n + 1) → ℝ) :
    pmfVariance p (fun a =>
      pmfCubeAverage p (fun tail : UniformCube α n => f (a, tail))) ≤
      (1 / 2 : ℝ) * pmfResamplingEnergy p f 0 := by
  rw [pmfVariance_eq_half_pairDifference]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pmfAverage_mono
  intro a
  apply pmfAverage_mono
  intro a'
  rw [← pmfCubeAverage_sub]
  exact pmfCubeAverage_sq_le p
    (fun tail : UniformCube α n => f (a, tail) - f (a', tail))

/-- Efron--Stein for a finite IID product of an arbitrary PMF. -/
theorem pmfCubeVariance_le_half_sum_resampling (p : PMF α) :
    ∀ {n : ℕ} (f : UniformCube α n → ℝ),
      pmfCubeVariance p f ≤
        (1 / 2 : ℝ) * ∑ i, pmfResamplingEnergy p f i := by
  intro n
  induction n with
  | zero =>
      intro f
      have hf : f = fun _ => f PUnit.unit := by
        funext x
        cases x
        rfl
      rw [hf]
      simp [pmfCubeVariance, pmfCubeAverage_const]
  | succ n ih =>
      intro f
      rw [pmfCubeVariance_succ_decomposition]
      have htail :
          pmfAverage p (fun a =>
            pmfCubeVariance p (fun tail : UniformCube α n => f (a, tail))) ≤
          pmfAverage p (fun a =>
            (1 / 2 : ℝ) * ∑ j,
              pmfResamplingEnergy p (fun tail => f (a, tail)) j) :=
        pmfAverage_mono p fun a => ih (fun tail => f (a, tail))
      have hhead := pmfCubeVariance_average_le_headEnergy p f
      calc
        pmfAverage p (fun a =>
            pmfCubeVariance p (fun tail : UniformCube α n => f (a, tail))) +
            pmfVariance p (fun a =>
              pmfCubeAverage p (fun tail : UniformCube α n => f (a, tail))) ≤
          pmfAverage p (fun a =>
              (1 / 2 : ℝ) * ∑ j,
                pmfResamplingEnergy p (fun tail => f (a, tail)) j) +
            (1 / 2 : ℝ) * pmfResamplingEnergy p f 0 := add_le_add htail hhead
        _ = (1 / 2 : ℝ) * ∑ i, pmfResamplingEnergy p f i := by
          rw [pmfAverage_const_mul, pmfAverage_fintypeSum]
          rw [Fin.sum_univ_succ]
          simp only [pmfResamplingEnergy, Fin.cases_zero, Fin.cases_succ]
          ring

theorem pmfCubeVariance_le_half_card_mul_of_resampling_le
    (p : PMF α) {n : ℕ} (f : UniformCube α n → ℝ)
    {D : ℝ} (hD : ∀ i, pmfResamplingEnergy p f i ≤ D) :
    pmfCubeVariance p f ≤ (1 / 2 : ℝ) * (n : ℝ) * D := by
  refine (pmfCubeVariance_le_half_sum_resampling p f).trans ?_
  calc
    (1 / 2 : ℝ) * ∑ i, pmfResamplingEnergy p f i ≤
        (1 / 2 : ℝ) * ∑ _i : Fin n, D := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun i _ => hD i
    _ = (1 / 2 : ℝ) * (n : ℝ) * D := by simp; ring

theorem variance_pmfCubeMeasure_le_half_sum_resampling
    (p : PMF α) {n : ℕ} (f : UniformCube α n → ℝ) :
    variance f (pmfCubeMeasure p n) ≤
      (1 / 2 : ℝ) * ∑ i, pmfResamplingEnergy p f i := by
  rw [variance_pmfCubeMeasure_eq_pmfCubeVariance]
  exact pmfCubeVariance_le_half_sum_resampling p f

theorem variance_pmfCubeMeasure_le_half_card_mul_of_resampling_le
    (p : PMF α) {n : ℕ} (f : UniformCube α n → ℝ)
    {D : ℝ} (hD : ∀ i, pmfResamplingEnergy p f i ≤ D) :
    variance f (pmfCubeMeasure p n) ≤ (1 / 2 : ℝ) * (n : ℝ) * D := by
  rw [variance_pmfCubeMeasure_eq_pmfCubeVariance]
  exact pmfCubeVariance_le_half_card_mul_of_resampling_le p f hD

/-- The explicit replacement energy written with the actual product and
coordinate PMF measures. -/
theorem pmfResamplingEnergy_eq_replace_integral
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) {n : ℕ} (f : UniformCube α n → ℝ) (i : Fin n) :
    pmfResamplingEnergy p f i =
      ∫ x, (∫ a', (f x - f (uniformCubeReplace x i a')) ^ 2
        ∂p.toMeasure) ∂pmfCubeMeasure p n := by
  rw [pmfResamplingEnergy_eq_replace_average]
  rw [integral_pmfCubeMeasure_eq_pmfCubeAverage]
  congr 1
  funext x
  rw [PMF.integral_eq_sum]
  simp only [pmfAverage, smul_eq_mul]

/-- Efron--Stein followed by the Section 4 finite-degree maximal closure. -/
theorem pressure_maximal_concentration_pmf_resampling
    (p : PMF α) (n W : ℕ)
    (Y : Fin (2 * W).succ → UniformCube α n → ℝ)
    {D : ℝ} (hD : ∀ r i, pmfResamplingEnergy p (Y r) i ≤ D) :
    (∫ ω, maxCenteredAbs (pmfCubeMeasure p n) Y ω
        ∂pmfCubeMeasure p n) ≤
      Real.sqrt (((2 * W + 1 : ℕ) : ℝ) *
        ((1 / 2 : ℝ) * (n : ℝ) * D)) := by
  apply pressure_maximal_concentration_of_variance W
  · intro r
    exact memLp_pmfCube p (Y r) 2
  · intro r
    exact variance_pmfCubeMeasure_le_half_card_mul_of_resampling_le
      p (Y r) (hD r)

theorem pressure_maximal_concentration_pmf_replace_sq
    (p : PMF α) (n W : ℕ)
    (Y : Fin (2 * W).succ → UniformCube α n → ℝ)
    {D : ℝ}
    (hD : ∀ r i x a',
      (Y r x - Y r (uniformCubeReplace x i a')) ^ 2 ≤ D) :
    (∫ ω, maxCenteredAbs (pmfCubeMeasure p n) Y ω
        ∂pmfCubeMeasure p n) ≤
      Real.sqrt (((2 * W + 1 : ℕ) : ℝ) *
        ((1 / 2 : ℝ) * (n : ℝ) * D)) := by
  apply pressure_maximal_concentration_pmf_resampling p n W Y
  intro r i
  exact pmfResamplingEnergy_le_of_replace_sq_le p (Y r) i (hD r i)

end EfronStein

end CircularLawSection4
