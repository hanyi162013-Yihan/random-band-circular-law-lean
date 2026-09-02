import CircularLawSection4.ProductSmallBall
import CircularLawSection4.PressureProbability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance

/-!
# Continuous product Efron--Stein: the one-coordinate and recursive layers

This file develops the measure-theoretic layer for the recursive `iidMeasure`
used by `ProductSmallBall`.  The hypotheses are deliberately concrete:
functions are globally measurable and pointwise bounded.  On probability
spaces these hypotheses provide every `MemLp` and Fubini condition needed
below.
-/

open scoped ENNReal BigOperators
open MeasureTheory ProbabilityTheory

namespace CircularLawSection4

universe u v

section BoundedHelpers

variable {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S]

/-- A globally measurable, pointwise bounded function belongs to every
finite `Lᵖ` space over a finite measure. -/
theorem memLp_of_measurable_of_bound {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (p : ENNReal) : MemLp f p μ :=
  MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all μ hC)

/-- The integral of a bounded function under a probability measure has the
same norm bound. -/
theorem norm_integral_le_bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖∫ x, f x ∂μ‖ ≤ C := by
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all μ hC)

/-- Jensen's square inequality in the bounded measurable regime, obtained
from nonnegativity of variance. -/
theorem sq_integral_le_integral_sq {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have hmem : MemLp f 2 μ := memLp_of_measurable_of_bound hf C hC 2
  have hv := variance_nonneg f μ
  rw [variance_eq_sub hmem] at hv
  exact sub_nonneg.mp hv

end BoundedHelpers

section ProductVariance

variable {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S]
  {μ : Measure Ω} {ν : Measure S}
  [SFinite μ] [SFinite ν]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Law of total variance for a bounded measurable function on a product
probability space, written directly as iterated integrals. -/
theorem variance_prod_decomposition_bounded
    (F : Ω × S → ℝ) (hF : Measurable F) (C : ℝ)
    (hC : ∀ z, ‖F z‖ ≤ C) :
    variance F (μ.prod ν) =
      (∫ x, variance (fun y => F (x, y)) ν ∂μ) +
        variance (fun x => ∫ y, F (x, y) ∂ν) μ := by
  let g : Ω → ℝ := fun x => ∫ y, F (x, y) ∂ν
  have hFmem : MemLp F 2 (μ.prod ν) :=
    memLp_of_measurable_of_bound hF C hC 2
  have hFint : Integrable F (μ.prod ν) := hFmem.integrable one_le_two
  have hFsq : Integrable (fun z => F z ^ 2) (μ.prod ν) := hFmem.integrable_sq
  have hgsm : StronglyMeasurable g := by
    exact hF.stronglyMeasurable.integral_prod_right'
  have hgC : ∀ x, ‖g x‖ ≤ C := by
    intro x
    exact norm_integral_le_bound (μ := ν) (fun y => hC (x, y))
  have hgmem : MemLp g 2 μ :=
    MemLp.of_bound hgsm.aestronglyMeasurable C (ae_of_all μ hgC)
  have hsection (x : Ω) : MemLp (fun y => F (x, y)) 2 ν :=
    memLp_of_measurable_of_bound
      (hF.comp measurable_prodMk_left) C (fun y => hC (x, y)) 2
  have hmean :
      (∫ z, F z ∂μ.prod ν) = ∫ x, g x ∂μ :=
    integral_prod F hFint
  have hsquare :
      (∫ z, F z ^ 2 ∂μ.prod ν) =
        ∫ x, ∫ y, F (x, y) ^ 2 ∂ν ∂μ :=
    integral_prod (fun z => F z ^ 2) hFsq
  have hsquareOuter :
      Integrable (fun x => ∫ y, F (x, y) ^ 2 ∂ν) μ :=
    hFsq.integral_prod_left
  rw [variance_eq_sub hFmem, variance_eq_sub hgmem]
  simp_rw [variance_eq_sub (hsection _), Pi.pow_apply]
  change (∫ z, F z ^ 2 ∂μ.prod ν) - (∫ z, F z ∂μ.prod ν) ^ 2 = _
  rw [hmean, hsquare, integral_sub hsquareOuter hgmem.integrable_sq]
  ring

omit [SFinite μ] in
/-- For one bounded measurable random variable, variance is one half of the
expected squared difference of two independent copies. -/
theorem variance_eq_half_pairDifference_bounded
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) :
    variance f μ =
      (1 / 2 : ℝ) * ∫ x, ∫ x', (f x - f x') ^ 2 ∂μ ∂μ := by
  have hmem : MemLp f 2 μ := memLp_of_measurable_of_bound hf C hC 2
  have hfint : Integrable f μ := hmem.integrable one_le_two
  have hfsq : Integrable (fun x => f x ^ 2) μ := hmem.integrable_sq
  let m : ℝ := ∫ x, f x ∂μ
  let q : ℝ := ∫ x, f x ^ 2 ∂μ
  have hinner (x : Ω) :
      (∫ x', (f x - f x') ^ 2 ∂μ) = f x ^ 2 - (2 * m) * f x + q := by
    calc
      (∫ x', (f x - f x') ^ 2 ∂μ) =
          ∫ x', (f x ^ 2 - (2 * f x) * f x') + f x' ^ 2 ∂μ := by
            congr 1
            funext x'
            ring
      _ = (∫ x', f x ^ 2 - (2 * f x) * f x' ∂μ) +
          ∫ x', f x' ^ 2 ∂μ := by
            rw [integral_add]
            · exact (integrable_const _).sub (hfint.const_mul _)
            · exact hfsq
      _ = (∫ _x' : Ω, f x ^ 2 ∂μ) -
          ∫ x', (2 * f x) * f x' ∂μ + q := by
            rw [integral_sub (integrable_const _) (hfint.const_mul _)]
      _ = f x ^ 2 - (2 * m) * f x + q := by
            simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
              integral_const_mul]
            dsimp [m]
            ring
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply]
  simp_rw [hinner]
  have hlin : Integrable (fun x => (2 * m) * f x) μ := hfint.const_mul _
  have hfirst :
      (∫ x, f x ^ 2 - (2 * m) * f x ∂μ) =
        q - (2 * m) * m := by
    calc
      (∫ x, f x ^ 2 - (2 * m) * f x ∂μ) =
          (∫ x, f x ^ 2 ∂μ) - ∫ x, (2 * m) * f x ∂μ :=
        integral_sub hfsq hlin
      _ = q - (2 * m) * m := by
        rw [integral_const_mul]
  have houter :
      (∫ x, (f x ^ 2 - (2 * m) * f x) + q ∂μ) =
        q - (2 * m) * m + q := by
    calc
      (∫ x, (f x ^ 2 - (2 * m) * f x) + q ∂μ) =
          (∫ x, f x ^ 2 - (2 * m) * f x ∂μ) +
            ∫ _x : Ω, q ∂μ :=
        integral_add (hfsq.sub hlin) (integrable_const _)
      _ = q - (2 * m) * m + q := by
        rw [hfirst]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [houter]
  dsimp [m, q]
  ring

end ProductVariance

section IIDRecursiveStep

variable {K : Type u} [MeasurableSpace K]
  (ν : Measure K) [SFinite ν] [IsProbabilityMeasure ν]

/-- The vector with its unique coordinate equal to `a`. -/
def oneCoordVector (a : K) : Fin 1 → K := fun _ => a

theorem measurable_oneCoordVector : Measurable (oneCoordVector : K → Fin 1 → K) := by
  apply measurable_pi_lambda
  intro _i
  exact measurable_id

omit [MeasurableSpace K] in
@[simp] theorem joinLast_zero_eq_oneCoordVector
    (y : Fin 0 → K) (a : K) :
    joinLast (y, a) = oneCoordVector a := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  have hlast : (0 : Fin 1) = Fin.last 0 := rfl
  rw [hi, hlast]
  rw [joinLast_last]
  rfl

omit [IsProbabilityMeasure ν] in
/-- The recursive one-coordinate law is the pushforward of `ν` by the
canonical identification `K → (Fin 1 → K)`. -/
theorem iidMeasure_one_eq_map_oneCoordVector :
    iidMeasure ν 1 = Measure.map oneCoordVector ν := by
  simp only [iidMeasure]
  rw [Measure.dirac_prod]
  rw [Measure.map_map measurable_joinLast measurable_prodMk_left]
  congr 1
  funext a
  exact joinLast_zero_eq_oneCoordVector _ a

/-- Fubini recursion for the exact successor `iidMeasure`.  Unlike the later
bounded theorems, this only assumes the integrability actually needed. -/
theorem integral_iidMeasure_succ {n : ℕ}
    {f : (Fin (n + 1) → K) → ℝ}
    (hf : Integrable f (iidMeasure ν (n + 1))) :
    (∫ x, f x ∂iidMeasure ν (n + 1)) =
      ∫ y, ∫ a, f (joinLast (y, a)) ∂ν ∂iidMeasure ν n := by
  let _ := iidMeasure_isProbability ν n
  rw [iidMeasure] at hf ⊢
  have hcomp :
      Integrable (f ∘ joinLast) ((iidMeasure ν n).prod ν) :=
    (integrable_map_measure hf.aestronglyMeasurable
      measurable_joinLast.aemeasurable).mp hf
  rw [integral_map measurable_joinLast.aemeasurable hf.aestronglyMeasurable]
  simpa only [Function.comp_apply] using integral_prod (f ∘ joinLast) hcomp

omit [IsProbabilityMeasure ν] in
/-- Pulling a variance through the `joinLast` map identifies the successor
IID law with the corresponding product variance. -/
theorem variance_iidMeasure_succ_eq_product {n : ℕ}
    (f : (Fin (n + 1) → K) → ℝ) (hf : Measurable f) :
    variance f (iidMeasure ν (n + 1)) =
      variance (fun z : (Fin n → K) × K => f (joinLast z))
        ((iidMeasure ν n).prod ν) := by
  rw [iidMeasure]
  simpa only [Function.comp_def] using
    (variance_map hf.aemeasurable measurable_joinLast.aemeasurable)

omit [IsProbabilityMeasure ν] in
/-- Variance under `iidMeasure ν 1` is exactly the variance of the
corresponding one-coordinate function under `ν`. -/
theorem variance_iidMeasure_one_eq
    (f : (Fin 1 → K) → ℝ) (hf : Measurable f) :
    variance f (iidMeasure ν 1) =
      variance (fun a => f (oneCoordVector a)) ν := by
  rw [iidMeasure_one_eq_map_oneCoordVector ν]
  simpa only [Function.comp_def] using
    (variance_map hf.aemeasurable measurable_oneCoordVector.aemeasurable)

/-- The complete `n = 1` Efron--Stein identity on the recursive IID law. -/
theorem variance_iidMeasure_one_eq_half_resampling_bounded
    (f : (Fin 1 → K) → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) :
    variance f (iidMeasure ν 1) =
      (1 / 2 : ℝ) * ∫ a, ∫ a',
        (f (oneCoordVector a) - f (oneCoordVector a')) ^ 2 ∂ν ∂ν := by
  rw [variance_iidMeasure_one_eq ν f hf]
  exact variance_eq_half_pairDifference_bounded
    (μ := ν) (fun a => f (oneCoordVector a))
    (hf.comp measurable_oneCoordVector) C (fun a => hC (oneCoordVector a))

/-- One recursive law-of-total-variance step for the exact `iidMeasure` used
in the Section 4 small-ball development. -/
theorem variance_iidMeasure_succ_decomposition_bounded {n : ℕ}
    (f : (Fin (n + 1) → K) → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) :
    variance f (iidMeasure ν (n + 1)) =
      (∫ y, variance (fun a => f (joinLast (y, a))) ν
        ∂iidMeasure ν n) +
      variance (fun y => ∫ a, f (joinLast (y, a)) ∂ν)
        (iidMeasure ν n) := by
  let _ := iidMeasure_isProbability ν n
  rw [variance_iidMeasure_succ_eq_product ν f hf]
  exact variance_prod_decomposition_bounded
    (μ := iidMeasure ν n) (ν := ν)
    (fun z => f (joinLast z)) (hf.comp measurable_joinLast) C
    (fun z => hC (joinLast z))

/-- The preceding recursive step with the fresh-coordinate conditional
variance replaced by its explicit independent-resampling energy. -/
theorem variance_iidMeasure_succ_decomposition_resampling_bounded {n : ℕ}
    (f : (Fin (n + 1) → K) → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) :
    variance f (iidMeasure ν (n + 1)) =
      (1 / 2 : ℝ) *
        (∫ y, ∫ a, ∫ a',
          (f (joinLast (y, a)) - f (joinLast (y, a'))) ^ 2
          ∂ν ∂ν ∂iidMeasure ν n) +
      variance (fun y => ∫ a, f (joinLast (y, a)) ∂ν)
        (iidMeasure ν n) := by
  rw [variance_iidMeasure_succ_decomposition_bounded ν f hf C hC]
  congr 1
  have hpoint (y : Fin n → K) :
      variance (fun a => f (joinLast (y, a))) ν =
        (1 / 2 : ℝ) * ∫ a, ∫ a',
          (f (joinLast (y, a)) - f (joinLast (y, a'))) ^ 2 ∂ν ∂ν := by
    exact variance_eq_half_pairDifference_bounded
      (μ := ν) (fun a => f (joinLast (y, a)))
      (hf.comp (measurable_joinLast.comp measurable_prodMk_left)) C
      (fun a => hC (joinLast (y, a)))
  simp_rw [hpoint, ← integral_const_mul]

/-- Recursive resampling budget obtained by repeatedly averaging out the
fresh last coordinate.  This is a Doob-style budget: at level `n + 1` it is
the genuine resampling energy of the fresh coordinate plus the budget of the
conditional mean on the first `n` coordinates. -/
noncomputable def iidRecursiveResamplingBudget :
    (n : ℕ) → ((Fin n → K) → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, f =>
      (∫ y, ∫ a, ∫ a',
        (f (joinLast (y, a)) - f (joinLast (y, a'))) ^ 2
        ∂ν ∂ν ∂iidMeasure ν n) +
      iidRecursiveResamplingBudget n
        (fun y => ∫ a, f (joinLast (y, a)) ∂ν)

/-- Full finite-dimensional variance closure for the recursive continuous
IID law.  The right side is the recursive (Doob) resampling budget above.
No conditional-expectation API is used: the proof is direct induction from
Fubini and the one-coordinate independent-copy identity. -/
theorem variance_iidMeasure_le_half_recursiveResamplingBudget_bounded :
    ∀ (n : ℕ) (f : (Fin n → K) → ℝ), Measurable f →
      ∀ (C : ℝ), (∀ x, ‖f x‖ ≤ C) →
      variance f (iidMeasure ν n) ≤
        (1 / 2 : ℝ) * iidRecursiveResamplingBudget ν n f := by
  intro n
  induction n with
  | zero =>
      intro f hf C hC
      let _ := iidMeasure_isProbability ν 0
      have hfconst : f = fun _x => f (fun i => Fin.elim0 i) := by
        funext x
        congr 1
        funext i
        exact Fin.elim0 i
      rw [hfconst]
      simp [iidRecursiveResamplingBudget, variance_eq_integral]
  | succ n ih =>
      intro f hf C hC
      let _ := iidMeasure_isProbability ν n
      let g : (Fin n → K) → ℝ :=
        fun y => ∫ a, f (joinLast (y, a)) ∂ν
      have hgsm : StronglyMeasurable g := by
        exact (hf.comp measurable_joinLast).stronglyMeasurable.integral_prod_right'
      have hgC : ∀ y, ‖g y‖ ≤ C := by
        intro y
        exact norm_integral_le_bound (μ := ν)
          (fun a => hC (joinLast (y, a)))
      have hrec :=
        variance_iidMeasure_succ_decomposition_resampling_bounded
          ν f hf C hC
      have hih := ih g hgsm.measurable C hgC
      rw [hrec]
      change
        (1 / 2 : ℝ) *
            (∫ y, ∫ a, ∫ a',
              (f (joinLast (y, a)) - f (joinLast (y, a'))) ^ 2
              ∂ν ∂ν ∂iidMeasure ν n) + variance g (iidMeasure ν n) ≤
          (1 / 2 : ℝ) *
            ((∫ y, ∫ a, ∫ a',
              (f (joinLast (y, a)) - f (joinLast (y, a'))) ^ 2
              ∂ν ∂ν ∂iidMeasure ν n) +
            iidRecursiveResamplingBudget ν n g)
      linarith

/-- The recursive continuous-product variance bound plugged into the
finite-degree pressure maximal-deviation closure. -/
theorem pressure_maximal_concentration_iid_recursiveResamplingBudget
    (n W : ℕ)
    (Y : Fin (2 * W).succ → (Fin n → K) → ℝ)
    (hY : ∀ r, Measurable (Y r)) (C : ℝ)
    (hC : ∀ r x, ‖Y r x‖ ≤ C) {B : ℝ}
    (hB : ∀ r, iidRecursiveResamplingBudget ν n (Y r) ≤ B) :
    (∫ ω, maxCenteredAbs (iidMeasure ν n) Y ω ∂iidMeasure ν n) ≤
      Real.sqrt (((2 * W + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) * B)) := by
  let _ := iidMeasure_isProbability ν n
  apply pressure_maximal_concentration_of_variance W
  · intro r
    exact memLp_of_measurable_of_bound (hY r) C (hC r) 2
  · intro r
    exact (variance_iidMeasure_le_half_recursiveResamplingBudget_bounded
      ν n (Y r) (hY r) C (hC r)).trans
        (mul_le_mul_of_nonneg_left (hB r) (by positivity))

end IIDRecursiveStep

end CircularLawSection4
