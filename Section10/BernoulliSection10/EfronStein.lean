import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Probability.Moments.Variance

set_option maxHeartbeats 1000000

/-!
# Efron--Stein inequalities on finite product spaces

This file develops the probability-theoretic part of Lemma 10.5 independently
of the matrix-valued affine logarithm estimates.  The basic sample space is a
finite canonical product and resampling means replacing one coordinate by an
independent draw from its marginal law.
-/

open scoped ENNReal NNReal
open Filter Topology
open MeasureTheory ProbabilityTheory

namespace BernoulliSection10

noncomputable section

section Resampling

variable {ι : Type*} {α : ι → Type*}

/-- Replace coordinate `i` of a dependent function by `y`. -/
def coordinateResample [DecidableEq ι] (i : ι) (x : ∀ j, α j) (y : α i) : ∀ j, α j :=
  Function.update x i y

@[simp] theorem coordinateResample_same [DecidableEq ι]
    (i : ι) (x : ∀ j, α j) (y : α i) :
    coordinateResample i x y i = y := by
  simp [coordinateResample]

@[simp] theorem coordinateResample_ne [DecidableEq ι]
    (i j : ι) (hji : j ≠ i) (x : ∀ k, α k) (y : α i) :
    coordinateResample i x y j = x j := by
  simp [coordinateResample, hji]

variable [∀ i, MeasurableSpace (α i)]

theorem measurable_coordinateResample [DecidableEq ι] (i : ι) :
    Measurable (fun p : (∀ j, α j) × α i => coordinateResample i p.1 p.2) := by
  simpa [coordinateResample] using (measurable_update' (X := α) (a := i))

/-- Squared change caused by replacing coordinate `i`. -/
def coordinateDifference [DecidableEq ι] (f : (∀ j, α j) → ℝ)
    (i : ι) (x : ∀ j, α j) (y : α i) : ℝ :=
  (f x - f (coordinateResample i x y)) ^ 2

theorem measurable_coordinateDifference [DecidableEq ι]
    {f : (∀ j, α j) → ℝ} (hf : Measurable f) (i : ι) :
    Measurable (fun p : (∀ j, α j) × α i =>
      coordinateDifference f i p.1 p.2) := by
  exact (hf.comp measurable_fst).sub
    (hf.comp (measurable_coordinateResample i)) |>.pow_const _

end Resampling

section Clipping

/-- Symmetric clipping used to reduce an unbounded observable to the bounded
case before passing to `L²`. -/
def clip (T x : ℝ) : ℝ := max (-T) (min T x)

theorem clip_measurable (T : ℝ) : Measurable (clip T) := by
  change Measurable (fun x : ℝ => max (-T) (min T x))
  exact measurable_const.max (measurable_const.min measurable_id)

theorem abs_clip_le (T x : ℝ) (hT : 0 ≤ T) : |clip T x| ≤ T := by
  simp only [clip]
  rw [abs_le]
  constructor <;> simp_all [max_le_iff]

theorem clip_eq_self {T x : ℝ} (hT : |x| ≤ T) : clip T x = x := by
  rw [abs_le] at hT
  simp [clip, hT.1, hT.2]

theorem abs_clip_le_abs (T x : ℝ) (hT : 0 ≤ T) : |clip T x| ≤ |x| := by
  have hLip : LipschitzWith 1 (clip T) := by
    change LipschitzWith 1 (fun y : ℝ => max (-T) (min T y))
    exact (LipschitzWith.id.const_min T).const_max (-T)
  have h := hLip.dist_le_mul x 0
  simpa [Real.dist_eq, clip, hT] using h

theorem clip_lipschitz (T : ℝ) : LipschitzWith 1 (clip T) := by
  change LipschitzWith 1 (fun x : ℝ => max (-T) (min T x))
  exact (LipschitzWith.id.const_min T).const_max (-T)

theorem abs_clip_sub_clip_le (T x y : ℝ) :
    |clip T x - clip T y| ≤ |x - y| := by
  simpa [Real.dist_eq] using (clip_lipschitz T).dist_le_mul x y

theorem clip_tendsto_atTop (x : ℝ) : Tendsto (fun T : ℝ => clip T x) atTop (𝓝 x) := by
  refine (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [eventually_ge_atTop |x|] with T hT
  exact clip_eq_self hT

end Clipping

section PairVariance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Variance is half the mean squared difference of two independent copies.
This bounded version is the algebraic identity used in the finite-product
induction below. -/
theorem variance_eq_half_integral_prod_sub_sq
    [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Var[f; μ] = (1 / 2 : ℝ) * ∫ x, ∫ y, (f x - f y) ^ 2 ∂μ ∂μ := by
  have hf_int : Integrable f μ :=
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hf_sq : Integrable (fun x => f x ^ 2) μ := by
    exact Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (C ^ 2)
      (ae_of_all _ fun x => by
        simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow]
        nlinarith [abs_nonneg (f x), hC x])
  have hdiff : Integrable (fun p : Ω × Ω => (f p.1 - f p.2) ^ 2) (μ.prod μ) := by
    refine Integrable.of_bound
      (((hf.comp measurable_fst).sub (hf.comp measurable_snd)).pow_const 2
        |>.aestronglyMeasurable) ((2 * C) ^ 2) ?_
    filter_upwards with p
    simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow]
    have hsub : |f p.1 - f p.2| ≤ |f p.1| + |f p.2| := abs_sub _ _
    nlinarith [abs_nonneg (f p.1), abs_nonneg (f p.2), abs_nonneg (f p.1 - f p.2),
      hC p.1, hC p.2]
  have hfst_sq : Integrable (fun p : Ω × Ω => f p.1 ^ 2) (μ.prod μ) :=
    hf_sq.comp_fst μ
  have hsnd_sq : Integrable (fun p : Ω × Ω => f p.2 ^ 2) (μ.prod μ) :=
    hf_sq.comp_snd μ
  have hcross : Integrable (fun p : Ω × Ω => f p.1 * f p.2) (μ.prod μ) :=
    hf_int.mul_prod hf_int
  have hprod :
      (∫ p : Ω × Ω, (f p.1 - f p.2) ^ 2 ∂μ.prod μ) =
        2 * (∫ x, f x ^ 2 ∂μ) - 2 * (∫ x, f x ∂μ) ^ 2 := by
    have hfst_eq :
        (∫ p : Ω × Ω, f p.1 ^ 2 ∂μ.prod μ) = ∫ x, f x ^ 2 ∂μ := by
      simpa using
        (integral_fun_fst (μ := μ) (ν := μ) (fun x => f x ^ 2))
    have hsnd_eq :
        (∫ p : Ω × Ω, f p.2 ^ 2 ∂μ.prod μ) = ∫ x, f x ^ 2 ∂μ := by
      simpa using
        (integral_fun_snd (μ := μ) (ν := μ) (fun x => f x ^ 2))
    have hcross_eq :
        (∫ p : Ω × Ω, f p.1 * f p.2 ∂μ.prod μ) =
          (∫ x, f x ∂μ) * ∫ x, f x ∂μ := by
      exact integral_prod_mul f f
    calc
      (∫ p : Ω × Ω, (f p.1 - f p.2) ^ 2 ∂μ.prod μ) =
          (∫ p : Ω × Ω, f p.1 ^ 2 ∂μ.prod μ) -
            2 * (∫ p : Ω × Ω, f p.1 * f p.2 ∂μ.prod μ) +
              (∫ p : Ω × Ω, f p.2 ^ 2 ∂μ.prod μ) := by
        let a : Ω × Ω → ℝ := fun p => f p.1 ^ 2
        let b : Ω × Ω → ℝ := fun p => 2 * (f p.1 * f p.2)
        let c : Ω × Ω → ℝ := fun p => f p.2 ^ 2
        have ha : Integrable a (μ.prod μ) := hfst_sq
        have hb : Integrable b (μ.prod μ) := hcross.const_mul 2
        have hc : Integrable c (μ.prod μ) := hsnd_sq
        calc
          _ = ∫ p, (a - b + c) p ∂μ.prod μ := by
            apply integral_congr_ae
            exact ae_of_all _ fun p => by simp [a, b, c]; ring
          _ = (∫ p, a p ∂μ.prod μ) - (∫ p, b p ∂μ.prod μ) +
                ∫ p, c p ∂μ.prod μ := by
            calc
              _ = (∫ p, (a - b) p ∂μ.prod μ) + ∫ p, c p ∂μ.prod μ := by
                simpa only [Pi.add_apply] using integral_add (ha.sub hb) hc
              _ = _ := by
                have habint :
                    (∫ p, (a - b) p ∂μ.prod μ) =
                      (∫ p, a p ∂μ.prod μ) - ∫ p, b p ∂μ.prod μ := by
                  simpa only [Pi.sub_apply] using integral_sub ha hb
                rw [habint]
          _ = _ := by
            dsimp [a, b, c]
            rw [integral_const_mul]
      _ = 2 * (∫ x, f x ^ 2 ∂μ) - 2 * (∫ x, f x ∂μ) ^ 2 := by
        rw [hfst_eq, hsnd_eq, hcross_eq]
        ring
  rw [variance_eq_sub (memLp_two_iff_integrable_sq hf.aestronglyMeasurable |>.2 hf_sq)]
  change (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 = _
  rw [← integral_prod _ hdiff, hprod]
  ring

end PairVariance

section ProductVariance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Jensen's inequality for the square, in the exact form needed below. -/
theorem sq_integral_le_integral_sq [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have hvar := variance_nonneg f μ
  rw [variance_eq_sub hf] at hvar
  change 0 ≤ (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 at hvar
  linarith

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {ν : Measure α} {κ : Measure β}

theorem measurable_prod_mk_left (x : α) : Measurable (fun y : β => (x, y)) := by
  apply Measurable.prod
  · exact measurable_const
  · exact measurable_id

/-- Law of total variance for a bounded function on a product probability
space, written using the literal fiber integrals.  The bounded formulation is
deliberate: it is the induction engine for Efron--Stein, and the final theorem
removes boundedness by clipping. -/
theorem variance_prod_eq_integral_variance_add
    [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    {f : α × β → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ p, |f p| ≤ C) :
    Var[f; ν.prod κ] =
      (∫ x, Var[(fun y => f (x, y)); κ] ∂ν) +
        Var[(fun x => ∫ y, f (x, y) ∂κ); ν] := by
  let g : α → ℝ := fun x => ∫ y, f (x, y) ∂κ
  have hf_int : Integrable f (ν.prod κ) :=
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hf_sq : Integrable (fun p => f p ^ 2) (ν.prod κ) := by
    apply Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (C ^ 2)
    filter_upwards with p
    simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow]
    nlinarith [abs_nonneg (f p), hC p]
  have hsec_int (x : α) : Integrable (fun y => f (x, y)) κ := by
    exact Integrable.of_bound
      (hf.comp (measurable_prod_mk_left x)).aestronglyMeasurable C
      (ae_of_all _ fun y => hC (x, y))
  have hsec_sq (x : α) : Integrable (fun y => f (x, y) ^ 2) κ := by
    refine Integrable.of_bound
      ((hf.comp (measurable_prod_mk_left x)).pow_const 2).aestronglyMeasurable
      (C ^ 2) ?_
    filter_upwards with y
    simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow]
    nlinarith [abs_nonneg (f (x, y)), hC (x, y)]
  have hg_strong : StronglyMeasurable g := by
    exact hf.stronglyMeasurable.integral_prod_right'
  have hg_bound (x : α) : |g x| ≤ C := by
    change |∫ y, f (x, y) ∂κ| ≤ C
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ y, f (x, y) ∂κ‖ ≤ ∫ y, ‖f (x, y)‖ ∂κ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ _y, C ∂κ := by
        apply integral_mono (hsec_int x).norm (integrable_const C)
        exact fun y => hC (x, y)
      _ = C := by simp
  have hg_sq : Integrable (fun x => g x ^ 2) ν := by
    apply Integrable.of_bound (hg_strong.pow 2).aestronglyMeasurable (C ^ 2)
    filter_upwards with x
    simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow]
    nlinarith [abs_nonneg (g x), hg_bound x]
  have hF_mem : MemLp f 2 (ν.prod κ) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hf_sq
  have hg_mem : MemLp g 2 ν :=
    (memLp_two_iff_integrable_sq hg_strong.aestronglyMeasurable).2 hg_sq
  have hsec_mem (x : α) : MemLp (fun y => f (x, y)) 2 κ :=
    (memLp_two_iff_integrable_sq
      (hf.comp (measurable_prod_mk_left x)).aestronglyMeasurable).2 (hsec_sq x)
  rw [variance_eq_sub hF_mem]
  change (∫ p, f p ^ 2 ∂ν.prod κ) - (∫ p, f p ∂ν.prod κ) ^ 2 = _
  change _ = (∫ x, Var[(fun y => f (x, y)); κ] ∂ν) + Var[g; ν]
  rw [integral_congr_ae (ae_of_all _ fun x => variance_eq_sub (hsec_mem x))]
  simp only [Pi.pow_apply]
  rw [integral_sub hf_sq.integral_prod_left hg_sq, variance_eq_sub hg_mem]
  simp only [Pi.pow_apply]
  rw [integral_prod _ hf_sq, integral_prod _ hf_int]
  dsimp [g]
  ring

/-- Averaging over the second coordinate cannot increase the squared
independent-copy difference.  This is Jensen's step in the product
Efron--Stein induction. -/
theorem variance_integral_fiber_le_half_resample
    [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    {f : α × β → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ p, |f p| ≤ C) :
    Var[(fun x => ∫ y, f (x, y) ∂κ); ν] ≤
      (1 / 2 : ℝ) *
        ∫ p : α × α, ∫ y, (f (p.1, y) - f (p.2, y)) ^ 2 ∂κ ∂ν.prod ν := by
  let g : α → ℝ := fun x => ∫ y, f (x, y) ∂κ
  have hsec_int (x : α) : Integrable (fun y => f (x, y)) κ := by
    exact Integrable.of_bound
      (hf.comp (measurable_prod_mk_left x)).aestronglyMeasurable C
      (ae_of_all _ fun y => hC (x, y))
  have hg_meas : Measurable g :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hg_bound (x : α) : |g x| ≤ C := by
    change |∫ y, f (x, y) ∂κ| ≤ C
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ y, f (x, y) ∂κ‖ ≤ ∫ y, ‖f (x, y)‖ ∂κ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ _y, C ∂κ := by
        apply integral_mono (hsec_int x).norm (integrable_const C)
        exact fun y => hC (x, y)
      _ = C := by simp
  let d : (α × α) × β → ℝ := fun q =>
    (f (q.1.1, q.2) - f (q.1.2, q.2)) ^ 2
  have hd_meas : Measurable d := by
    dsimp [d]
    fun_prop
  have hd_int : Integrable d ((ν.prod ν).prod κ) := by
    apply Integrable.of_bound hd_meas.aestronglyMeasurable ((2 * C) ^ 2)
    filter_upwards with q
    dsimp [d]
    simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow]
    have hsub : |f (q.1.1, q.2) - f (q.1.2, q.2)| ≤
        |f (q.1.1, q.2)| + |f (q.1.2, q.2)| := abs_sub _ _
    nlinarith [abs_nonneg (f (q.1.1, q.2)), abs_nonneg (f (q.1.2, q.2)),
      abs_nonneg (f (q.1.1, q.2) - f (q.1.2, q.2)),
      hC (q.1.1, q.2), hC (q.1.2, q.2)]
  have hleft_int : Integrable (fun p : α × α => (g p.1 - g p.2) ^ 2) (ν.prod ν) := by
    refine Integrable.of_bound
      (((hg_meas.comp measurable_fst).sub (hg_meas.comp measurable_snd)).pow_const 2
        |>.aestronglyMeasurable) ((2 * C) ^ 2) ?_
    filter_upwards with p
    simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow]
    have hsub : |g p.1 - g p.2| ≤ |g p.1| + |g p.2| := abs_sub _ _
    nlinarith [abs_nonneg (g p.1), abs_nonneg (g p.2), abs_nonneg (g p.1 - g p.2),
      hg_bound p.1, hg_bound p.2]
  have hpoint (p : α × α) :
      (g p.1 - g p.2) ^ 2 ≤ ∫ y, d (p, y) ∂κ := by
    have hd_sec_sq : Integrable (fun y => d (p, y)) κ := by
      refine Integrable.of_bound
        (hd_meas.comp (measurable_prod_mk_left p)).aestronglyMeasurable
        ((2 * C) ^ 2) ?_
      filter_upwards with y
      dsimp [d]
      simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow]
      have hsub : |f (p.1, y) - f (p.2, y)| ≤ |f (p.1, y)| + |f (p.2, y)| :=
        abs_sub _ _
      nlinarith [abs_nonneg (f (p.1, y)), abs_nonneg (f (p.2, y)),
        abs_nonneg (f (p.1, y) - f (p.2, y)), hC (p.1, y), hC (p.2, y)]
    have hd_sec_mem : MemLp (fun y => f (p.1, y) - f (p.2, y)) 2 κ := by
      apply (memLp_two_iff_integrable_sq
        ((hf.comp (measurable_prod_mk_left p.1)).sub
          (hf.comp (measurable_prod_mk_left p.2))).aestronglyMeasurable).2
      simpa [d] using hd_sec_sq
    have havg : g p.1 - g p.2 = ∫ y, f (p.1, y) - f (p.2, y) ∂κ := by
      dsimp [g]
      rw [integral_sub (hsec_int p.1) (hsec_int p.2)]
    rw [havg]
    simpa [d] using sq_integral_le_integral_sq hd_sec_mem
  calc
    Var[(fun x => ∫ y, f (x, y) ∂κ); ν] =
        (1 / 2 : ℝ) * ∫ p : α × α, (g p.1 - g p.2) ^ 2 ∂ν.prod ν := by
      change Var[g; ν] = _
      rw [variance_eq_half_integral_prod_sub_sq hg_meas C hg_bound,
        ← integral_prod _ hleft_int]
    _ ≤ (1 / 2 : ℝ) * ∫ p : α × α, ∫ y, d (p, y) ∂κ ∂ν.prod ν := by
      exact mul_le_mul_of_nonneg_left
        (integral_mono hleft_int hd_int.integral_prod_left hpoint) (by norm_num)
    _ = (1 / 2 : ℝ) *
        ∫ p : α × α, ∫ y, (f (p.1, y) - f (p.2, y)) ^ 2 ∂κ ∂ν.prod ν := by
      rfl

/-- For bounded measurable functions, the fiber variance is integrable in the
outer coordinate. -/
theorem integrable_variance_fiber_bounded
    [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    {f : α × β → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ p, |f p| ≤ C) :
    Integrable (fun x => Var[(fun y => f (x, y)); κ]) ν := by
  let g : α → ℝ := fun x => ∫ y, f (x, y) ∂κ
  have hf_sq : Integrable (fun p => f p ^ 2) (ν.prod κ) := by
    apply Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (C ^ 2)
    filter_upwards with p
    simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow]
    nlinarith [abs_nonneg (f p), hC p]
  have hsec_sq (x : α) : Integrable (fun y => f (x, y) ^ 2) κ := by
    refine Integrable.of_bound
      ((hf.comp (measurable_prod_mk_left x)).pow_const 2).aestronglyMeasurable
      (C ^ 2) ?_
    filter_upwards with y
    simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow]
    nlinarith [abs_nonneg (f (x, y)), hC (x, y)]
  have hg_strong : StronglyMeasurable g :=
    hf.stronglyMeasurable.integral_prod_right'
  have hsec_int (x : α) : Integrable (fun y => f (x, y)) κ := by
    exact Integrable.of_bound
      (hf.comp (measurable_prod_mk_left x)).aestronglyMeasurable C
      (ae_of_all _ fun y => hC (x, y))
  have hg_bound (x : α) : |g x| ≤ C := by
    change |∫ y, f (x, y) ∂κ| ≤ C
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ y, f (x, y) ∂κ‖ ≤ ∫ y, ‖f (x, y)‖ ∂κ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ _y, C ∂κ := by
        apply integral_mono (hsec_int x).norm (integrable_const C)
        exact fun y => hC (x, y)
      _ = C := by simp
  have hg_sq : Integrable (fun x => g x ^ 2) ν := by
    apply Integrable.of_bound (hg_strong.pow 2).aestronglyMeasurable (C ^ 2)
    filter_upwards with x
    simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow]
    nlinarith [abs_nonneg (g x), hg_bound x]
  have hsec_mem (x : α) : MemLp (fun y => f (x, y)) 2 κ :=
    (memLp_two_iff_integrable_sq
      (hf.comp (measurable_prod_mk_left x)).aestronglyMeasurable).2 (hsec_sq x)
  apply (hf_sq.integral_prod_left.sub hg_sq).congr
  exact ae_of_all _ fun x => (variance_eq_sub (hsec_mem x)).symm

end ProductVariance

section FiniteProductEfronStein

variable {α : Type*} [MeasurableSpace α] [Nonempty α]
  {μ : Measure α} [IsProbabilityMeasure μ]

/-- Conditional independent-copy energy of coordinate `i`, with every other
coordinate held fixed at `x`.  Its value is independent of `x i`; using a full
tuple here makes the definition uniform even when the index type is empty. -/
def conditionalCoordinateEnergy {n : ℕ}
    (f : (Fin n → α) → ℝ) (i : Fin n) (x : Fin n → α) : ℝ :=
  ∫ p : α × α,
    (f (Function.update x i p.1) - f (Function.update x i p.2)) ^ 2 ∂μ.prod μ

/-- Finite-product Efron--Stein with a uniform conditional energy bound.

This is the form used by Lemma 10.5: after all physical rows but one are fixed,
Lemma 10.2 supplies `K i` for the double integral over the original and
resampled row. -/
theorem efronStein_fin_product_bounded
    (n : ℕ) {f : (Fin n → α) → ℝ} (hf : Measurable f)
    (C : ℝ) (hC : ∀ x, |f x| ≤ C)
    (K : Fin n → ℝ) (hK : ∀ i, 0 ≤ K i)
    (hresample : ∀ i x, conditionalCoordinateEnergy (μ := μ) f i x ≤ K i) :
    Var[f; Measure.pi (fun _ : Fin n => μ)] ≤
      (1 / 2 : ℝ) * ∑ i, K i := by
  induction n with
  | zero =>
      rw [variance_eq_half_integral_prod_sub_sq hf C hC]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
      let x0 : Fin 0 → α := fun i => Fin.elim0 i
      have hfun : ∀ x : Fin 0 → α, f x = f x0 := fun x =>
        congrArg f (Subsingleton.elim x x0)
      simp_rw [hfun]
      simp
  | succ n ih =>
      let πn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => μ)
      let F : α × (Fin n → α) → ℝ := fun p => f (Fin.cons p.1 p.2)
      have hF : Measurable F := by
        dsimp [F]
        apply hf.comp
        simpa [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero] using
          (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => α) 0).symm.measurable
      have hFC : ∀ p, |F p| ≤ C := fun p => hC (Fin.cons p.1 p.2)
      have hvar_equiv :
          Var[f; Measure.pi (fun _ : Fin (n + 1) => μ)] = Var[F; μ.prod πn] := by
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
        have he := measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => μ) 0
        have hv := he.variance_fun_comp hF.aemeasurable
        simpa [e, F, πn, Function.comp_def, MeasurableEquiv.piFinSuccAbove,
          Fin.insertNthEquiv, Fin.insertNth_zero] using hv
      have htail_resample (a : α) (i : Fin n) (x : Fin n → α) :
          conditionalCoordinateEnergy (μ := μ) (fun t => F (a, t)) i x ≤ K i.succ := by
        have h := hresample i.succ (Fin.cons a x)
        simpa [conditionalCoordinateEnergy, F, Fin.cons_update] using h
      have htail (a : α) :
          Var[(fun t => F (a, t)); πn] ≤
            (1 / 2 : ℝ) * ∑ i : Fin n, K i.succ := by
        apply ih (hf := hF.comp (measurable_prod_mk_left a))
          (K := fun i => K i.succ)
        · exact fun t => hFC (a, t)
        · exact fun i => hK i.succ
        · exact htail_resample a
      have htail_integral :
          (∫ a, Var[(fun t => F (a, t)); πn] ∂μ) ≤
            (1 / 2 : ℝ) * ∑ i : Fin n, K i.succ := by
        calc
          (∫ a, Var[(fun t => F (a, t)); πn] ∂μ) ≤
              ∫ _a, (1 / 2 : ℝ) * ∑ i : Fin n, K i.succ ∂μ := by
            apply integral_mono
            · exact integrable_variance_fiber_bounded (ν := μ) (κ := πn) hF C hFC
            · exact integrable_const _
            · exact htail
          _ = (1 / 2 : ℝ) * ∑ i : Fin n, K i.succ := by simp
      let d : (α × α) × (Fin n → α) → ℝ := fun q =>
        (F (q.1.1, q.2) - F (q.1.2, q.2)) ^ 2
      have hd_meas : Measurable d := by
        dsimp [d]
        fun_prop
      have hd_int : Integrable d ((μ.prod μ).prod πn) := by
        apply Integrable.of_bound hd_meas.aestronglyMeasurable ((2 * C) ^ 2)
        filter_upwards with q
        dsimp [d]
        simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow]
        have hsub : |F (q.1.1, q.2) - F (q.1.2, q.2)| ≤
            |F (q.1.1, q.2)| + |F (q.1.2, q.2)| := abs_sub _ _
        nlinarith [abs_nonneg (F (q.1.1, q.2)), abs_nonneg (F (q.1.2, q.2)),
          abs_nonneg (F (q.1.1, q.2) - F (q.1.2, q.2)),
          hFC (q.1.1, q.2), hFC (q.1.2, q.2)]
      have hhead_cond (t : Fin n → α) :
          (∫ p : α × α, d (p, t) ∂μ.prod μ) ≤ K 0 := by
        have h := hresample (0 : Fin (n + 1))
          (Fin.cons (Classical.choice (inferInstance : Nonempty α)) t)
        simpa [conditionalCoordinateEnergy, d, F, Fin.update_cons_zero] using h
      have htriple :
          (∫ p : α × α, ∫ t, d (p, t) ∂πn ∂μ.prod μ) ≤ K 0 := by
        calc
          (∫ p : α × α, ∫ t, d (p, t) ∂πn ∂μ.prod μ) =
              ∫ t, ∫ p : α × α, d (p, t) ∂μ.prod μ ∂πn :=
            integral_integral_swap hd_int
          _ ≤ ∫ _t, K 0 ∂πn := by
            apply integral_mono hd_int.swap.integral_prod_left (integrable_const _)
            exact hhead_cond
          _ = K 0 := by simp [πn]
      have hhead :
          Var[(fun a => ∫ t, F (a, t) ∂πn); μ] ≤ (1 / 2 : ℝ) * K 0 := by
        calc
          Var[(fun a => ∫ t, F (a, t) ∂πn); μ] ≤
              (1 / 2 : ℝ) *
                ∫ p : α × α, ∫ t, d (p, t) ∂πn ∂μ.prod μ := by
            simpa [d] using
              (variance_integral_fiber_le_half_resample
                (ν := μ) (κ := πn) hF C hFC)
          _ ≤ (1 / 2 : ℝ) * K 0 := by gcongr
      rw [hvar_equiv, variance_prod_eq_integral_variance_add hF C hFC]
      calc
        (∫ x, Var[(fun y => F (x, y)); πn] ∂μ) +
              Var[(fun x => ∫ y, F (x, y) ∂πn); μ] ≤
            (1 / 2 : ℝ) * ∑ i : Fin n, K i.succ + (1 / 2 : ℝ) * K 0 :=
          add_le_add htail_integral hhead
        _ = (1 / 2 : ℝ) * ∑ i : Fin (n + 1), K i := by
          rw [Fin.sum_univ_succ]
          ring

/-- `L²` Efron--Stein.  The conditional resampling differences are assumed
integrable; the numerical hypothesis is otherwise identical to the bounded
theorem.  Symmetric clipping preserves every resampling bound because it is
one-Lipschitz, and dominated convergence removes the clipping. -/
theorem efronStein_fin_product
    (n : ℕ) {f : (Fin n → α) → ℝ} (hf : Measurable f)
    (hf2 : MemLp f 2 (Measure.pi (fun _ : Fin n => μ)))
    (K : Fin n → ℝ) (hK : ∀ i, 0 ≤ K i)
    (hresample_int : ∀ i x,
      Integrable (fun p : α × α =>
        (f (Function.update x i p.1) - f (Function.update x i p.2)) ^ 2) (μ.prod μ))
    (hresample : ∀ i x, conditionalCoordinateEnergy (μ := μ) f i x ≤ K i) :
    Var[f; Measure.pi (fun _ : Fin n => μ)] ≤
      (1 / 2 : ℝ) * ∑ i, K i := by
  let πn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => μ)
  let fclip : ℕ → (Fin n → α) → ℝ := fun T x => clip (T : ℝ) (f x)
  have hfclip_meas (T : ℕ) : Measurable (fclip T) :=
    (clip_measurable T).comp hf
  have hfclip_bound (T : ℕ) (x : Fin n → α) : |fclip T x| ≤ (T : ℝ) := by
    exact abs_clip_le _ _ (Nat.cast_nonneg T)
  have hclip_diff (T : ℕ) (i : Fin n) (x : Fin n → α) (p : α × α) :
      (fclip T (Function.update x i p.1) -
          fclip T (Function.update x i p.2)) ^ 2 ≤
        (f (Function.update x i p.1) -
          f (Function.update x i p.2)) ^ 2 := by
    have h := abs_clip_sub_clip_le (T : ℝ)
      (f (Function.update x i p.1)) (f (Function.update x i p.2))
    dsimp [fclip]
    exact sq_le_sq.mpr h
  have hclip_resample (T : ℕ) (i : Fin n) (x : Fin n → α) :
      conditionalCoordinateEnergy (μ := μ) (fclip T) i x ≤ K i := by
    calc
      conditionalCoordinateEnergy (μ := μ) (fclip T) i x ≤
          conditionalCoordinateEnergy (μ := μ) f i x := by
        apply integral_mono
        · apply (hresample_int i x).mono
          · have hm : Measurable (fun p : α × α =>
                (fclip T (Function.update x i p.1) -
                  fclip T (Function.update x i p.2)) ^ 2) := by
              fun_prop
            exact hm.aestronglyMeasurable
          · filter_upwards with p
            let a := fclip T (Function.update x i p.1) -
              fclip T (Function.update x i p.2)
            let b := f (Function.update x i p.1) -
              f (Function.update x i p.2)
            have hab : a ^ 2 ≤ b ^ 2 := hclip_diff T i x p
            change |a ^ 2| ≤ |b ^ 2|
            rw [abs_of_nonneg (sq_nonneg a), abs_of_nonneg (sq_nonneg b)]
            exact hab
        · exact hresample_int i x
        · exact hclip_diff T i x
      _ ≤ K i := hresample i x
  have hvar_clip (T : ℕ) :
      Var[fclip T; πn] ≤ (1 / 2 : ℝ) * ∑ i, K i := by
    exact efronStein_fin_product_bounded (μ := μ) n (hfclip_meas T) T
      (hfclip_bound T) K hK (hclip_resample T)
  have hf_int : Integrable f πn := hf2.integrable one_le_two
  have hf_sq : Integrable (fun x => f x ^ 2) πn := hf2.integrable_sq
  have hclip_lim (x : Fin n → α) :
      Tendsto (fun T : ℕ => fclip T x) atTop (𝓝 (f x)) := by
    exact (clip_tendsto_atTop (f x)).comp tendsto_natCast_atTop_atTop
  have hint : Tendsto (fun T : ℕ => ∫ x, fclip T x ∂πn) atTop (𝓝 (∫ x, f x ∂πn)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |f x|)
    · exact fun T => (hfclip_meas T).aestronglyMeasurable
    · exact hf_int.abs
    · intro T
      exact ae_of_all _ fun x => by
        simpa [Real.norm_eq_abs] using abs_clip_le_abs (T : ℝ) (f x) (Nat.cast_nonneg T)
    · exact ae_of_all _ hclip_lim
  have hint_sq : Tendsto (fun T : ℕ => ∫ x, (fclip T x) ^ 2 ∂πn) atTop
      (𝓝 (∫ x, f x ^ 2 ∂πn)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => f x ^ 2)
    · exact fun T => ((hfclip_meas T).pow_const 2).aestronglyMeasurable
    · exact hf_sq
    · intro T
      exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (fclip T x))]
        have h := abs_clip_le_abs (T : ℝ) (f x) (Nat.cast_nonneg T)
        exact sq_le_sq.mpr h
    · exact ae_of_all _ fun x => (hclip_lim x).pow 2
  have hfclip_mem (T : ℕ) : MemLp (fclip T) 2 πn := by
    apply MemLp.of_bound (hfclip_meas T).aestronglyMeasurable (T : ℝ)
    exact ae_of_all _ fun x => by
      simpa [Real.norm_eq_abs] using hfclip_bound T x
  have hvar_tendsto : Tendsto (fun T : ℕ => Var[fclip T; πn]) atTop (𝓝 Var[f; πn]) := by
    have hsub := hint_sq.sub (hint.pow 2)
    have hvar_eq (T : ℕ) :
        Var[fclip T; πn] =
          (∫ x, (fclip T x) ^ 2 ∂πn) - (∫ x, fclip T x ∂πn) ^ 2 := by
      simpa only [Pi.pow_apply] using variance_eq_sub (hfclip_mem T)
    have hf_var_eq :
        Var[f; πn] = (∫ x, f x ^ 2 ∂πn) - (∫ x, f x ∂πn) ^ 2 := by
      simpa only [Pi.pow_apply] using variance_eq_sub hf2
    simpa only [hvar_eq, hf_var_eq] using hsub
  exact le_of_tendsto' hvar_tendsto hvar_clip

end FiniteProductEfronStein

section FiniteFamilyConcentration

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- Maximum absolute centered deviation of a nonempty finite family.  The
indexing by `Fin (m + 1)` records nonemptiness in the type and avoids an
auxiliary choice hypothesis at callers. -/
def maxCenteredDeviation {m : ℕ} (Y : Fin (m + 1) → Ω → ℝ)
    (ν : Measure Ω) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => |Y i ω - ∫ x, Y i x ∂ν|)

theorem measurable_maxCenteredDeviation {m : ℕ}
    {Y : Fin (m + 1) → Ω → ℝ} (hY : ∀ i, Measurable (Y i)) :
    Measurable (maxCenteredDeviation Y ν) := by
  change Measurable (fun ω =>
    Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin (m + 1) => |Y i ω - ∫ x, Y i x ∂ν|))
  have hsup : Measurable
      (Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (m + 1) => fun ω =>
          |Y i ω - ∫ x, Y i x ∂ν|)) := by
    apply Finset.measurable_sup'
    intro i _hi
    fun_prop
  have heq :
      (fun ω => Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (m + 1) => |Y i ω - ∫ x, Y i x ∂ν|)) =
      Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (m + 1) => fun ω =>
          |Y i ω - ∫ x, Y i x ∂ν|) := by
    funext ω
    exact (Finset.sup'_apply Finset.univ_nonempty
      (fun i : Fin (m + 1) => fun ω =>
        |Y i ω - ∫ x, Y i x ∂ν|) ω).symm
  rw [heq]
  exact hsup

/-- The Cauchy--Schwarz/Jensen step used after the individual Efron--Stein
bounds in Lemma 10.5. -/
theorem integral_maxCenteredDeviation_le_sqrt_sum_variance
    [IsProbabilityMeasure ν] {m : ℕ} {Y : Fin (m + 1) → Ω → ℝ}
    (hY : ∀ i, Measurable (Y i)) (hY2 : ∀ i, MemLp (Y i) 2 ν) :
    (∫ ω, maxCenteredDeviation Y ν ω ∂ν) ≤
      Real.sqrt (∑ i, Var[Y i; ν]) := by
  let centered : Fin (m + 1) → Ω → ℝ := fun i ω =>
    Y i ω - ∫ x, Y i x ∂ν
  let S : Ω → ℝ := fun ω => ∑ i, (centered i ω) ^ 2
  let M : Ω → ℝ := maxCenteredDeviation Y ν
  have hcenter_meas (i : Fin (m + 1)) : Measurable (centered i) := by
    dsimp [centered]
    exact (hY i).sub_const _
  have hcenter_mem (i : Fin (m + 1)) : MemLp (centered i) 2 ν := by
    dsimp [centered]
    exact (hY2 i).sub (memLp_const _)
  have hcenter_sq_int (i : Fin (m + 1)) :
      Integrable (fun ω => (centered i ω) ^ 2) ν :=
    (hcenter_mem i).integrable_sq
  have hS_meas : Measurable S := by
    dsimp [S]
    fun_prop
  have hS_int : Integrable S ν := by
    dsimp [S]
    exact integrable_finsetSum Finset.univ (fun i _hi => hcenter_sq_int i)
  have hS_nonneg (ω : Ω) : 0 ≤ S ω := by
    dsimp [S]
    exact Finset.sum_nonneg fun _i _hi => sq_nonneg _
  have hM_meas : Measurable M := by
    exact measurable_maxCenteredDeviation hY
  have hM_nonneg (ω : Ω) : 0 ≤ M ω := by
    dsimp [M, maxCenteredDeviation]
    calc
      0 ≤ |Y 0 ω - ∫ x, Y 0 x ∂ν| := abs_nonneg _
      _ ≤ Finset.univ.sup' Finset.univ_nonempty
          (fun i => |Y i ω - ∫ x, Y i x ∂ν|) :=
        Finset.le_sup'
          (fun i : Fin (m + 1) => |Y i ω - ∫ x, Y i x ∂ν|)
          (Finset.mem_univ (0 : Fin (m + 1)))
  have hM_le_sqrt (ω : Ω) : M ω ≤ Real.sqrt (S ω) := by
    dsimp [M, maxCenteredDeviation]
    apply Finset.sup'_le
    intro i _hi
    apply Real.le_sqrt_of_sq_le
    dsimp [S, centered]
    simpa only [sq_abs] using
      (Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : Fin (m + 1) =>
          (Y j ω - ∫ x, Y j x ∂ν) ^ 2)
        (fun j _hj => sq_nonneg (Y j ω - ∫ x, Y j x ∂ν))
        (Finset.mem_univ i))
  have hsqrt_meas : Measurable (fun ω => Real.sqrt (S ω)) :=
    Real.continuous_sqrt.measurable.comp hS_meas
  have hsqrt_sq_int : Integrable (fun ω => (Real.sqrt (S ω)) ^ 2) ν := by
    apply hS_int.congr
    exact ae_of_all _ fun ω => (Real.sq_sqrt (hS_nonneg ω)).symm
  have hsqrt_mem : MemLp (fun ω => Real.sqrt (S ω)) 2 ν :=
    (memLp_two_iff_integrable_sq hsqrt_meas.aestronglyMeasurable).2 hsqrt_sq_int
  have hsqrt_int : Integrable (fun ω => Real.sqrt (S ω)) ν :=
    hsqrt_mem.integrable one_le_two
  have hM_int : Integrable M ν := by
    apply hsqrt_int.mono hM_meas.aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      simpa only [Real.norm_of_nonneg (hM_nonneg ω),
        Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hM_le_sqrt ω
  have hsqrt_integral_sq :
      (∫ ω, Real.sqrt (S ω) ∂ν) ^ 2 ≤ ∫ ω, S ω ∂ν := by
    have h := sq_integral_le_integral_sq hsqrt_mem
    rw [integral_congr_ae
      (ae_of_all _ fun ω => Real.sq_sqrt (hS_nonneg ω))] at h
    exact h
  have hS_integral : (∫ ω, S ω ∂ν) = ∑ i, Var[Y i; ν] := by
    calc
      (∫ ω, S ω ∂ν) =
          ∑ i, ∫ ω, (centered i ω) ^ 2 ∂ν := by
        dsimp [S]
        rw [integral_finsetSum Finset.univ (fun i _hi => hcenter_sq_int i)]
      _ = ∑ i, Var[Y i; ν] := by
        apply Finset.sum_congr rfl
        intro i _hi
        dsimp [centered]
        exact (variance_eq_integral (hY i).aemeasurable).symm
  calc
    (∫ ω, maxCenteredDeviation Y ν ω ∂ν) = ∫ ω, M ω ∂ν := rfl
    _ ≤ ∫ ω, Real.sqrt (S ω) ∂ν :=
      integral_mono hM_int hsqrt_int hM_le_sqrt
    _ ≤ Real.sqrt (∫ ω, S ω ∂ν) :=
      Real.le_sqrt_of_sq_le hsqrt_integral_sq
    _ = Real.sqrt (∑ i, Var[Y i; ν]) := by rw [hS_integral]

end FiniteFamilyConcentration

section EfronSteinFiniteFamily

variable {α : Type*} [MeasurableSpace α] [Nonempty α]
  {μ : Measure α} [IsProbabilityMeasure μ]

/-- Reusable probability skeleton of Lemma 10.5: coordinate resampling bounds
for every degree directly imply the expected maximal centered deviation
bound.  There is no intermediate concentration certificate for callers to
instantiate. -/
theorem efronStein_maxCenteredDeviation
    (n m : ℕ) {Y : Fin (m + 1) → (Fin n → α) → ℝ}
    (hY : ∀ r, Measurable (Y r))
    (hY2 : ∀ r, MemLp (Y r) 2 (Measure.pi (fun _ : Fin n => μ)))
    (K : Fin (m + 1) → Fin n → ℝ)
    (hK : ∀ r i, 0 ≤ K r i)
    (hresample_int : ∀ r i x,
      Integrable (fun p : α × α =>
        (Y r (Function.update x i p.1) -
          Y r (Function.update x i p.2)) ^ 2) (μ.prod μ))
    (hresample : ∀ r i x,
      conditionalCoordinateEnergy (μ := μ) (Y r) i x ≤ K r i) :
    (∫ ω, maxCenteredDeviation Y (Measure.pi (fun _ : Fin n => μ)) ω
        ∂Measure.pi (fun _ : Fin n => μ)) ≤
      Real.sqrt (∑ r, (1 / 2 : ℝ) * ∑ i, K r i) := by
  let πn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => μ)
  have hbase := integral_maxCenteredDeviation_le_sqrt_sum_variance
    (ν := πn) hY hY2
  calc
    (∫ ω, maxCenteredDeviation Y (Measure.pi (fun _ : Fin n => μ)) ω
        ∂Measure.pi (fun _ : Fin n => μ)) ≤
        Real.sqrt (∑ r, Var[Y r; πn]) := hbase
    _ ≤ Real.sqrt (∑ r, (1 / 2 : ℝ) * ∑ i, K r i) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro r _hr
      exact efronStein_fin_product (μ := μ) n (hY r) (hY2 r)
        (K r) (hK r) (hresample_int r) (hresample r)

end EfronSteinFiniteFamily

end

end BernoulliSection10
