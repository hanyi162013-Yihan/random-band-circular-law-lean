import Vendor.Arxiv2410.V3.FreeDysonUniqueness
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # The scalar Ginibre Dyson equation on the positive imaginary axis

Uniqueness makes the canonical upper-half-plane solution purely imaginary.
Its imaginary part is then a positive real root of an explicit rational
equation.  The final deterministic calculation parameterizes a candidate
logarithmic primitive by `a = t + v`, so it does not assume differentiability
of the implicitly defined function `v(t)`.

This file does not assert either endpoint limits or random log-potential
convergence.  In particular it is not a replacement assumption for BC12.
-/

open Arxiv2410V3
open scoped ComplexConjugate

noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace CircularLawSection6.GinibreDyson

/-- Imaginary part of the canonical Dyson transform at `i t`. -/
def dysonV (z : ℂ) (t : ℝ) : ℝ :=
  (freeDysonStieltjes z (Complex.I * (t : ℂ))).im

/-- The real parameter `a = t + v` of the imaginary-axis Dyson equation. -/
def dysonA (z : ℂ) (t : ℝ) : ℝ := t + dysonV z t

private theorem scalarDysonEquation_reflect {z m : ℂ} {t : ℝ}
    (h : ScalarDysonEquation z (Complex.I * (t : ℂ)) m) :
    ScalarDysonEquation z (Complex.I * (t : ℂ)) (-conj m) := by
  have heta : -conj (Complex.I * (t : ℂ)) = Complex.I * (t : ℂ) := by simp
  have hsum : Complex.I * (t : ℂ) + -conj m =
      -conj (Complex.I * (t : ℂ) + m) := by
    simp only [map_add, neg_add, heta]
  unfold ScalarDysonEquation at h ⊢
  rw [hsum]
  have hc := congrArg (fun q : ℂ => -conj q) h
  simp only [map_add, map_neg, map_mul, map_inv₀, Complex.conj_ofReal] at hc
  simp only [map_add, map_mul, Complex.conj_ofReal, inv_neg, neg_neg]
  linear_combination hc

/-- Symmetry and the proved uniqueness theorem force a purely imaginary value. -/
theorem freeDysonStieltjes_re_eq_zero (z : ℂ) {t : ℝ} (ht : 0 < t) :
    (freeDysonStieltjes z (Complex.I * (t : ℂ))).re = 0 := by
  have heta : 0 < (Complex.I * (t : ℂ)).im := by simpa using ht
  have hm := freeDysonStieltjes_im_pos z _ heta
  have heq := freeDysonStieltjes_equation z _ heta
  have hreflect : 0 < (-conj (freeDysonStieltjes z (Complex.I * (t : ℂ)))).im := by
    simpa using hm
  have h := scalarDysonEquation_unique heta hm hreflect heq
    (scalarDysonEquation_reflect heq)
  have hre := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.conj_re] at hre
  linarith

theorem dysonV_pos (z : ℂ) {t : ℝ} (ht : 0 < t) : 0 < dysonV z t :=
  freeDysonStieltjes_im_pos z _ (by simpa using ht)

theorem dysonV_le_one (z : ℂ) {t : ℝ} (ht : 0 < t) : dysonV z t ≤ 1 :=
  freeDysonStieltjes_im_le_one z _ (by simpa using ht)

theorem dysonA_pos (z : ℂ) {t : ℝ} (ht : 0 < t) : 0 < dysonA z t :=
  add_pos ht (dysonV_pos z ht)

theorem freeDysonStieltjes_eq_I_mul (z : ℂ) {t : ℝ} (ht : 0 < t) :
    freeDysonStieltjes z (Complex.I * (t : ℂ)) = Complex.I * (dysonV z t : ℂ) := by
  apply Complex.ext
  · simpa using freeDysonStieltjes_re_eq_zero z ht
  · simp [dysonV]

private theorem normSq_I_mul (x : ℝ) :
    Complex.normSq (Complex.I * (x : ℂ)) = x ^ 2 := by
  simp [Complex.normSq_apply, pow_two]

/-- The real rational equation for any positive purely imaginary Dyson root. -/
theorem scalarDyson_imaginary_div {z : ℂ} {t v : ℝ}
    (ht : 0 < t) (hv : 0 < v)
    (h : ScalarDysonEquation z (Complex.I * (t : ℂ)) (Complex.I * (v : ℂ))) :
    v = (t + v) / ((t + v) ^ 2 + ‖z‖ ^ 2) := by
  have ha : 0 < t + v := add_pos ht hv
  have hden : 0 < (t + v) ^ 2 + ‖z‖ ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg ‖z‖)
  have hsum : Complex.I * (t : ℂ) + Complex.I * (v : ℂ) =
      Complex.I * ((t + v : ℝ) : ℂ) := by push_cast; ring
  have him := scalarDyson_imaginary_identity h
  rw [hsum, normSq_I_mul, normSq_I_mul, Complex.normSq_eq_norm_sq] at him
  have him0 : -(v / v ^ 2) = -(t + v) - ‖z‖ ^ 2 * (t + v) / (t + v) ^ 2 := by
    simpa using him
  have him1 : -(1 / v) = -(t + v) - ‖z‖ ^ 2 / (t + v) := by
    convert him0 using 1 <;> field_simp [hv.ne', ha.ne']
  apply (eq_div_iff hden.ne').2
  field_simp [hv.ne', ha.ne'] at him1
  nlinarith only [him1]

/-- Exact real form of the canonical imaginary-axis solution. -/
theorem dysonV_eq_div (z : ℂ) {t : ℝ} (ht : 0 < t) :
    dysonV z t = dysonA z t / ((dysonA z t) ^ 2 + ‖z‖ ^ 2) := by
  have h := freeDysonStieltjes_equation z (Complex.I * (t : ℂ)) (by simpa using ht)
  rw [freeDysonStieltjes_eq_I_mul z ht] at h
  exact scalarDyson_imaginary_div ht (dysonV_pos z ht) h

/-- The positive-`t` branch lies strictly above the algebraic endpoint. -/
theorem dysonA_sq_add_norm_sq_gt_one (z : ℂ) {t : ℝ} (ht : 0 < t) :
    1 < (dysonA z t) ^ 2 + ‖z‖ ^ 2 := by
  have hv := dysonV_pos z ht
  have ha := dysonA_pos z ht
  have hden : 0 < (dysonA z t) ^ 2 + ‖z‖ ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg ‖z‖)
  have hmul := (eq_div_iff hden.ne').1 (dysonV_eq_div z ht)
  by_contra hnot
  have hle := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) hv.le
  change dysonV z t * ((dysonA z t) ^ 2 + ‖z‖ ^ 2) ≤ dysonV z t * 1 at hle
  rw [hmul] at hle
  unfold dysonA at hle
  linarith

/-- Explicit imaginary part as a function of the auxiliary parameter. -/
def profileV (r a : ℝ) : ℝ := a / (a ^ 2 + r ^ 2)

/-- The physical height `t` as a function of `a`. -/
def profileT (r a : ℝ) : ℝ := a - profileV r a

/-- Candidate primitive in the auxiliary parameter. -/
def profileF (r a : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (a ^ 2 + r ^ 2) - (1 / 2 : ℝ) * (profileV r a) ^ 2

theorem profileT_dysonA (z : ℂ) {t : ℝ} (ht : 0 < t) :
    profileT ‖z‖ (dysonA z t) = t := by
  unfold profileT profileV
  rw [← dysonV_eq_div z ht]
  unfold dysonA
  ring

private theorem hasDerivAt_quadratic (r a : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 2 + r ^ 2) (2 * a) a := by
  simpa using ((hasDerivAt_id a).pow 2).add_const (r ^ 2)

theorem hasDerivAt_profileV {r a : ℝ} (h : a ^ 2 + r ^ 2 ≠ 0) :
    HasDerivAt (profileV r) ((r ^ 2 - a ^ 2) / (a ^ 2 + r ^ 2) ^ 2) a := by
  refine ((hasDerivAt_id a).fun_div (hasDerivAt_quadratic r a) h).congr_deriv ?_
  dsimp
  ring

theorem hasDerivAt_profileT {r a : ℝ} (h : a ^ 2 + r ^ 2 ≠ 0) :
    HasDerivAt (profileT r) (1 - (r ^ 2 - a ^ 2) / (a ^ 2 + r ^ 2) ^ 2) a :=
  (hasDerivAt_id a).sub (hasDerivAt_profileV h)

/-- The parameterized derivative identity `F'(a) = v(a) t'(a)`. -/
theorem hasDerivAt_profileF {r a : ℝ} (h : a ^ 2 + r ^ 2 ≠ 0) :
    HasDerivAt (profileF r)
      (profileV r a * (1 - (r ^ 2 - a ^ 2) / (a ^ 2 + r ^ 2) ^ 2)) a := by
  have hlog := ((hasDerivAt_quadratic r a).log h).const_mul (1 / 2 : ℝ)
  have hsq := ((hasDerivAt_profileV h).pow 2).const_mul (1 / 2 : ℝ)
  refine (hlog.sub hsq).congr_deriv ?_
  dsimp [profileV]
  ring

theorem deriv_profileF_eq_profileV_mul_deriv_profileT {r a : ℝ}
    (h : a ^ 2 + r ^ 2 ≠ 0) :
    deriv (profileF r) a = profileV r a * deriv (profileT r) a := by
  rw [(hasDerivAt_profileF h).deriv, (hasDerivAt_profileT h).deriv]

end CircularLawSection6.GinibreDyson
