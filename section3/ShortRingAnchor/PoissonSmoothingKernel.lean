import Vendor.Arxiv2410.V3.PoissonCounting
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Lemma 3.5: the scalar Poisson smoothing inequalities

All statements here are elementary real analysis. No limiting law, density
bound, integrability formula, or random-matrix theorem is assumed.
-/

open Set MeasureTheory
open scoped Interval

noncomputable section
namespace ShortRingAnchor
open Arxiv2410V3

/-- Lemma 3.5: the Poisson convolution of an interval indicator. -/
def poissonWindow (v a b x : ℝ) : ℝ :=
  (Real.arctan ((b - x) / v) - Real.arctan ((a - x) / v)) / Real.pi

/-- Lemma 3.5: the closed interval indicator, including both endpoints. -/
def closedIntervalIndicator (a b x : ℝ) : ℝ := if a ≤ x ∧ x ≤ b then 1 else 0

/-- Lemma 3.5 kernel tail: the elementary bound `arctan x ≤ x` for `x ≥ 0`. -/
theorem arctan_le_self_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  simpa only [Real.tan_arctan] using
    Real.le_tan (Real.arctan_nonneg.mpr hx) (Real.arctan_lt_pi_div_two x)

/-- Lemma 3.5: the one-sided Poisson tail is bounded by `v/delta`. -/
theorem arctan_upper_tail_le {v delta y : ℝ}
    (hv : 0 < v) (hd : 0 < delta) (hy : delta ≤ y) :
    Real.pi / 2 - Real.arctan (y / v) ≤ v / delta := by
  have hy0 : 0 < y := hd.trans_le hy
  calc
    Real.pi / 2 - Real.arctan (y / v) = Real.arctan (v / y) := by
      rw [← Real.arctan_inv_of_pos (div_pos hy0 hv), inv_div]
    _ ≤ v / y := arctan_le_self_nonneg (div_nonneg hv.le hy0.le)
    _ ≤ v / delta := div_le_div_of_nonneg_left hv.le hd hy

/-- Lemma 3.5: the lower-side kernel tail, by oddness of arctangent. -/
theorem arctan_lower_tail_le {v delta y : ℝ}
    (hv : 0 < v) (hd : 0 < delta) (hy : y ≤ -delta) :
    Real.arctan (y / v) + Real.pi / 2 ≤ v / delta := by
  have h := arctan_upper_tail_le hv hd (show delta ≤ -y by linarith)
  rw [neg_div, Real.arctan_neg] at h
  linarith

/-- Lemma 3.5: the smoothed interval indicator is nonnegative. -/
theorem poissonWindow_nonneg {v a b x : ℝ} (hv : 0 < v) (hab : a ≤ b) :
    0 ≤ poissonWindow v a b x := by
  apply div_nonneg _ Real.pi_pos.le
  exact sub_nonneg.mpr (Real.arctan_le_arctan_iff.mpr
    (div_le_div_of_nonneg_right (by linarith) hv.le))

/-- Lemma 3.5: Poisson smoothing does not exceed total mass one. -/
theorem poissonWindow_le_one (v a b x : ℝ) : poissonWindow v a b x ≤ 1 := by
  unfold poissonWindow
  apply (div_le_iff₀ Real.pi_pos).mpr
  linarith [Real.arctan_lt_pi_div_two ((b - x) / v),
    Real.neg_pi_div_two_lt_arctan ((a - x) / v)]

/-- Lemma 3.5: enlarging the endpoints captures all but `O(v/delta)`
of the kernel mass at every point of the original closed interval. -/
theorem one_le_poissonWindow_enlarged_add_tail {v delta a b x : ℝ}
    (hv : 0 < v) (hd : 0 < delta) (hx : x ∈ Icc a b) :
    1 ≤ poissonWindow v (a - delta) (b + delta) x + 2 * (v / delta) / Real.pi := by
  have hright := arctan_upper_tail_le hv hd (show delta ≤ b + delta - x by linarith [hx.2])
  have hleft := arctan_lower_tail_le hv hd (show a - delta - x ≤ -delta by linarith [hx.1])
  unfold poissonWindow
  rw [← add_div]
  apply (le_div_iff₀ Real.pi_pos).mpr
  linarith

/-- Lemma 3.5, upper smoothing inequality at the scalar level. -/
theorem closedIntervalIndicator_le_poissonWindow_enlarged_add_tail
    {v delta a b : ℝ} (hv : 0 < v) (hd : 0 < delta) (hab : a ≤ b) (x : ℝ) :
    closedIntervalIndicator a b x ≤
      poissonWindow v (a - delta) (b + delta) x + 2 * (v / delta) / Real.pi := by
  unfold closedIntervalIndicator
  split_ifs with hx
  · exact one_le_poissonWindow_enlarged_add_tail hv hd hx
  · exact add_nonneg (poissonWindow_nonneg hv (by linarith)) (by positivity)

/-- Lemma 3.5, lower smoothing inequality at the scalar level. The bound
is uniform over all real spectral points, including points far outside the compact set. -/
theorem poissonWindow_le_closedIntervalIndicator_enlarged_add_tail
    {v delta a b : ℝ} (hv : 0 < v) (hd : 0 < delta) (x : ℝ) :
    poissonWindow v a b x ≤
      closedIntervalIndicator (a - delta) (b + delta) x + 2 * (v / delta) / Real.pi := by
  unfold closedIntervalIndicator
  split_ifs with hx
  · exact (poissonWindow_le_one _ _ _ _).trans (le_add_of_nonneg_right (by positivity))
  · have hcase : x < a - delta ∨ b + delta < x := by
      by_cases h : a - delta ≤ x
      · exact Or.inr (lt_of_not_ge (fun h' => hx ⟨h, h'⟩))
      · exact Or.inl (lt_of_not_ge h)
    rw [zero_add]
    unfold poissonWindow
    apply (div_le_div_iff_of_pos_right Real.pi_pos).mpr
    rcases hcase with hleft | hright
    · have ht := arctan_upper_tail_le hv hd (show delta ≤ a - x by linarith)
      have hvd : 0 ≤ v / delta := by positivity
      linarith [Real.arctan_lt_pi_div_two ((b - x) / v)]
    · have ht := arctan_lower_tail_le hv hd (show b - x ≤ -delta by linarith)
      have hvd : 0 ≤ v / delta := by positivity
      linarith [Real.neg_pi_div_two_lt_arctan ((a - x) / v)]

/-- Lemma 3.5: continuity of the (unnormalized) Poisson kernel on the line. -/
theorem continuous_poissonKernel_shift {v : ℝ} (hv : 0 < v) (x : ℝ) :
    Continuous (fun u : ℝ => poissonKernel v (x - u)) := by
  unfold poissonKernel
  exact continuous_const.div (by fun_prop) (fun u => ne_of_gt (by positivity))

/-- Lemma 3.5: the arctangent primitive has exactly the Poisson derivative. -/
theorem hasDerivAt_arctan_shift {v : ℝ} (hv : 0 < v) (x u : ℝ) :
    HasDerivAt (fun t : ℝ => Real.arctan ((t - x) / v))
      (poissonKernel v (x - u)) u := by
  have h : HasDerivAt (fun t : ℝ => Real.arctan ((t - x) / v))
      (1 / (1 + ((u - x) / v) ^ 2) * (1 / v)) u := by
    simpa only [id_eq] using (((hasDerivAt_id u).sub_const x).div_const v).arctan
  convert h using 1
  unfold poissonKernel
  field_simp
  <;> ring

/-- Lemma 3.5: exact Poisson integral of the interval indicator. -/
theorem poissonWindow_eq_integral {v : ℝ} (hv : 0 < v) (a b x : ℝ) :
    poissonWindow v a b x = (∫ u in a..b, poissonKernel v (x - u)) / Real.pi := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_arctan_shift hv x u)
    ((continuous_poissonKernel_shift hv x).intervalIntegrable a b)]
  rfl

end ShortRingAnchor
