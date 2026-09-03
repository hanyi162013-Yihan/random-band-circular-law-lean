import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Clipped logarithms and finite empirical distribution functions

This file proves the deterministic integration-by-parts step behind (3.12)
of Proposition 3.6.  Everything is formulated for a finite family of
nonnegative numbers, so no Lebesgue--Stieltjes measure API is needed.
-/

open Set MeasureTheory
open scoped BigOperators Interval

noncomputable section

namespace ShortRingAnchor

/-- Clamp a real number to the closed interval `[lo, hi]`. -/
def realClamp (lo hi x : Real) : Real := min hi (max lo x)

/-- The logarithm of a squared singular value, clipped between `a^2` and
`R^2`, with the factor `1/2` that converts back to `log s`. -/
def clippedLog (a R x : Real) : Real :=
  (1 / 2 : Real) * Real.log (realClamp (a ^ 2) (R ^ 2) x)

/-- Average of a test function over a nonempty finite family. -/
def empiricalAverage {I : Type*} [Fintype I] (x : I -> Real)
    (f : Real -> Real) : Real :=
  (∑ i, f (x i)) / (Fintype.card I : Real)

/-- Empirical CDF of a finite family, using the source convention
`F(t) = # {i : x_i <= t} / #I`. -/
noncomputable def empiricalCdf {I : Type*} [Fintype I]
    (x : I -> Real) (t : Real) : Real :=
  (((Finset.univ.filter fun i => x i <= t).card : Nat) : Real) /
    (Fintype.card I : Real)

/-- Empirical average of the clipped logarithm. -/
def empiricalClippedLog {I : Type*} [Fintype I]
    (a R : Real) (x : I -> Real) : Real :=
  empiricalAverage x (clippedLog a R)

lemma realClamp_lower {lo hi x : Real} (hlohi : lo <= hi) :
    lo <= realClamp lo hi x := by
  exact le_min hlohi (le_max_left lo x)

lemma realClamp_upper {lo hi x : Real} : realClamp lo hi x <= hi := by
  exact min_le_left hi (max lo x)

lemma lt_realClamp_iff_of_mem_Ico {lo hi x t : Real}
    (ht : t ∈ Ico lo hi) :
    t < realClamp lo hi x <-> t < x := by
  rcases ht with ⟨hlot, hthi⟩
  constructor
  · intro h
    have hmax : t < max lo x := h.trans_le (min_le_right hi (max lo x))
    exact (lt_max_iff.mp hmax).resolve_left (not_lt_of_ge hlot)
  · intro htx
    exact lt_min hthi (lt_max_of_lt_right htx)

lemma continuousOn_one_div_Icc {u v : Real} (hu : 0 < u) :
    ContinuousOn (fun t : Real => 1 / t) (Icc u v) := by
  intro t ht
  exact continuousAt_const.div continuousAt_id
    (ne_of_gt (hu.trans_le ht.1)) |>.continuousWithinAt

lemma intervalIntegrable_one_div {u v : Real} (hu : 0 < u) (huv : u <= v) :
    IntervalIntegrable (fun t : Real => 1 / t) volume u v :=
  (continuousOn_one_div_Icc hu).intervalIntegrable_of_Icc huv

/-- The elementary antiderivative used in the layer-cake identity. -/
theorem intervalIntegral_one_div_eq_log_sub {u v : Real}
    (hu : 0 < u) (huv : u <= v) :
    (∫ t : Real in u..v, 1 / t) = Real.log v - Real.log u := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
  · exact Real.continuousOn_log.mono fun t ht =>
      ne_of_gt (hu.trans_le ht.1)
  · intro t ht
    simpa [one_div] using Real.hasDerivAt_log (ne_of_gt (hu.trans ht.1))
  · exact intervalIntegrable_one_div hu huv

/-- On a common clipping interval, thresholding the clamped value is the
same as thresholding the original value. -/
lemma commonIndicator_integral_eq_clampedInterval
    {lo hi x : Real} (hlohi : lo <= hi) :
    (∫ t : Real in Ico lo hi, (Iio x).indicator (fun t => 1 / t) t) =
      ∫ t : Real in lo..realClamp lo hi x, 1 / t := by
  let y := realClamp lo hi x
  have hloy : lo <= y := realClamp_lower hlohi
  have hyhi : y <= hi := realClamp_upper
  rw [intervalIntegral.integral_of_le hloy, ← integral_Ico_eq_integral_Ioc]
  rw [setIntegral_indicator measurableSet_Iio]
  apply setIntegral_congr_set
  filter_upwards [] with t
  apply propext
  change (((lo <= t) ∧ t < hi) ∧ t < x) ↔ ((lo <= t) ∧ t < y)
  constructor
  · intro ht
    refine ⟨ht.1.1, ?_⟩
    exact (lt_realClamp_iff_of_mem_Ico ht.1).2 ht.2
  · intro ht
    have hthi : t < hi := ht.2.trans_le hyhi
    exact ⟨⟨ht.1, hthi⟩,
      (lt_realClamp_iff_of_mem_Ico ⟨ht.1, hthi⟩).1 ht.2⟩

/-- Single-point layer-cake formula for the clipped logarithm. -/
theorem clippedLog_eq_log_add_integral
    {a R x : Real} (ha : 0 < a) (haR : a <= R) :
    clippedLog a R x = Real.log a +
      (1 / 2 : Real) *
        ∫ t : Real in Ico (a ^ 2) (R ^ 2),
          (Iio x).indicator (fun t => 1 / t) t := by
  have haR2 : a ^ 2 <= R ^ 2 := by nlinarith
  let y := realClamp (a ^ 2) (R ^ 2) x
  have hay : a ^ 2 <= y := realClamp_lower haR2
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hint := intervalIntegral_one_div_eq_log_sub ha2 hay
  have hcommon := commonIndicator_integral_eq_clampedInterval
    (x := x) haR2
  change (1 / 2 : Real) * Real.log y = _
  rw [hcommon, hint, Real.log_pow]
  ring

end ShortRingAnchor
