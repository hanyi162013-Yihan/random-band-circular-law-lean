import ShortRingAnchor.ClippedLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Low/middle/high logarithmic decomposition

This file supplies the deterministic truncation identity used to combine
(3.10)--(3.14).  It also proves a slightly coarser upper-edge estimate than
(3.13): `log s <= s^2 / R` for `s > R >= 1`.  The coarser bound still tends
to zero as `R -> infinity` and avoids importing an operator-norm estimate.
-/

open scoped BigOperators

noncomputable section

namespace ShortRingAnchor

/-- Amount by which clipping at `a` raises `log x`. -/
def lowerLogCorrection (a x : Real) : Real :=
  if x < a then Real.log a - Real.log x else 0

/-- Amount by which clipping at `R` lowers `log x`. -/
def upperLogCorrection (R x : Real) : Real :=
  if R < x then Real.log x - Real.log R else 0

/-- Empirical logarithmic average. -/
def empiricalLog {I : Type*} [Fintype I] (x : I -> Real) : Real :=
  empiricalAverage x Real.log

def empiricalLowerLogCorrection {I : Type*} [Fintype I]
    (a : Real) (x : I -> Real) : Real :=
  empiricalAverage x (lowerLogCorrection a)

def empiricalUpperLogCorrection {I : Type*} [Fintype I]
    (R : Real) (x : I -> Real) : Real :=
  empiricalAverage x (upperLogCorrection R)

theorem lowerLogCorrection_nonneg {a x : Real}
    (_ha : 0 < a) (hx : 0 < x) :
    0 <= lowerLogCorrection a x := by
  by_cases hxa : x < a
  · simp only [lowerLogCorrection, hxa, if_true]
    exact sub_nonneg.mpr (Real.log_le_log hx hxa.le)
  · simp [lowerLogCorrection, hxa]

theorem upperLogCorrection_nonneg {R x : Real}
    (hR : 0 < R) (_hx : 0 < x) :
    0 <= upperLogCorrection R x := by
  by_cases hRx : R < x
  · simp only [upperLogCorrection, hRx, if_true]
    exact sub_nonneg.mpr (Real.log_le_log hR hRx.le)
  · simp [upperLogCorrection, hRx]

/-- Exact pointwise low/middle/high decomposition. -/
theorem log_eq_clippedLog_sub_lower_add_upper
    {a R x : Real} (ha : 0 < a) (haR : a <= R) (hx : 0 < x) :
    Real.log x = clippedLog a R (x ^ 2) - lowerLogCorrection a x +
      upperLogCorrection R x := by
  have hR : 0 < R := ha.trans_le haR
  have ha2R2 : a ^ 2 <= R ^ 2 := by nlinarith
  by_cases hxa : x < a
  · have hx2a2 : x ^ 2 <= a ^ 2 := by nlinarith
    have hRx : ¬ R < x := not_lt_of_ge (hxa.le.trans haR)
    simp [clippedLog, realClamp, lowerLogCorrection, upperLogCorrection,
      hxa, hRx, max_eq_left hx2a2, min_eq_right ha2R2, Real.log_pow]
  · have hax : a <= x := le_of_not_gt hxa
    by_cases hRx : R < x
    · have hxa' : ¬ x < a := hxa
      have hR2x2 : R ^ 2 <= x ^ 2 := by nlinarith
      simp [clippedLog, realClamp, lowerLogCorrection, upperLogCorrection,
        hxa', hRx, max_eq_right (by nlinarith : a ^ 2 <= x ^ 2),
        min_eq_left hR2x2, Real.log_pow]
    · have hxR : x <= R := le_of_not_gt hRx
      have hax2 : a ^ 2 <= x ^ 2 := by nlinarith
      have hxR2 : x ^ 2 <= R ^ 2 := by nlinarith
      simp [clippedLog, realClamp, lowerLogCorrection, upperLogCorrection,
        hxa, hRx, max_eq_right hax2, min_eq_right hxR2, Real.log_pow]

/-- Finite empirical version of the exact truncation identity. -/
theorem empiricalLog_eq_clipped_sub_lower_add_upper
    {I : Type*} [Fintype I] {a R : Real} {x : I -> Real}
    (ha : 0 < a) (haR : a <= R) (hx : forall i, 0 < x i) :
    empiricalLog x = empiricalClippedLog a R (fun i => x i ^ 2) -
      empiricalLowerLogCorrection a x + empiricalUpperLogCorrection R x := by
  unfold empiricalLog empiricalClippedLog empiricalLowerLogCorrection
    empiricalUpperLogCorrection empiricalAverage
  rw [← sub_div, ← add_div]
  congr 1
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact log_eq_clippedLog_sub_lower_add_upper ha haR (hx i)

/-- Coarse upper-edge inequality sufficient for the `R -> infinity` step:
for `x > R >= 1`, the logarithmic excess is at most `x^2/R`. -/
theorem upperLogCorrection_le_sq_div
    {R x : Real} (hR : 1 <= R) (hx : 0 < x) :
    upperLogCorrection R x <= x ^ 2 / R := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  by_cases hRx : R < x
  · rw [upperLogCorrection, if_pos hRx]
    have hlogR : 0 <= Real.log R := Real.log_nonneg hR
    have hlogx_le : Real.log x <= x := by
      exact (Real.log_le_sub_one_of_pos hx).trans (by linarith)
    have hx_le : x <= x ^ 2 / R := by
      apply (le_div_iff₀ hRpos).2
      nlinarith
    linarith
  · rw [upperLogCorrection, if_neg hRx]
    exact div_nonneg (sq_nonneg x) hRpos.le

/-- Empirical upper-edge correction is controlled by the empirical second
moment divided by `R`. -/
theorem empiricalUpperLogCorrection_le_secondMoment_div
    {I : Type*} [Fintype I] {R : Real} {x : I -> Real}
    (hR : 1 <= R) (hx : forall i, 0 < x i) :
    empiricalUpperLogCorrection R x <=
      empiricalAverage x (fun t => t ^ 2) / R := by
  unfold empiricalUpperLogCorrection empiricalAverage
  calc
    (∑ i, upperLogCorrection R (x i)) / (Fintype.card I : Real)
        <= (∑ i, x i ^ 2 / R) / (Fintype.card I : Real) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          apply Finset.sum_le_sum
          intro i hi
          exact upperLogCorrection_le_sq_div hR (hx i)
    _ = ((∑ i, x i ^ 2) / R) / (Fintype.card I : Real) := by
          congr 1
          rw [Finset.sum_div]
    _ = (∑ i, x i ^ 2) / (Fintype.card I : Real) / R := by
          rw [div_div, div_div, mul_comm]

end ShortRingAnchor
