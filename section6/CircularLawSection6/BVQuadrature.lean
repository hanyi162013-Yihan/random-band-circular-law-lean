import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith

/-! # A uniform bounded-variation quadrature error

The error is bounded by mesh size times total variation, independently of
the number of mesh cells. This is the estimate needed when the sampling
window grows with the matrix dimension.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace CircularLawSection6

theorem abs_sub_le_variation {f : ℝ → ℝ} {S : Set ℝ}
    (hf : BoundedVariationOn f S) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    |f x - f y| ≤ (eVariationOn f S).toReal := by
  have h := ENNReal.toReal_mono hf (eVariationOn.edist_le f hx hy)
  simpa only [← dist_edist, Real.dist_eq] using h

theorem leftRectangle_error_le {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b) (hBV : BoundedVariationOn f (Icc a b)) :
    |(b - a) * f a - ∫ x in a..b, f x| ≤
      (b - a) * (eVariationOn f (Icc a b)).toReal := by
  have heq : (b - a) * f a - ∫ x in a..b, f x = ∫ x in a..b, f a - f x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hf.intervalIntegrable,
      intervalIntegral.integral_const]
    rfl
  rw [heq, ← Real.norm_eq_abs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x => f a - f x) (a := a) (b := b) (C := (eVariationOn f (Icc a b)).toReal)
    (fun x hx => by
      rw [uIoc_of_le hab] at hx
      simpa only [Real.norm_eq_abs] using
        abs_sub_le_variation hBV (left_mem_Icc.2 hab) ⟨hx.1.le, hx.2⟩)
  simpa only [abs_of_nonneg (sub_nonneg.2 hab), mul_comm] using h

theorem leftRectangleSum_error_le {f : ℝ → ℝ} (hf : Continuous f)
    (hBV : BoundedVariationOn f univ) (u : ℕ → ℝ) (hu : Monotone u)
    (n : ℕ) {δ : ℝ} (hmesh : ∀ i < n, u (i + 1) - u i ≤ δ) :
    |(∑ i ∈ Finset.range n, (u (i + 1) - u i) * f (u i)) -
        ∫ x in u 0..u n, f x| ≤
      δ * (eVariationOn f (Icc (u 0) (u n))).toReal := by
  have hcell (i : ℕ) : BoundedVariationOn f (Icc (u i) (u (i + 1))) :=
    hBV.mono (subset_univ _)
  have hint := intervalIntegral.sum_integral_adjacent_intervals
    (a := u) (n := n) (fun _ _ => hf.intervalIntegrable)
  have hvar : (∑ i ∈ Finset.range n,
      (eVariationOn f (Icc (u i) (u (i + 1)))).toReal) =
        (eVariationOn f (Icc (u 0) (u n))).toReal := by
    rw [← ENNReal.toReal_sum (fun i _ => hcell i), eVariationOn.sum' f hu]
  rw [← hint, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |(u (i + 1) - u i) * f (u i) - ∫ x in u i..u (i + 1), f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, δ *
        (eVariationOn f (Icc (u i) (u (i + 1)))).toReal := by
      apply Finset.sum_le_sum
      intro i hi
      exact (leftRectangle_error_le hf (hu (Nat.le_succ i)) (hcell i)).trans
        (mul_le_mul_of_nonneg_right (hmesh i (Finset.mem_range.1 hi)) ENNReal.toReal_nonneg)
    _ = _ := by rw [← Finset.mul_sum, hvar]

theorem uniformMesh_error_le {f : ℝ → ℝ} (hf : Continuous f)
    (hBV : BoundedVariationOn f univ) (a : ℝ) (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    |δ * (∑ i ∈ Finset.range n, f (a + i * δ)) -
        ∫ x in a..a + n * δ, f x| ≤ δ * (eVariationOn f univ).toReal := by
  have hu : Monotone (fun i : ℕ => a + i * δ) := by
    intro i j hij
    exact add_le_add_left (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hδ) a
  have hstep (i : ℕ) : (a + (i + 1 : ℕ) * δ) - (a + i * δ) = δ := by
    push_cast
    ring
  have h := leftRectangleSum_error_le hf hBV _ hu n (fun i _ => (hstep i).le)
  simp only [hstep, ← Finset.mul_sum, Nat.cast_zero, zero_mul, add_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hBV (eVariationOn.mono f (subset_univ _))) hδ)

end CircularLawSection6
