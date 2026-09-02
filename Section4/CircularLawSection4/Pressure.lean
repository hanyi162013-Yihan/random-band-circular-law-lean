import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite-dimensional core of pressure concentration

This is the deterministic inequality in the last Cauchy--Schwarz step of
Proposition `prop:pressure-concentration`.  The preceding probabilistic step
(row resampling plus Efron--Stein) supplies a second-moment bound for each
exterior degree; the result here accounts exactly for the `sqrt(2W+1)` loss.
-/

open scoped BigOperators
open Real

namespace CircularLawSection4

variable {ι : Type*}

/-- Maximum absolute coordinate of a nonempty finite real family. -/
noncomputable def pressureFiniteMax [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => |x i|

theorem pressureFiniteMax_nonneg [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) :
    0 ≤ pressureFiniteMax x := by
  classical
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i : ι => |x i|)
  rw [pressureFiniteMax, hi]
  exact abs_nonneg _

/-- Squaring the maximum costs no more than summing all coordinate squares. -/
theorem pressureFiniteMax_sq_le_sum_sq [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) :
    (pressureFiniteMax x) ^ 2 ≤ ∑ i, (x i) ^ 2 := by
  classical
  obtain ⟨i, hi, hmax⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i : ι => |x i|)
  rw [pressureFiniteMax, hmax, sq_abs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) hi

/-- Euclidean control of the maximum coordinate. -/
theorem pressureFiniteMax_le_sqrt_sum_sq [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) :
    pressureFiniteMax x ≤ √(∑ i, (x i) ^ 2) := by
  apply (Real.le_sqrt (pressureFiniteMax_nonneg x)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)).2
  exact pressureFiniteMax_sq_le_sum_sq x

/-- A uniform squared-coordinate bound incurs exactly a square-root
cardinality loss. -/
theorem pressureFiniteMax_le_sqrt_card_mul
    [Fintype ι] [Nonempty ι] (x : ι → ℝ) {V : ℝ}
    (hV : ∀ i, (x i) ^ 2 ≤ V) :
    pressureFiniteMax x ≤ √((Fintype.card ι : ℝ) * V) := by
  refine (pressureFiniteMax_le_sqrt_sum_sq x).trans (Real.sqrt_le_sqrt ?_)
  calc
    (∑ i, (x i) ^ 2) ≤ ∑ _i : ι, V :=
      Finset.sum_le_sum fun i _ => hV i
    _ = (Fintype.card ι : ℝ) * V := by simp

/-- Paper-shaped specialization to exterior degrees `0,...,2W`. -/
theorem pressureDegrees_max_le
    (W : ℕ) (x : Fin (2 * W).succ → ℝ) {V : ℝ}
    (hV : ∀ r, (x r) ^ 2 ≤ V) :
    pressureFiniteMax x ≤ √(((2 * W + 1 : ℕ) : ℝ) * V) := by
  simpa [Nat.succ_eq_add_one] using
    pressureFiniteMax_le_sqrt_card_mul x hV

end CircularLawSection4
