import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Circular scalar bands (`CYCLIC5.1`)

This is the deterministic constructor underlying the manuscript's labelled definition
`CYCLIC5.1`.  Rows and columns are indexed by `ZMod n`; an entry is parameterized by its
cyclic displacement `j - i`.  In the probabilistic model, `gaussian i s` is an independent
standard circular complex Gaussian.  That distributional assertion belongs in an
ordinary theorem hypothesis when concentration or comparison theorems are applied; the
matrix formula itself is completely deterministic.

The constructor is totalized at `n = 0` because `ZMod 0` exists in Lean.  Every
paper-facing matrix application must separately assume `0 < n`.
-/

open scoped BigOperators

namespace CircularLawSections56.Section6

/-- Circular scalar band with active displacement set `active`, variance weights `weight`,
and a supplied realization of the scalar entries.

This is the Lean counterpart of definition `CYCLIC5.1`:
`A(i,i+s) = sqrt(q_s) g_(i,s)`, with all inactive displacements set to zero. -/
noncomputable def cyclicGaussianBandMatrix (n : ℕ)
    (active : Finset (ZMod n)) (weight : ZMod n → ℝ)
    (gaussian : ZMod n → ZMod n → ℂ) : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j =>
    if _h : j - i ∈ active then
      (Real.sqrt (weight (j - i)) : ℂ) * gaussian i (j - i)
    else 0

/-- Entries with inactive displacement vanish. -/
@[simp]
theorem cyclicGaussianBandMatrix_eq_zero_of_not_mem
    (n : ℕ) (active : Finset (ZMod n)) (weight : ZMod n → ℝ)
    (gaussian : ZMod n → ZMod n → ℂ) (i j : ZMod n)
    (h : j - i ∉ active) :
    cyclicGaussianBandMatrix n active weight gaussian i j = 0 := by
  simp [cyclicGaussianBandMatrix, h]

/-- Formula for an active cyclic displacement. -/
@[simp]
theorem cyclicGaussianBandMatrix_apply_of_mem
    (n : ℕ) (active : Finset (ZMod n)) (weight : ZMod n → ℝ)
    (gaussian : ZMod n → ZMod n → ℂ) (i j : ZMod n)
    (h : j - i ∈ active) :
    cyclicGaussianBandMatrix n active weight gaussian i j =
      (Real.sqrt (weight (j - i)) : ℂ) * gaussian i (j - i) := by
  simp [cyclicGaussianBandMatrix, h]

/-- The weight conditions called “normalized” in `CYCLIC5.1`.  Nonnegativity is stated
on the active set, since inactive weights never enter the matrix. -/
def IsNormalizedCyclicWeights {n : ℕ}
    (active : Finset (ZMod n)) (weight : ZMod n → ℝ) : Prop :=
  (∀ s ∈ active, 0 ≤ weight s) ∧ ∑ s ∈ active, weight s = 1

/-- Positive diagonal variance means that displacement zero is active and has positive
weight. -/
def HasPositiveDiagonalVariance {n : ℕ}
    (active : Finset (ZMod n)) (weight : ZMod n → ℝ) : Prop :=
  (0 : ZMod n) ∈ active ∧ 0 < weight 0

/-- The deterministic variance mass of one row. -/
def cyclicRowVarianceMass {n : ℕ}
    (active : Finset (ZMod n)) (weight : ZMod n → ℝ) : ℝ :=
  ∑ s ∈ active, weight s

/-- A normalized cyclic profile has row variance mass exactly one. -/
theorem cyclicRowVarianceMass_eq_one {n : ℕ}
    {active : Finset (ZMod n)} {weight : ZMod n → ℝ}
    (h : IsNormalizedCyclicWeights active weight) :
    cyclicRowVarianceMass active weight = 1 := by
  exact h.2

/-- Positive diagonal variance supplies both facts used in the Gaussian cofactor proof:
zero is active and its variance weight is nonzero. -/
theorem zero_mem_and_weight_ne_zero_of_positiveDiagonalVariance {n : ℕ}
    {active : Finset (ZMod n)} {weight : ZMod n → ℝ}
    (h : HasPositiveDiagonalVariance active weight) :
    (0 : ZMod n) ∈ active ∧ weight 0 ≠ 0 :=
  ⟨h.1, h.2.ne'⟩

end CircularLawSections56.Section6
