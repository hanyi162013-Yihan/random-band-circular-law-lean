import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Gaussian-profile sparse/dense closure

This file is the final scalar assembly of `thm:gaussian-profile`.  On the sparse branch,
the expected raw potential comes from the compact-core/tail squeeze and its fluctuation
comes from Gaussian row-resampling concentration.  On the dense branch, the cited dense
Gaussian comparison theorem is passed explicitly.  The replacement principle and
Hilbert--Schmidt tightness are likewise visible hypotheses of the last declaration.
-/

open Filter Topology

namespace CircularLawSections56.Section6

/-- Quantitative sparse/dense error closure for a fixed admissible spectral parameter.
The sparse mean and fluctuation errors are separated because only the former uses the
compact-core argument. -/
theorem gaussian_profile_logPotential_error_bound
    (sparseBranch : Prop)
    (logPotential meanPotential target sparseMeanError sparseFluctuationError
      denseComparisonError : ℝ)
    (hSparseMeanError : 0 ≤ sparseMeanError)
    (hSparseFluctuationError : 0 ≤ sparseFluctuationError)
    (hDenseComparisonError : 0 ≤ denseComparisonError)
    (hSparseMean : sparseBranch →
      |meanPotential - target| ≤ sparseMeanError)
    (hSparseFluctuation : sparseBranch →
      |logPotential - meanPotential| ≤ sparseFluctuationError)
    (hDense : ¬ sparseBranch →
      |logPotential - target| ≤ denseComparisonError) :
    |logPotential - target| ≤
      sparseMeanError + sparseFluctuationError + denseComparisonError := by
  by_cases h : sparseBranch
  · have hTriangle :
        |logPotential - target| ≤
          |logPotential - meanPotential| + |meanPotential - target| :=
      abs_sub_le _ _ _
    calc
      |logPotential - target| ≤
          |logPotential - meanPotential| + |meanPotential - target| := hTriangle
      _ ≤ sparseFluctuationError + sparseMeanError :=
        add_le_add (hSparseFluctuation h) (hSparseMean h)
      _ ≤ sparseMeanError + sparseFluctuationError + denseComparisonError := by
        rw [add_comm sparseFluctuationError sparseMeanError]
        exact le_add_of_nonneg_right hDenseComparisonError
  · calc
      |logPotential - target| ≤ denseComparisonError := hDense h
      _ ≤ sparseMeanError + sparseFluctuationError + denseComparisonError := by
        exact le_add_of_nonneg_left
          (add_nonneg hSparseMeanError hSparseFluctuationError)

/-- If the sparse mean, sparse fluctuation, and dense-comparison errors all vanish, the
raw logarithmic potential converges along the full sequence. -/
theorem gaussian_profile_logPotential_tendsto
    (sparseBranch : ℕ → Prop)
    (logPotential meanPotential : ℕ → ℝ) (target : ℝ)
    (sparseMeanError sparseFluctuationError denseComparisonError : ℕ → ℝ)
    (hSparseMeanError : ∀ n, 0 ≤ sparseMeanError n)
    (hSparseFluctuationError : ∀ n, 0 ≤ sparseFluctuationError n)
    (hDenseComparisonError : ∀ n, 0 ≤ denseComparisonError n)
    (hSparseMean : ∀ n, sparseBranch n →
      |meanPotential n - target| ≤ sparseMeanError n)
    (hSparseFluctuation : ∀ n, sparseBranch n →
      |logPotential n - meanPotential n| ≤ sparseFluctuationError n)
    (hDense : ∀ n, ¬ sparseBranch n →
      |logPotential n - target| ≤ denseComparisonError n)
    (hSparseMeanZero : Tendsto sparseMeanError atTop (𝓝 0))
    (hSparseFluctuationZero : Tendsto sparseFluctuationError atTop (𝓝 0))
    (hDenseComparisonZero : Tendsto denseComparisonError atTop (𝓝 0)) :
    Tendsto logPotential atTop (𝓝 target) := by
  have hTotalZero :
      Tendsto
        (fun n => sparseMeanError n + sparseFluctuationError n +
          denseComparisonError n)
        atTop (𝓝 0) := by
    simpa only [zero_add] using
      (hSparseMeanZero.add hSparseFluctuationZero).add hDenseComparisonZero
  have hAbs : Tendsto (fun n => |logPotential n - target|) atTop (𝓝 0) :=
    squeeze_zero
      (fun n => abs_nonneg (logPotential n - target))
      (fun n => gaussian_profile_logPotential_error_bound
        (sparseBranch n) (logPotential n) (meanPotential n) target
        (sparseMeanError n) (sparseFluctuationError n) (denseComparisonError n)
        (hSparseMeanError n) (hSparseFluctuationError n)
        (hDenseComparisonError n) (hSparseMean n) (hSparseFluctuation n)
        (hDense n))
      hTotalZero
  exact tendsto_iff_dist_tendsto_zero.2 (by
    simpa [Real.dist_eq] using hAbs)

/-- Replacement-principle closure for `thm:gaussian-profile`.

`hReplacement` is an ordinary theorem argument representing the cited replacement
principle at the level appropriate to the caller (normally simultaneously for a.e.
spectral parameter).  `hsTightness` is supplied separately, so neither external input is
hidden in a custom axiom. -/
theorem gaussian_profile_circularLaw_of_replacement
    (sparseBranch : ℕ → Prop)
    (logPotential meanPotential : ℕ → ℝ) (target : ℝ)
    (sparseMeanError sparseFluctuationError denseComparisonError : ℕ → ℝ)
    (HSTightness CircularLawConclusion : Prop)
    (hSparseMeanError : ∀ n, 0 ≤ sparseMeanError n)
    (hSparseFluctuationError : ∀ n, 0 ≤ sparseFluctuationError n)
    (hDenseComparisonError : ∀ n, 0 ≤ denseComparisonError n)
    (hSparseMean : ∀ n, sparseBranch n →
      |meanPotential n - target| ≤ sparseMeanError n)
    (hSparseFluctuation : ∀ n, sparseBranch n →
      |logPotential n - meanPotential n| ≤ sparseFluctuationError n)
    (hDense : ∀ n, ¬ sparseBranch n →
      |logPotential n - target| ≤ denseComparisonError n)
    (hSparseMeanZero : Tendsto sparseMeanError atTop (𝓝 0))
    (hSparseFluctuationZero : Tendsto sparseFluctuationError atTop (𝓝 0))
    (hDenseComparisonZero : Tendsto denseComparisonError atTop (𝓝 0))
    (hsTightness : HSTightness)
    (hReplacement :
      Tendsto logPotential atTop (𝓝 target) →
        HSTightness → CircularLawConclusion) :
    CircularLawConclusion := by
  apply hReplacement
  · exact gaussian_profile_logPotential_tendsto sparseBranch logPotential meanPotential
      target sparseMeanError sparseFluctuationError denseComparisonError
      hSparseMeanError hSparseFluctuationError hDenseComparisonError
      hSparseMean hSparseFluctuation hDense
      hSparseMeanZero hSparseFluctuationZero hDenseComparisonZero
  · exact hsTightness

/-- Concrete Hilbert--Schmidt version of the final replacement closure.  This is the
preferred paper-facing wrapper: tightness is represented by a uniform normalized
expected Hilbert--Schmidt-square bound, not by an opaque proposition. -/
theorem gaussian_profile_circularLaw_of_uniform_hs_bound
    {CircularLawConclusion : Prop}
    (sparseBranch : ℕ → Prop)
    (logPotential meanPotential normalizedExpectedHSSquare : ℕ → ℝ)
    (target : ℝ)
    (sparseMeanError sparseFluctuationError denseComparisonError : ℕ → ℝ)
    (hSparseMeanError : ∀ n, 0 ≤ sparseMeanError n)
    (hSparseFluctuationError : ∀ n, 0 ≤ sparseFluctuationError n)
    (hDenseComparisonError : ∀ n, 0 ≤ denseComparisonError n)
    (hSparseMean : ∀ n, sparseBranch n →
      |meanPotential n - target| ≤ sparseMeanError n)
    (hSparseFluctuation : ∀ n, sparseBranch n →
      |logPotential n - meanPotential n| ≤ sparseFluctuationError n)
    (hDense : ∀ n, ¬ sparseBranch n →
      |logPotential n - target| ≤ denseComparisonError n)
    (hSparseMeanZero : Tendsto sparseMeanError atTop (𝓝 0))
    (hSparseFluctuationZero : Tendsto sparseFluctuationError atTop (𝓝 0))
    (hDenseComparisonZero : Tendsto denseComparisonError atTop (𝓝 0))
    (hHSTightness :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n, normalizedExpectedHSSquare n ≤ C)
    (hReplacement :
      Tendsto logPotential atTop (𝓝 target) →
        (∃ C : ℝ, 0 ≤ C ∧
          ∀ n, normalizedExpectedHSSquare n ≤ C) →
        CircularLawConclusion) :
    CircularLawConclusion := by
  exact gaussian_profile_circularLaw_of_replacement
    sparseBranch logPotential meanPotential target
    sparseMeanError sparseFluctuationError denseComparisonError
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n, normalizedExpectedHSSquare n ≤ C)
    CircularLawConclusion
    hSparseMeanError hSparseFluctuationError hDenseComparisonError
    hSparseMean hSparseFluctuation hDense
    hSparseMeanZero hSparseFluctuationZero hDenseComparisonZero
    hHSTightness hReplacement

end CircularLawSections56.Section6
