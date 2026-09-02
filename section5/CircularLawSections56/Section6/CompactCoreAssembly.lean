import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Compact Gaussian core: branchwise assembly

This file formalizes the logical assembly of `prop:compact-gaussian-core`.  The two
regimes in the manuscript deliberately enter as ordinary hypotheses:

* on the direct high-band branch, the raw logarithmic anchor is a **Section 3 input** and
  the deterministic-centering estimate comes from Gaussian concentration;
* on the long branch, the raw expectation estimate is the strengthened `L¹` interface
  exported by Section 5 (and hence uses Section 4 transitively);
* for the fixed-cutoff potential, the direct comparison theorem and the long-branch
  block-periodicization theorem are external inputs.

The declarations below contain no probability-space fiction for a triangular array.
They consume the resulting scalar deterministic errors and prove the branchwise and
asymptotic closures.
-/

open Filter Topology

namespace CircularLawSections56.Section6

/-- A two-regime error estimate.  Exactly one proof is used at each index, while the
conclusion keeps both nonnegative error budgets so no maximum operation is required. -/
theorem branchwise_error_bound
    (directBranch : Prop) (value target directError longError : ℝ)
    (hDirectError : 0 ≤ directError) (hLongError : 0 ≤ longError)
    (hDirect : directBranch → |value - target| ≤ directError)
    (hLong : ¬ directBranch → |value - target| ≤ longError) :
    |value - target| ≤ directError + longError := by
  by_cases h : directBranch
  · exact (hDirect h).trans (le_add_of_nonneg_right hLongError)
  · exact (hLong h).trans (le_add_of_nonneg_left hDirectError)

/-- If both branch error budgets vanish, a sequence assembled from the two regimes has
the common deterministic limit. -/
theorem branchwise_tendsto
    (directBranch : ℕ → Prop) (value : ℕ → ℝ) (target : ℝ)
    (directError longError : ℕ → ℝ)
    (hDirectError : ∀ n, 0 ≤ directError n)
    (hLongError : ∀ n, 0 ≤ longError n)
    (hDirect : ∀ n, directBranch n →
      |value n - target| ≤ directError n)
    (hLong : ∀ n, ¬ directBranch n →
      |value n - target| ≤ longError n)
    (hDirectZero : Tendsto directError atTop (𝓝 0))
    (hLongZero : Tendsto longError atTop (𝓝 0)) :
    Tendsto value atTop (𝓝 target) := by
  have hTotalZero :
      Tendsto (fun n => directError n + longError n) atTop (𝓝 0) := by
    simpa only [zero_add] using hDirectZero.add hLongZero
  have hAbs : Tendsto (fun n => |value n - target|) atTop (𝓝 0) :=
    squeeze_zero
      (fun n => abs_nonneg (value n - target))
      (fun n => branchwise_error_bound
        (directBranch n) (value n) target (directError n) (longError n)
        (hDirectError n) (hLongError n) (hDirect n) (hLong n))
      hTotalZero
  exact tendsto_iff_dist_tendsto_zero.2 (by
    simpa [Real.dist_eq] using hAbs)

/-- Raw-expectation half of `prop:compact-gaussian-core`.

`section3AnchorError` is the explicitly supplied high-band anchor error requested for
reuse from Section 3.  `directCenteringError` is supplied by the compact Gaussian
concentration lemma; at the probability level,
`deterministic_center_tendsto_of_section3_anchor` proves the corresponding centering
bridge before this scalar error form is used.  `section5LongError` is the long-branch
expectation-strength interface assembled from Sections 4--5. -/
theorem compactCore_raw_expectation_tendsto
    (directHighBand : ℕ → Prop) (rawExpectation : ℕ → ℝ) (target : ℝ)
    (section3AnchorError directCenteringError section5LongError : ℕ → ℝ)
    (hSection3AnchorError : ∀ n, 0 ≤ section3AnchorError n)
    (hDirectCenteringError : ∀ n, 0 ≤ directCenteringError n)
    (hSection5LongError : ∀ n, 0 ≤ section5LongError n)
    (hDirect : ∀ n, directHighBand n →
      |rawExpectation n - target| ≤
        section3AnchorError n + directCenteringError n)
    (hLong : ∀ n, ¬ directHighBand n →
      |rawExpectation n - target| ≤ section5LongError n)
    (hSection3AnchorZero : Tendsto section3AnchorError atTop (𝓝 0))
    (hDirectCenteringZero : Tendsto directCenteringError atTop (𝓝 0))
    (hSection5LongZero : Tendsto section5LongError atTop (𝓝 0)) :
    Tendsto rawExpectation atTop (𝓝 target) := by
  apply branchwise_tendsto directHighBand rawExpectation target
    (fun n => section3AnchorError n + directCenteringError n)
    section5LongError
  · intro n
    exact add_nonneg (hSection3AnchorError n) (hDirectCenteringError n)
  · exact hSection5LongError
  · exact hDirect
  · exact hLong
  · simpa only [zero_add] using hSection3AnchorZero.add hDirectCenteringZero
  · exact hSection5LongZero

/-- Fixed-cutoff half of `prop:compact-gaussian-core`.  The direct error represents the
cited high-band squared-singular-value comparison; the long error represents block
periodicization, Mirsky stability, and the same comparison applied uniformly to blocks. -/
theorem compactCore_cutoff_expectation_tendsto
    (directHighBand : ℕ → Prop) (cutoffExpectation : ℕ → ℝ) (target : ℝ)
    (directComparisonError longPeriodicizationError : ℕ → ℝ)
    (hDirectError : ∀ n, 0 ≤ directComparisonError n)
    (hLongError : ∀ n, 0 ≤ longPeriodicizationError n)
    (hDirect : ∀ n, directHighBand n →
      |cutoffExpectation n - target| ≤ directComparisonError n)
    (hLong : ∀ n, ¬ directHighBand n →
      |cutoffExpectation n - target| ≤ longPeriodicizationError n)
    (hDirectZero : Tendsto directComparisonError atTop (𝓝 0))
    (hLongZero : Tendsto longPeriodicizationError atTop (𝓝 0)) :
    Tendsto cutoffExpectation atTop (𝓝 target) :=
  branchwise_tendsto directHighBand cutoffExpectation target
    directComparisonError longPeriodicizationError hDirectError hLongError
    hDirect hLong hDirectZero hLongZero

/-- Scalar main-chain form of `prop:compact-gaussian-core`: the raw and fixed-cutoff
expectations converge simultaneously once their explicitly named branch inputs are
provided. -/
theorem compact_gaussian_core
    (directHighBand : ℕ → Prop)
    (rawExpectation cutoffExpectation : ℕ → ℝ)
    (rawTarget cutoffTarget : ℝ)
    (section3AnchorError directCenteringError section5LongError : ℕ → ℝ)
    (directComparisonError longPeriodicizationError : ℕ → ℝ)
    (hSection3AnchorError : ∀ n, 0 ≤ section3AnchorError n)
    (hDirectCenteringError : ∀ n, 0 ≤ directCenteringError n)
    (hSection5LongError : ∀ n, 0 ≤ section5LongError n)
    (hDirectComparisonError : ∀ n, 0 ≤ directComparisonError n)
    (hLongPeriodicizationError : ∀ n, 0 ≤ longPeriodicizationError n)
    (hRawDirect : ∀ n, directHighBand n →
      |rawExpectation n - rawTarget| ≤
        section3AnchorError n + directCenteringError n)
    (hRawLong : ∀ n, ¬ directHighBand n →
      |rawExpectation n - rawTarget| ≤ section5LongError n)
    (hCutoffDirect : ∀ n, directHighBand n →
      |cutoffExpectation n - cutoffTarget| ≤ directComparisonError n)
    (hCutoffLong : ∀ n, ¬ directHighBand n →
      |cutoffExpectation n - cutoffTarget| ≤ longPeriodicizationError n)
    (hSection3AnchorZero : Tendsto section3AnchorError atTop (𝓝 0))
    (hDirectCenteringZero : Tendsto directCenteringError atTop (𝓝 0))
    (hSection5LongZero : Tendsto section5LongError atTop (𝓝 0))
    (hDirectComparisonZero : Tendsto directComparisonError atTop (𝓝 0))
    (hLongPeriodicizationZero : Tendsto longPeriodicizationError atTop (𝓝 0)) :
    Tendsto rawExpectation atTop (𝓝 rawTarget) ∧
      Tendsto cutoffExpectation atTop (𝓝 cutoffTarget) := by
  constructor
  · exact compactCore_raw_expectation_tendsto directHighBand rawExpectation rawTarget
      section3AnchorError directCenteringError section5LongError
      hSection3AnchorError hDirectCenteringError hSection5LongError
      hRawDirect hRawLong hSection3AnchorZero hDirectCenteringZero hSection5LongZero
  · exact compactCore_cutoff_expectation_tendsto directHighBand cutoffExpectation
      cutoffTarget directComparisonError longPeriodicizationError
      hDirectComparisonError hLongPeriodicizationError hCutoffDirect hCutoffLong
      hDirectComparisonZero hLongPeriodicizationZero

end CircularLawSections56.Section6
