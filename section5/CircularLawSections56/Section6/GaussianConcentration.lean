import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Ring

/-!
# Scalar Efron--Stein aggregation for Gaussian log determinants

This file contains only the finite-sum and scalar-convergence layer of
`lem:compact-Gaussian-concentration` in Section 6.  In the intended application:

* the Efron--Stein hypothesis is supplied by the row-resampling theorem from Section 4;
* the uniform row-cost hypothesis packages the complex Gaussian affine-log second-moment
  estimate and cofactor nonvanishing; and
* the final variance-to-probability implication is supplied as an ordinary Chebyshev or
  convergence-in-probability theorem hypothesis.

No Gaussian measure, determinant polynomial, or external random-matrix input is postulated
inside this module.
-/

open Filter Topology
open scoped BigOperators

namespace CircularLawSections56.Section6

/-- The logarithmic scale `log(e n)` appearing in the Gaussian row-resampling estimate.
At the totalized boundary `n = 0` this equals `Real.log 0 = 0`; every normalized-variance
application below explicitly assumes `0 < n`. -/
noncomputable def gaussianLogScale (n : ℕ) : ℝ :=
  Real.log (Real.exp 1 * (n : ℝ))

/-- Scalar finite-sum form of Efron--Stein aggregation.

If variance is at most half the sum of the row-resampling costs and every one of the `n`
row costs is at most `rowBound`, then variance is at most
`(1/2) * n * rowBound`.  The row costs and variance are allowed to be arbitrary real
numbers; their probabilistic nonnegativity is not needed for this order calculation. -/
theorem efronStein_variance_le_of_uniform_row_cost
    (n : ℕ) (variance rowBound : ℝ) (rowResampleCost : ℕ → ℝ)
    (hEfronStein :
      variance ≤ (1 / 2 : ℝ) *
        ∑ i ∈ Finset.range n, rowResampleCost i)
    (hRowCost : ∀ i < n, rowResampleCost i ≤ rowBound) :
    variance ≤ (1 / 2 : ℝ) * (n : ℝ) * rowBound := by
  have hSum :
      (∑ i ∈ Finset.range n, rowResampleCost i) ≤
        ∑ _i ∈ Finset.range n, rowBound := by
    apply Finset.sum_le_sum
    intro i hi
    exact hRowCost i (Finset.mem_range.mp hi)
  calc
    variance ≤ (1 / 2 : ℝ) *
        ∑ i ∈ Finset.range n, rowResampleCost i := hEfronStein
    _ ≤ (1 / 2 : ℝ) * ∑ _i ∈ Finset.range n, rowBound :=
      mul_le_mul_of_nonneg_left hSum (by
        exact div_nonneg zero_le_one zero_le_two)
    _ = (1 / 2 : ℝ) * (n : ℝ) * rowBound := by simp [mul_assoc]

/-- The Section 6 Gaussian specialization of the scalar Efron--Stein sum.

The hypothesis `hRowCost` is precisely the point where the one-row affine Gaussian
logarithmic estimate and cofactor nonvanishing enter.  Together with the ordinary
Efron--Stein hypothesis, the row bound `4 K log(e n)^2` gives
`2 n K log(e n)^2`. -/
theorem gaussian_logdet_variance_le
    (n : ℕ) (variance K : ℝ) (rowResampleCost : ℕ → ℝ)
    (hEfronStein :
      variance ≤ (1 / 2 : ℝ) *
        ∑ i ∈ Finset.range n, rowResampleCost i)
    (hRowCost : ∀ i < n,
      rowResampleCost i ≤ 4 * K * (gaussianLogScale n) ^ 2) :
    variance ≤ 2 * (n : ℝ) * K * (gaussianLogScale n) ^ 2 := by
  have hAggregate := efronStein_variance_le_of_uniform_row_cost
    n variance (4 * K * (gaussianLogScale n) ^ 2) rowResampleCost
    hEfronStein hRowCost
  calc
    variance ≤ (1 / 2 : ℝ) * (n : ℝ) *
        (4 * K * (gaussianLogScale n) ^ 2) := hAggregate
    _ = 2 * (n : ℝ) * K * (gaussianLogScale n) ^ 2 := by ring

/-- Explicit normalized-variance estimate.

After division by `n^2`, the Gaussian Efron--Stein bound is
`2 K log(e n)^2 / n`.  Positivity of `n` is used only to cancel the normalizing factor. -/
theorem gaussian_logdet_normalized_variance_le
    (n : ℕ) (variance K : ℝ) (rowResampleCost : ℕ → ℝ)
    (hn : 0 < n)
    (hEfronStein :
      variance ≤ (1 / 2 : ℝ) *
        ∑ i ∈ Finset.range n, rowResampleCost i)
    (hRowCost : ∀ i < n,
      rowResampleCost i ≤ 4 * K * (gaussianLogScale n) ^ 2) :
    variance / (n : ℝ) ^ 2 ≤
      (2 * K * (gaussianLogScale n) ^ 2) / (n : ℝ) := by
  have hnReal : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnSq : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnReal
  have hVariance := gaussian_logdet_variance_le
    n variance K rowResampleCost hEfronStein hRowCost
  calc
    variance / (n : ℝ) ^ 2 ≤
        (2 * (n : ℝ) * K * (gaussianLogScale n) ^ 2) /
          (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hVariance hnSq.le
    _ = (2 * K * (gaussianLogScale n) ^ 2) / (n : ℝ) := by
      field_simp

/-- Squeeze a normalized variance to zero through an explicit deterministic upper bound. -/
theorem normalized_variance_tendsto_zero_of_bound
    (normalizedVariance varianceBound : ℕ → ℝ)
    (hVarianceNonneg : ∀ n, 0 ≤ normalizedVariance n)
    (hVarianceBound : ∀ n, normalizedVariance n ≤ varianceBound n)
    (hBoundZero : Tendsto varianceBound atTop (𝓝 0)) :
    Tendsto normalizedVariance atTop (𝓝 0) :=
  squeeze_zero hVarianceNonneg hVarianceBound hBoundZero

/-- Small wrapper from the scalar variance estimate to concentration.

`hVarianceToProbability` is an explicit external Chebyshev or
variance-to-convergence-in-probability theorem.  Its conclusion is represented here by a
sequence of fixed-threshold deviation probabilities tending to zero; a project-specific
`TendstoInMeasure` wrapper can be passed in the same way. -/
theorem deviation_probability_tendsto_zero_of_variance_to_probability
    (normalizedVariance varianceBound deviationProbability : ℕ → ℝ)
    (hVarianceNonneg : ∀ n, 0 ≤ normalizedVariance n)
    (hVarianceBound : ∀ n, normalizedVariance n ≤ varianceBound n)
    (hBoundZero : Tendsto varianceBound atTop (𝓝 0))
    (hVarianceToProbability :
      Tendsto normalizedVariance atTop (𝓝 0) →
        Tendsto deviationProbability atTop (𝓝 0)) :
    Tendsto deviationProbability atTop (𝓝 0) :=
  hVarianceToProbability
    (normalized_variance_tendsto_zero_of_bound
      normalizedVariance varianceBound hVarianceNonneg hVarianceBound hBoundZero)

end CircularLawSections56.Section6
