import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Pressure-to-target closure

This file isolates the final deterministic comparison in
`eq:target-mean-pressure` of Section 5.  The complete balanced cells occupy a fraction
`cellLengthRatio` of the full strip.  Thus their normalized pressure is first multiplied by
that ratio before it is compared with the full-strip normalization.

The proof keeps the three errors separate:

1. the terminal-remainder error between the full strip and the complete cells;
2. the error of the complete-cell normalized pressure from the target; and
3. the error of the complete-cell length ratio from one.

All probabilistic, pressure-lifting, and balanced-division inputs are ordinary real
inequality hypotheses here.
-/

open Filter Topology

namespace CircularLawSections56.Section5

/-- Quantitative pressure-to-target comparison for one set of parameters.

`wholeNormalizedPressure` is the pressure divided by the ambient strip length.
`cellNormalizedPressure` is the complete balanced-cell pressure divided by the total
length of those cells, and `cellLengthRatio` is complete-cell length divided by ambient
length.  Since balanced cells lie inside the strip, the ratio belongs to `[0,1]`.

The conclusion is the exact three-error estimate used to close
`eq:target-mean-pressure`. -/
theorem target_pressure_error_bound
    (wholeNormalizedPressure cellNormalizedPressure cellLengthRatio target
      remainderError cellPressureError lengthRatioError : ℝ)
    (hRatioNonneg : 0 ≤ cellLengthRatio)
    (hRatioLeOne : cellLengthRatio ≤ 1)
    (hRemainder :
      |wholeNormalizedPressure -
          cellLengthRatio * cellNormalizedPressure| ≤ remainderError)
    (hCellPressure :
      |cellNormalizedPressure - target| ≤ cellPressureError)
    (hLengthRatio : |cellLengthRatio - 1| ≤ lengthRatioError) :
    |wholeNormalizedPressure - target| ≤
      remainderError + cellPressureError + lengthRatioError * |target| := by
  have hCellErrorNonneg : 0 ≤ cellPressureError :=
    (abs_nonneg (cellNormalizedPressure - target)).trans hCellPressure
  have hScaledCell :
      |cellLengthRatio * cellNormalizedPressure -
          cellLengthRatio * target| ≤ cellPressureError := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hRatioNonneg]
    calc
      cellLengthRatio * |cellNormalizedPressure - target| ≤
          cellLengthRatio * cellPressureError :=
        mul_le_mul_of_nonneg_left hCellPressure hRatioNonneg
      _ ≤ 1 * cellPressureError :=
        mul_le_mul_of_nonneg_right hRatioLeOne hCellErrorNonneg
      _ = cellPressureError := one_mul _
  have hRatioIdentity :
      |cellLengthRatio * target - target| =
        |cellLengthRatio - 1| * |target| := by
    calc
      |cellLengthRatio * target - target| =
          |cellLengthRatio * target - 1 * target| := by rw [one_mul]
      _ = |(cellLengthRatio - 1) * target| := by rw [sub_mul]
      _ = |cellLengthRatio - 1| * |target| := abs_mul _ _
  have hScaledRatio :
      |cellLengthRatio * target - target| ≤ lengthRatioError * |target| := by
    rw [hRatioIdentity]
    exact mul_le_mul_of_nonneg_right hLengthRatio (abs_nonneg target)
  calc
    |wholeNormalizedPressure - target| ≤
        |wholeNormalizedPressure -
            cellLengthRatio * cellNormalizedPressure| +
          |cellLengthRatio * cellNormalizedPressure - target| :=
      abs_sub_le _ _ _
    _ ≤ |wholeNormalizedPressure -
            cellLengthRatio * cellNormalizedPressure| +
          (|cellLengthRatio * cellNormalizedPressure -
              cellLengthRatio * target| +
            |cellLengthRatio * target - target|) :=
      add_le_add (le_refl _) (abs_sub_le _ _ _)
    _ ≤ remainderError +
          (cellPressureError + lengthRatioError * |target|) :=
      add_le_add hRemainder (add_le_add hScaledCell hScaledRatio)
    _ = remainderError + cellPressureError + lengthRatioError * |target| :=
      (add_assoc _ _ _).symm

/-- Asymptotic closure of `target_pressure_error_bound`.

The three scalar errors may come from different probability spaces or triangular-array
estimates: only their deterministic bounds and convergence to zero are needed. -/
theorem target_pressure_tendsto
    (wholeNormalizedPressure cellNormalizedPressure cellLengthRatio : ℕ → ℝ)
    (target : ℝ)
    (remainderError cellPressureError lengthRatioError : ℕ → ℝ)
    (hRatioNonneg : ∀ n, 0 ≤ cellLengthRatio n)
    (hRatioLeOne : ∀ n, cellLengthRatio n ≤ 1)
    (hRemainder : ∀ n,
      |wholeNormalizedPressure n -
          cellLengthRatio n * cellNormalizedPressure n| ≤ remainderError n)
    (hCellPressure : ∀ n,
      |cellNormalizedPressure n - target| ≤ cellPressureError n)
    (hLengthRatio : ∀ n,
      |cellLengthRatio n - 1| ≤ lengthRatioError n)
    (hRemainderZero : Tendsto remainderError atTop (𝓝 0))
    (hCellPressureZero : Tendsto cellPressureError atTop (𝓝 0))
    (hLengthRatioZero : Tendsto lengthRatioError atTop (𝓝 0)) :
    Tendsto wholeNormalizedPressure atTop (𝓝 target) := by
  have hScaledRatioZero :
      Tendsto (fun n => lengthRatioError n * |target|) atTop (𝓝 0) := by
    simpa only [zero_mul] using hLengthRatioZero.mul tendsto_const_nhds
  have hTotalErrorZero :
      Tendsto
        (fun n => remainderError n + cellPressureError n +
          lengthRatioError n * |target|)
        atTop (𝓝 0) := by
    simpa only [zero_add] using
      (hRemainderZero.add hCellPressureZero).add hScaledRatioZero
  have hAbs :
      Tendsto (fun n => |wholeNormalizedPressure n - target|) atTop (𝓝 0) :=
    squeeze_zero
      (fun n => abs_nonneg (wholeNormalizedPressure n - target))
      (fun n => target_pressure_error_bound
        (wholeNormalizedPressure n) (cellNormalizedPressure n)
        (cellLengthRatio n) target (remainderError n)
        (cellPressureError n) (lengthRatioError n)
        (hRatioNonneg n) (hRatioLeOne n) (hRemainder n)
        (hCellPressure n) (hLengthRatio n))
      hTotalErrorZero
  exact tendsto_iff_dist_tendsto_zero.2 (by
    simpa [Real.dist_eq] using hAbs)

end CircularLawSections56.Section5
