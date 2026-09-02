import CircularLawSections56.Section5.PressureLifting
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Asymptotic pressure lifting on complete cell multiples

This file turns the exact finite estimate `max_pressure_lift` into the sequence-level
statement `eq:global-pressure-multiples`.  The only asymptotic input is the visibly stated
vanishing normalized cell error.
-/

open Filter Topology

namespace CircularLawSections56.Section5

variable {ι : Type*}

/-- If the normalized per-cell lifting error tends to zero, the lifted and one-cell
maximal pressures have the same asymptotic normalization. -/
theorem max_pressure_lift_difference_tendsto_zero
    (degrees : Finset ι) (hdegrees : degrees.Nonempty)
    (base lifted : ℕ → ι → ℝ) (q m : ℕ → ℕ) (cellError : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hm : ∀ n, 0 < m n)
    (hdegree : ∀ n r, r ∈ degrees →
      (q n : ℝ) * (base n r - cellError n) ≤ lifted n r ∧
        lifted n r ≤ (q n : ℝ) * (base n r + cellError n))
    (hErrorZero :
      Tendsto (fun n => cellError n / (m n : ℝ)) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        finiteSignedMax degrees hdegrees (lifted n) /
            ((q n : ℝ) * (m n : ℝ)) -
          finiteSignedMax degrees hdegrees (base n) / (m n : ℝ))
      atTop (𝓝 0) := by
  let difference : ℕ → ℝ := fun n =>
    finiteSignedMax degrees hdegrees (lifted n) /
        ((q n : ℝ) * (m n : ℝ)) -
      finiteSignedMax degrees hdegrees (base n) / (m n : ℝ)
  have hAbs : Tendsto (fun n => |difference n|) atTop (𝓝 0) :=
    squeeze_zero
      (fun n => abs_nonneg (difference n))
      (fun n => max_pressure_lift hdegrees (base n) (lifted n)
        (q n) (m n) (cellError n) (hq n) (hm n) (hdegree n))
      hErrorZero
  have hDifference : Tendsto difference atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.2 (by
      simpa [Real.dist_eq] using hAbs)
  exact hDifference

/-- Paper equation `eq:global-pressure-multiples` in sequence form.

Mesoscopic calibration supplies `hBaseTarget`; the caller supplies the displayed
degreewise comparison and `max_pressure_lift` promotes it to the finite maximum; the
normalized projective/fresh-cell loss is exactly `hErrorZero`. -/
theorem global_pressure_on_cell_multiples
    (degrees : Finset ι) (hdegrees : degrees.Nonempty)
    (base lifted : ℕ → ι → ℝ) (q m : ℕ → ℕ) (cellError : ℕ → ℝ)
    (target : ℝ)
    (hq : ∀ n, 0 < q n) (hm : ∀ n, 0 < m n)
    (hdegree : ∀ n r, r ∈ degrees →
      (q n : ℝ) * (base n r - cellError n) ≤ lifted n r ∧
        lifted n r ≤ (q n : ℝ) * (base n r + cellError n))
    (hErrorZero :
      Tendsto (fun n => cellError n / (m n : ℝ)) atTop (𝓝 0))
    (hBaseTarget :
      Tendsto
        (fun n => finiteSignedMax degrees hdegrees (base n) / (m n : ℝ))
        atTop (𝓝 target)) :
    Tendsto
      (fun n => finiteSignedMax degrees hdegrees (lifted n) /
        ((q n : ℝ) * (m n : ℝ)))
      atTop (𝓝 target) := by
  have hDifference := max_pressure_lift_difference_tendsto_zero
    degrees hdegrees base lifted q m cellError hq hm hdegree hErrorZero
  have hSum := hDifference.add hBaseTarget
  simpa only [sub_add_cancel, zero_add] using hSum

/-- Varying-degree version of `max_pressure_lift_difference_tendsto_zero`.

In the manuscript the exterior-degree set is `{0, ..., 2 Wₙ}` and therefore changes
with `n`.  This statement keeps that dependence explicit instead of silently replacing
it by one fixed finite set. -/
theorem max_pressure_lift_difference_tendsto_zero_varyingDegrees
    (degrees : ℕ → Finset ι) (hdegrees : ∀ n, (degrees n).Nonempty)
    (base lifted : ℕ → ι → ℝ) (q m : ℕ → ℕ) (cellError : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hm : ∀ n, 0 < m n)
    (hdegree : ∀ n r, r ∈ degrees n →
      (q n : ℝ) * (base n r - cellError n) ≤ lifted n r ∧
        lifted n r ≤ (q n : ℝ) * (base n r + cellError n))
    (hErrorZero :
      Tendsto (fun n => cellError n / (m n : ℝ)) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        finiteSignedMax (degrees n) (hdegrees n) (lifted n) /
            ((q n : ℝ) * (m n : ℝ)) -
          finiteSignedMax (degrees n) (hdegrees n) (base n) / (m n : ℝ))
      atTop (𝓝 0) := by
  let difference : ℕ → ℝ := fun n =>
    finiteSignedMax (degrees n) (hdegrees n) (lifted n) /
        ((q n : ℝ) * (m n : ℝ)) -
      finiteSignedMax (degrees n) (hdegrees n) (base n) / (m n : ℝ)
  have hAbs : Tendsto (fun n => |difference n|) atTop (𝓝 0) :=
    squeeze_zero
      (fun n => abs_nonneg (difference n))
      (fun n => max_pressure_lift (hdegrees n) (base n) (lifted n)
        (q n) (m n) (cellError n) (hq n) (hm n) (hdegree n))
      hErrorZero
  exact tendsto_iff_dist_tendsto_zero.2 (by
    simpa [Real.dist_eq] using hAbs)

/-- Paper equation `eq:global-pressure-multiples` with the literal varying set of
exterior degrees. -/
theorem global_pressure_on_cell_multiples_varyingDegrees
    (degrees : ℕ → Finset ι) (hdegrees : ∀ n, (degrees n).Nonempty)
    (base lifted : ℕ → ι → ℝ) (q m : ℕ → ℕ) (cellError : ℕ → ℝ)
    (target : ℝ)
    (hq : ∀ n, 0 < q n) (hm : ∀ n, 0 < m n)
    (hdegree : ∀ n r, r ∈ degrees n →
      (q n : ℝ) * (base n r - cellError n) ≤ lifted n r ∧
        lifted n r ≤ (q n : ℝ) * (base n r + cellError n))
    (hErrorZero :
      Tendsto (fun n => cellError n / (m n : ℝ)) atTop (𝓝 0))
    (hBaseTarget :
      Tendsto
        (fun n => finiteSignedMax (degrees n) (hdegrees n) (base n) / (m n : ℝ))
        atTop (𝓝 target)) :
    Tendsto
      (fun n => finiteSignedMax (degrees n) (hdegrees n) (lifted n) /
        ((q n : ℝ) * (m n : ℝ)))
      atTop (𝓝 target) := by
  have hDifference := max_pressure_lift_difference_tendsto_zero_varyingDegrees
    degrees hdegrees base lifted q m cellError hq hm hdegree hErrorZero
  have hSum := hDifference.add hBaseTarget
  simpa only [sub_add_cancel, zero_add] using hSum

/-- Eventual-hypothesis version of the varying-degree lift.  This is the convenient
interface for floor-based cell counts, which may vanish on a finite prefix. -/
theorem max_pressure_lift_difference_tendsto_zero_varyingDegrees_eventually
    (degrees : ℕ → Finset ι) (hdegrees : ∀ n, (degrees n).Nonempty)
    (base lifted : ℕ → ι → ℝ) (q m : ℕ → ℕ) (cellError : ℕ → ℝ)
    (hLifting : ∀ᶠ n in atTop,
      0 < q n ∧ 0 < m n ∧ ∀ r, r ∈ degrees n →
        (q n : ℝ) * (base n r - cellError n) ≤ lifted n r ∧
          lifted n r ≤ (q n : ℝ) * (base n r + cellError n))
    (hErrorZero :
      Tendsto (fun n => cellError n / (m n : ℝ)) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        finiteSignedMax (degrees n) (hdegrees n) (lifted n) /
            ((q n : ℝ) * (m n : ℝ)) -
          finiteSignedMax (degrees n) (hdegrees n) (base n) / (m n : ℝ))
      atTop (𝓝 0) := by
  let difference : ℕ → ℝ := fun n =>
    finiteSignedMax (degrees n) (hdegrees n) (lifted n) /
        ((q n : ℝ) * (m n : ℝ)) -
      finiteSignedMax (degrees n) (hdegrees n) (base n) / (m n : ℝ)
  have hAbs : Tendsto (fun n => |difference n|) atTop (𝓝 0) := by
    apply squeeze_zero'
      (g := fun n => cellError n / (m n : ℝ))
    · exact Filter.Eventually.of_forall fun n => abs_nonneg (difference n)
    · filter_upwards [hLifting] with n hn
      exact max_pressure_lift (hdegrees n) (base n) (lifted n)
        (q n) (m n) (cellError n) hn.1 hn.2.1 hn.2.2
    · exact hErrorZero
  exact tendsto_iff_dist_tendsto_zero.2 (by
    simpa [Real.dist_eq] using hAbs)

/-- Eventual-hypothesis form of `eq:global-pressure-multiples` with a varying degree
set.  No artificial positivity or degreewise estimate is required on a finite prefix. -/
theorem global_pressure_on_cell_multiples_varyingDegrees_eventually
    (degrees : ℕ → Finset ι) (hdegrees : ∀ n, (degrees n).Nonempty)
    (base lifted : ℕ → ι → ℝ) (q m : ℕ → ℕ) (cellError : ℕ → ℝ)
    (target : ℝ)
    (hLifting : ∀ᶠ n in atTop,
      0 < q n ∧ 0 < m n ∧ ∀ r, r ∈ degrees n →
        (q n : ℝ) * (base n r - cellError n) ≤ lifted n r ∧
          lifted n r ≤ (q n : ℝ) * (base n r + cellError n))
    (hErrorZero :
      Tendsto (fun n => cellError n / (m n : ℝ)) atTop (𝓝 0))
    (hBaseTarget :
      Tendsto
        (fun n => finiteSignedMax (degrees n) (hdegrees n) (base n) / (m n : ℝ))
        atTop (𝓝 target)) :
    Tendsto
      (fun n => finiteSignedMax (degrees n) (hdegrees n) (lifted n) /
        ((q n : ℝ) * (m n : ℝ)))
      atTop (𝓝 target) := by
  have hDifference :=
    max_pressure_lift_difference_tendsto_zero_varyingDegrees_eventually
      degrees hdegrees base lifted q m cellError hLifting hErrorZero
  have hSum := hDifference.add hBaseTarget
  simpa only [sub_add_cancel, zero_add] using hSum

end CircularLawSections56.Section5
