import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Mesoscopic calibration and the final one-seam closure

The random variables in the manuscript live on probability spaces which vary with the
bandwidth.  The internal argument only uses three scalar `L¹` error estimates.  Encoding
those estimates as real numbers avoids pretending that the triangular array is a sequence
on one fixed probability space.
-/

open Filter Topology

namespace CircularLawSections56.Section5

/-- The triangle inequality used in mesoscopic calibration: an anchor observable is close
to the circular potential, the random pressure is close to the anchor, and the deterministic
mean pressure is close to the random pressure. -/
theorem mesoscopic_calibration_error_bound
    (anchor randomPressure meanPressure target anchorError seamError concentrationError : ℝ)
    (hAnchor : |anchor - target| ≤ anchorError)
    (hSeam : |randomPressure - anchor| ≤ seamError)
    (hConcentration : |meanPressure - randomPressure| ≤ concentrationError) :
    |meanPressure - target| ≤ concentrationError + seamError + anchorError := by
  calc
    |meanPressure - target| =
        |(meanPressure - randomPressure) +
          ((randomPressure - anchor) + (anchor - target))| := by ring_nf
    _ ≤ |meanPressure - randomPressure| +
          |(randomPressure - anchor) + (anchor - target)| := abs_add_le _ _
    _ ≤ |meanPressure - randomPressure| +
          (|randomPressure - anchor| + |anchor - target|) :=
      add_le_add (le_refl _) (abs_add_le _ _)
    _ ≤ concentrationError + seamError + anchorError := by linarith

/-- Triangular-array version of the mesoscopic calibration argument.  No common underlying
sample space is assumed: the hypotheses are precisely the three scalar `L¹` errors used by
the proof. -/
theorem mesoscopic_calibration_tendsto
    (anchor randomPressure meanPressure : ℕ → ℝ) (target : ℝ)
    (anchorError seamError concentrationError : ℕ → ℝ)
    (hAnchor : ∀ n, |anchor n - target| ≤ anchorError n)
    (hSeam : ∀ n, |randomPressure n - anchor n| ≤ seamError n)
    (hConcentration : ∀ n,
      |meanPressure n - randomPressure n| ≤ concentrationError n)
    (hAnchorError : Tendsto anchorError atTop (𝓝 0))
    (hSeamError : Tendsto seamError atTop (𝓝 0))
    (hConcentrationError : Tendsto concentrationError atTop (𝓝 0)) :
    Tendsto meanPressure atTop (𝓝 target) := by
  have hsum :
      Tendsto (fun n => concentrationError n + seamError n + anchorError n)
        atTop (𝓝 0) := by
    simpa only [zero_add] using
      (hConcentrationError.add hSeamError).add hAnchorError
  have habs : Tendsto (fun n => |meanPressure n - target|) atTop (𝓝 0) :=
    squeeze_zero
      (fun n => abs_nonneg (meanPressure n - target))
      (fun n => mesoscopic_calibration_error_bound
        (anchor n) (randomPressure n) (meanPressure n) target
        (anchorError n) (seamError n) (concentrationError n)
        (hAnchor n) (hSeam n) (hConcentration n))
      hsum
  exact tendsto_iff_dist_tendsto_zero.2 (by
    simpa [Real.dist_eq] using habs)

/-- The final closure is the same three-error calculation, with the order used in
`eq:final-seam`, `eq:final-pressure-fluctuation`, and `eq:target-mean-pressure`. -/
theorem final_closure_error_bound
    (logDet randomPressure meanPressure target seamError fluctuationError
      meanPressureError : ℝ)
    (hSeam : |logDet - randomPressure| ≤ seamError)
    (hFluctuation : |randomPressure - meanPressure| ≤ fluctuationError)
    (hMean : |meanPressure - target| ≤ meanPressureError) :
    |logDet - target| ≤ seamError + fluctuationError + meanPressureError := by
  calc
    |logDet - target| =
        |(logDet - randomPressure) +
          ((randomPressure - meanPressure) + (meanPressure - target))| := by ring_nf
    _ ≤ |logDet - randomPressure| +
          |(randomPressure - meanPressure) + (meanPressure - target)| := abs_add_le _ _
    _ ≤ |logDet - randomPressure| +
          (|randomPressure - meanPressure| + |meanPressure - target|) :=
      add_le_add (le_refl _) (abs_add_le _ _)
    _ ≤ seamError + fluctuationError + meanPressureError := by linarith

/-- Asymptotic conclusion of the single final closure.  This theorem is the exported
`L¹`/expectation-strength interface needed by the compact-Gaussian-core argument in
Section 6, once its three hypotheses are instantiated by Sections 3--5. -/
theorem final_closure_tendsto
    (logDet randomPressure meanPressure : ℕ → ℝ) (target : ℝ)
    (seamError fluctuationError meanPressureError : ℕ → ℝ)
    (hSeam : ∀ n, |logDet n - randomPressure n| ≤ seamError n)
    (hFluctuation : ∀ n,
      |randomPressure n - meanPressure n| ≤ fluctuationError n)
    (hMean : ∀ n, |meanPressure n - target| ≤ meanPressureError n)
    (hSeamError : Tendsto seamError atTop (𝓝 0))
    (hFluctuationError : Tendsto fluctuationError atTop (𝓝 0))
    (hMeanPressureError : Tendsto meanPressureError atTop (𝓝 0)) :
    Tendsto logDet atTop (𝓝 target) := by
  have hsum : Tendsto
      (fun n => seamError n + fluctuationError n + meanPressureError n)
      atTop (𝓝 0) := by
    simpa only [zero_add] using
      (hSeamError.add hFluctuationError).add hMeanPressureError
  have habs : Tendsto (fun n => |logDet n - target|) atTop (𝓝 0) :=
    squeeze_zero
      (fun n => abs_nonneg (logDet n - target))
      (fun n => final_closure_error_bound
        (logDet n) (randomPressure n) (meanPressure n) target
        (seamError n) (fluctuationError n) (meanPressureError n)
        (hSeam n) (hFluctuation n) (hMean n))
      hsum
  exact tendsto_iff_dist_tendsto_zero.2 (by
    simpa [Real.dist_eq] using habs)

end CircularLawSections56.Section5
