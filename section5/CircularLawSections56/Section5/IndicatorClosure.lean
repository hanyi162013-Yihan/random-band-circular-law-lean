import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Branchwise indicator-profile closure

This module records an honest scalar interface for the final proof of the indicator-profile
theorem.  Its hypotheses are deliberately labelled by provenance:

* **Section 3 input:** the short/high-band branch already has an anchor error comparing
  the normalized logarithmic potential with the target;
* **Section 4 inputs:** in the long branch, the determinant-to-random-pressure seam and
  the random-to-mean pressure fluctuation are already bounded; and
* **Section 5 input:** the lifted mean pressure is already close to the target.

The proofs below only combine these inputs.  The replacement principle is likewise an
ordinary implication supplied by the caller, together with an explicit uniform bound on
the normalized expected Hilbert--Schmidt square.  No external random-matrix theorem is
encoded as an axiom or hidden in a structure field.
-/

open Filter Topology

namespace CircularLawSections56.Section5

/-- Error assigned to the short/high-band branch.  It is exactly the explicit Section 3
anchor error; Section 5 does not re-prove that random-matrix input. -/
def shortBranchError (section3AnchorError : ℝ) : ℝ :=
  section3AnchorError

/-- Error assigned to the long branch: Section 4's final seam and pressure fluctuation,
plus Section 5's mean-pressure error. -/
def longBranchError
    (section4SeamError section4PressureFluctuationError
      section5MeanPressureError : ℝ) : ℝ :=
  section4SeamError + section4PressureFluctuationError +
    section5MeanPressureError

/-- Branch-selected error.  `true` denotes the short/high-band branch and `false` the
long pressure-lifting branch. -/
def indicatorBranchError (shortBranch : Bool)
    (section3AnchorError section4SeamError
      section4PressureFluctuationError section5MeanPressureError : ℝ) : ℝ :=
  if shortBranch then
    shortBranchError section3AnchorError
  else
    longBranchError section4SeamError section4PressureFluctuationError
      section5MeanPressureError

/-- **Short branch.**  This theorem makes the Section 3 dependency explicit: the branch
closes from the supplied high-band/anchor absolute-error estimate and nothing else. -/
theorem indicator_short_branch_error_bound
    (logPotential target section3AnchorError : ℝ)
    (hSection3Anchor :
      |logPotential - target| ≤ section3AnchorError) :
    |logPotential - target| ≤ shortBranchError section3AnchorError := by
  exact hSection3Anchor

/-- **Long branch.**  The first two hypotheses are the final-seam and pressure-
fluctuation inputs proved in Section 4.  The third is the mean-pressure calibration and
lifting output of Section 5. -/
theorem indicator_long_branch_error_bound
    (logPotential randomPressure meanPressure target
      section4SeamError section4PressureFluctuationError
      section5MeanPressureError : ℝ)
    (hSection4Seam :
      |logPotential - randomPressure| ≤ section4SeamError)
    (hSection4PressureFluctuation :
      |randomPressure - meanPressure| ≤
        section4PressureFluctuationError)
    (hSection5MeanPressure :
      |meanPressure - target| ≤ section5MeanPressureError) :
    |logPotential - target| ≤
      longBranchError section4SeamError
        section4PressureFluctuationError section5MeanPressureError := by
  unfold longBranchError
  calc
    |logPotential - target| =
        |(logPotential - randomPressure) +
          ((randomPressure - meanPressure) + (meanPressure - target))| := by
      ring_nf
    _ ≤ |logPotential - randomPressure| +
          |(randomPressure - meanPressure) + (meanPressure - target)| :=
      abs_add_le _ _
    _ ≤ |logPotential - randomPressure| +
          (|randomPressure - meanPressure| + |meanPressure - target|) :=
      add_le_add (le_refl _) (abs_add_le _ _)
    _ ≤ section4SeamError + section4PressureFluctuationError +
          section5MeanPressureError := by
      linarith

/-- The two branches cover the target absolute error.  Every premise visibly identifies
whether it comes from Section 3, Section 4, or Section 5. -/
theorem indicator_branchwise_error_bound
    (shortBranch : Bool)
    (logPotential randomPressure meanPressure target
      section3AnchorError section4SeamError
      section4PressureFluctuationError section5MeanPressureError : ℝ)
    (hSection3Anchor : shortBranch = true →
      |logPotential - target| ≤ section3AnchorError)
    (hSection4Seam : shortBranch = false →
      |logPotential - randomPressure| ≤ section4SeamError)
    (hSection4PressureFluctuation : shortBranch = false →
      |randomPressure - meanPressure| ≤
        section4PressureFluctuationError)
    (hSection5MeanPressure : shortBranch = false →
      |meanPressure - target| ≤ section5MeanPressureError) :
    |logPotential - target| ≤
      indicatorBranchError shortBranch section3AnchorError
        section4SeamError section4PressureFluctuationError
        section5MeanPressureError := by
  cases shortBranch with
  | false =>
      simpa [indicatorBranchError] using
        indicator_long_branch_error_bound
          logPotential randomPressure meanPressure target
          section4SeamError section4PressureFluctuationError
          section5MeanPressureError
          (hSection4Seam rfl) (hSection4PressureFluctuation rfl)
          (hSection5MeanPressure rfl)
  | true =>
      simpa [indicatorBranchError] using
        indicator_short_branch_error_bound
          logPotential target section3AnchorError (hSection3Anchor rfl)

/-- A branch-independent nonnegative envelope.  Absolute values make the convergence
theorem valid without adding redundant sign assumptions on error sequences. -/
def indicatorErrorEnvelope
    (section3AnchorError section4SeamError
      section4PressureFluctuationError section5MeanPressureError : ℝ) : ℝ :=
  |section3AnchorError| + |section4SeamError| +
    |section4PressureFluctuationError| + |section5MeanPressureError|

/-- The branchwise inputs imply a single branch-independent absolute-error estimate. -/
theorem indicator_error_le_envelope
    (shortBranch : Bool)
    (logPotential randomPressure meanPressure target
      section3AnchorError section4SeamError
      section4PressureFluctuationError section5MeanPressureError : ℝ)
    (hSection3Anchor : shortBranch = true →
      |logPotential - target| ≤ section3AnchorError)
    (hSection4Seam : shortBranch = false →
      |logPotential - randomPressure| ≤ section4SeamError)
    (hSection4PressureFluctuation : shortBranch = false →
      |randomPressure - meanPressure| ≤
        section4PressureFluctuationError)
    (hSection5MeanPressure : shortBranch = false →
      |meanPressure - target| ≤ section5MeanPressureError) :
    |logPotential - target| ≤
      indicatorErrorEnvelope section3AnchorError section4SeamError
        section4PressureFluctuationError section5MeanPressureError := by
  cases shortBranch with
  | false =>
      have hlong := indicator_long_branch_error_bound
        logPotential randomPressure meanPressure target
        section4SeamError section4PressureFluctuationError
        section5MeanPressureError
        (hSection4Seam rfl) (hSection4PressureFluctuation rfl)
        (hSection5MeanPressure rfl)
      unfold indicatorErrorEnvelope longBranchError at *
      linarith [le_abs_self section4SeamError,
        le_abs_self section4PressureFluctuationError,
        le_abs_self section5MeanPressureError,
        abs_nonneg section3AnchorError]
  | true =>
      have hshort := hSection3Anchor rfl
      unfold indicatorErrorEnvelope
      linarith [le_abs_self section3AnchorError,
        abs_nonneg section4SeamError,
        abs_nonneg section4PressureFluctuationError,
        abs_nonneg section5MeanPressureError]

/-- If every Section 3/4/5 scalar error tends to zero, the branch may vary arbitrarily
with `n` and the normalized logarithmic potential still tends to the target. -/
theorem indicator_branchwise_logPotential_tendsto
    (shortBranch : ℕ → Bool)
    (logPotential randomPressure meanPressure : ℕ → ℝ)
    (target : ℝ)
    (section3AnchorError section4SeamError
      section4PressureFluctuationError section5MeanPressureError : ℕ → ℝ)
    (hSection3Anchor : ∀ n, shortBranch n = true →
      |logPotential n - target| ≤ section3AnchorError n)
    (hSection4Seam : ∀ n, shortBranch n = false →
      |logPotential n - randomPressure n| ≤ section4SeamError n)
    (hSection4PressureFluctuation : ∀ n, shortBranch n = false →
      |randomPressure n - meanPressure n| ≤
        section4PressureFluctuationError n)
    (hSection5MeanPressure : ∀ n, shortBranch n = false →
      |meanPressure n - target| ≤ section5MeanPressureError n)
    (hSection3AnchorError :
      Tendsto section3AnchorError atTop (𝓝 0))
    (hSection4SeamError :
      Tendsto section4SeamError atTop (𝓝 0))
    (hSection4PressureFluctuationError :
      Tendsto section4PressureFluctuationError atTop (𝓝 0))
    (hSection5MeanPressureError :
      Tendsto section5MeanPressureError atTop (𝓝 0)) :
    Tendsto logPotential atTop (𝓝 target) := by
  have h3abs :
      Tendsto (fun n => |section3AnchorError n|) atTop (𝓝 0) := by
    simpa using hSection3AnchorError.abs
  have h4seamAbs :
      Tendsto (fun n => |section4SeamError n|) atTop (𝓝 0) := by
    simpa using hSection4SeamError.abs
  have h4fluctAbs :
      Tendsto (fun n => |section4PressureFluctuationError n|)
        atTop (𝓝 0) := by
    simpa using hSection4PressureFluctuationError.abs
  have h5abs :
      Tendsto (fun n => |section5MeanPressureError n|) atTop (𝓝 0) := by
    simpa using hSection5MeanPressureError.abs
  have hEnvelope :
      Tendsto (fun n => indicatorErrorEnvelope
        (section3AnchorError n) (section4SeamError n)
        (section4PressureFluctuationError n) (section5MeanPressureError n))
        atTop (𝓝 0) := by
    simpa [indicatorErrorEnvelope] using
      ((h3abs.add h4seamAbs).add h4fluctAbs).add h5abs
  have hAbs :
      Tendsto (fun n => |logPotential n - target|) atTop (𝓝 0) :=
    squeeze_zero
      (fun n => abs_nonneg (logPotential n - target))
      (fun n => indicator_error_le_envelope
        (shortBranch n) (logPotential n) (randomPressure n)
        (meanPressure n) target (section3AnchorError n)
        (section4SeamError n) (section4PressureFluctuationError n)
        (section5MeanPressureError n)
        (hSection3Anchor n) (hSection4Seam n)
        (hSection4PressureFluctuation n) (hSection5MeanPressure n))
      hEnvelope
  exact tendsto_iff_dist_tendsto_zero.2 (by
    simpa [Real.dist_eq] using hAbs)

/-- The manuscript identity `N⁻¹ E‖X_N‖_HS² = 1` supplies the explicit uniform
Hilbert--Schmidt-square bound expected by the replacement closure below. -/
theorem uniform_hs_square_bound_of_eq_one
    (normalizedExpectedHSSquare : ℕ → ℝ)
    (hHSIdentity : ∀ n, normalizedExpectedHSSquare n = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, normalizedExpectedHSSquare n ≤ C := by
  refine ⟨1, zero_le_one, ?_⟩
  intro n
  rw [hHSIdentity n]

/-- Generic replacement-principle closure.

`hReplacement` is an ordinary implication supplied by the caller.  Thus the theorem does
not claim to formalize the external replacement principle: it only applies that explicit
input to (i) logarithmic-potential convergence and (ii) an explicit uniform normalized
Hilbert--Schmidt-square bound. -/
theorem replacement_principle_closure
    {CircularLawConclusion : Prop}
    (logPotential normalizedExpectedHSSquare : ℕ → ℝ)
    (target : ℝ)
    (hLogPotential : Tendsto logPotential atTop (𝓝 target))
    (hHSTightness :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n, normalizedExpectedHSSquare n ≤ C)
    (hReplacement :
      Tendsto logPotential atTop (𝓝 target) →
        (∃ C : ℝ, 0 ≤ C ∧
          ∀ n, normalizedExpectedHSSquare n ≤ C) →
        CircularLawConclusion) :
    CircularLawConclusion :=
  hReplacement hLogPotential hHSTightness

/-- End-to-end scalar indicator closure with every non-Section-5 result exposed as an
ordinary premise:

* `hSection3Anchor` and its vanishing error are the **Section 3** input;
* `hSection4Seam` and `hSection4PressureFluctuation` are the **Section 4** inputs;
* `hSection5MeanPressure` is the **Section 5** lifting output;
* `hHSTightness` is the explicit Hilbert--Schmidt tightness input; and
* `hReplacement` is the external replacement principle as a plain implication.
-/
theorem indicator_circularLaw_of_branchwise_errors
    {CircularLawConclusion : Prop}
    (shortBranch : ℕ → Bool)
    (logPotential randomPressure meanPressure
      normalizedExpectedHSSquare : ℕ → ℝ)
    (target : ℝ)
    (section3AnchorError section4SeamError
      section4PressureFluctuationError section5MeanPressureError : ℕ → ℝ)
    (hSection3Anchor : ∀ n, shortBranch n = true →
      |logPotential n - target| ≤ section3AnchorError n)
    (hSection4Seam : ∀ n, shortBranch n = false →
      |logPotential n - randomPressure n| ≤ section4SeamError n)
    (hSection4PressureFluctuation : ∀ n, shortBranch n = false →
      |randomPressure n - meanPressure n| ≤
        section4PressureFluctuationError n)
    (hSection5MeanPressure : ∀ n, shortBranch n = false →
      |meanPressure n - target| ≤ section5MeanPressureError n)
    (hSection3AnchorError :
      Tendsto section3AnchorError atTop (𝓝 0))
    (hSection4SeamError :
      Tendsto section4SeamError atTop (𝓝 0))
    (hSection4PressureFluctuationError :
      Tendsto section4PressureFluctuationError atTop (𝓝 0))
    (hSection5MeanPressureError :
      Tendsto section5MeanPressureError atTop (𝓝 0))
    (hHSTightness :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n, normalizedExpectedHSSquare n ≤ C)
    (hReplacement :
      Tendsto logPotential atTop (𝓝 target) →
        (∃ C : ℝ, 0 ≤ C ∧
          ∀ n, normalizedExpectedHSSquare n ≤ C) →
        CircularLawConclusion) :
    CircularLawConclusion := by
  apply replacement_principle_closure
    logPotential normalizedExpectedHSSquare target
  · exact indicator_branchwise_logPotential_tendsto
      shortBranch logPotential randomPressure meanPressure target
      section3AnchorError section4SeamError
      section4PressureFluctuationError section5MeanPressureError
      hSection3Anchor hSection4Seam hSection4PressureFluctuation
      hSection5MeanPressure hSection3AnchorError hSection4SeamError
      hSection4PressureFluctuationError hSection5MeanPressureError
  · exact hHSTightness
  · exact hReplacement

end CircularLawSections56.Section5
