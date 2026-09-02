import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Probability-level Section 3 input and branch closure

The scalar error envelopes in `IndicatorClosure.lean` are convenient for quantitative
bookkeeping, but the actual Section 3 short-ring endpoint is convergence in probability.
This file records that endpoint at the matching mathlib level, as `TendstoInMeasure`, and
proves that arbitrary interleaving with a long-branch sequence having the same limit
preserves convergence in probability.

The local Section 3 audit found a definition named
`ShortRingAnchor.Proposition36Conclusion` with this mathematical shape, but no local
theorem proving it.  Accordingly `Section3ShortRingAnchorInput` is an explicit premise,
not a constructed fact.
-/

open Filter MeasureTheory Topology

namespace CircularLawSections56.Section5

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Convergence in probability on one fixed probability space.  This matches the
`Proposition36Conclusion` endpoint of the local Section 3 project after instantiating its
normalized shifted log determinant. -/
def ConvergesInProbability
    (μ : Measure Ω) (observable : ℕ → Ω → ℝ) (target : ℝ) : Prop :=
  TendstoInMeasure μ observable atTop (fun _ => target)

/-- The known finite-moment short-ring/high-band anchor from Section 3, deliberately
represented as a named ordinary premise. -/
def Section3ShortRingAnchorInput
    (μ : Measure Ω) (shortLogPotential : ℕ → Ω → ℝ) (target : ℝ) : Prop :=
  ConvergesInProbability μ shortLogPotential target

/-- The expectation-strength Section 4--5 long branch, after its scalar estimates have
been converted to convergence in probability. -/
def LongBranchLogPotentialInput
    (μ : Measure Ω) (longLogPotential : ℕ → Ω → ℝ) (target : ℝ) : Prop :=
  ConvergesInProbability μ longLogPotential target

/-- Select the Section 3 short observable or the Section 4--5 long observable at each
index. -/
def branchSelectedLogPotential
    (shortBranch : ℕ → Bool)
    (shortLogPotential longLogPotential : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => if shortBranch n then shortLogPotential n ω else longLogPotential n ω

/-- An arbitrary interleaving of two sequences converging in measure to the same limit
also converges in measure to that limit. -/
theorem tendstoInMeasure_branchSelected
    (μ : Measure Ω) (shortBranch : ℕ → Bool)
    (shortLogPotential longLogPotential : ℕ → Ω → ℝ) (target : ℝ)
    (hShort : TendstoInMeasure μ shortLogPotential atTop (fun _ => target))
    (hLong : TendstoInMeasure μ longLogPotential atTop (fun _ => target)) :
    TendstoInMeasure μ
      (branchSelectedLogPotential shortBranch shortLogPotential longLogPotential)
      atTop (fun _ => target) := by
  intro ε hε
  have hMixed := (hShort ε hε).if' (hLong ε hε)
    (p := fun n => shortBranch n = true)
  convert hMixed using 1
  funext n
  cases h : shortBranch n <;> simp [branchSelectedLogPotential, h]

/-- Probability-level indicator log-potential conclusion with Section 3 visible as a
preinput and the long Section 4--5 conclusion visible separately. -/
theorem indicator_logPotential_tendstoInMeasure_of_section3_and_long
    (μ : Measure Ω) (shortBranch : ℕ → Bool)
    (shortLogPotential longLogPotential : ℕ → Ω → ℝ) (target : ℝ)
    (hSection3 :
      Section3ShortRingAnchorInput μ shortLogPotential target)
    (hLong : LongBranchLogPotentialInput μ longLogPotential target) :
    ConvergesInProbability μ
      (branchSelectedLogPotential shortBranch shortLogPotential longLogPotential)
      target := by
  exact tendstoInMeasure_branchSelected μ shortBranch shortLogPotential
    longLogPotential target hSection3 hLong

/-- Replacement-principle application at the probability level.

The Hilbert--Schmidt premise is a concrete uniform normalized second-moment bound rather
than an arbitrary proposition.  The replacement theorem itself remains an explicit
ordinary implication supplied by the caller. -/
theorem indicator_circularLaw_of_probability_inputs
    {CircularLawConclusion : Prop}
    (μ : Measure Ω) (shortBranch : ℕ → Bool)
    (shortLogPotential longLogPotential : ℕ → Ω → ℝ)
    (normalizedExpectedHSSquare : ℕ → ℝ) (target : ℝ)
    (hSection3 :
      Section3ShortRingAnchorInput μ shortLogPotential target)
    (hLong : LongBranchLogPotentialInput μ longLogPotential target)
    (hHSTightness :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n, normalizedExpectedHSSquare n ≤ C)
    (hReplacement :
      ConvergesInProbability μ
          (branchSelectedLogPotential shortBranch shortLogPotential longLogPotential)
          target →
        (∃ C : ℝ, 0 ≤ C ∧ ∀ n, normalizedExpectedHSSquare n ≤ C) →
        CircularLawConclusion) :
    CircularLawConclusion := by
  exact hReplacement
    (indicator_logPotential_tendstoInMeasure_of_section3_and_long
      μ shortBranch shortLogPotential longLogPotential target hSection3 hLong)
    hHSTightness

end CircularLawSections56.Section5
