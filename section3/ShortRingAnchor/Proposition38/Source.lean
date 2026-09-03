import ShortRingAnchor.SourceStatement
import Mathlib.Probability.Moments.SubGaussian

/-!
# Proposition 3.8: source and atom convention

Checked source: arXiv:2609.01295v1, `main.tex`, lines 1146--1249;
PDF pages 16--17. The source explicitly says **real** atoms. Its model is
(2.13), with `N = m W`, `m ≥ 4`, and three independent full block diagonals,
each normalized by `(3 W)^(-1/2)`. No density is assumed.

This file does not import the Section 8 high-band interface: that interface
assumes this proposition, and using it here would be circular.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace ShortRingAnchor.Proposition38

/-- Proposition 3.8's fixed real subgaussian atom. The finite MGF parameter
is an equivalent qualitative convention for a finite subgaussian norm;
no numerical conversion of Orlicz constants is used in the conclusion. -/
structure Atom where
  law : Measure ℝ
  parameter : ℝ≥0
  probability : law Set.univ = 1
  centered : (∫ x : ℝ, x ∂law) = 0
  second_moment : (∫ x : ℝ, x ^ 2 ∂law) = 1
  subgaussian : HasSubgaussianMGF (fun x : ℝ => x) parameter law

instance (A : Atom) : IsProbabilityMeasure A.law := ⟨A.probability⟩

/-- Equation (3.19), for arbitrary positive dimension sequences. This
only names the conclusion and does not assert it. As in Proposition 3.6,
the totalized logarithm is used only off an asymptotically negligible
singular event, whose probability must be proved to vanish. -/
def Conclusion {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : ℕ → ℕ) (X : ∀ k, Ω → Matrix (Fin (N k)) (Fin (N k)) ℂ) (z : ℂ) : Prop :=
  TendstoInMeasure μ (fun k sample => normalizedShiftLogDet (X k sample) z)
    atTop (fun _ => circularLogPotential z)

/-- Equation (3.19): the previously verified determinant assembly has
exactly the required convergence conclusion, not a circular-law premise. -/
theorem conclusion_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : ℕ → ℕ) (X : ∀ k, Ω → Matrix (Fin (N k)) (Fin (N k)) ℂ) (z : ℂ) :
    Conclusion μ N X z ↔ Proposition36SequenceConclusion μ N X z := Iff.rfl

end ShortRingAnchor.Proposition38
