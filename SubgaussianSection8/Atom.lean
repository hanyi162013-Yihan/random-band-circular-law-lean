import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Function.L2Space

/-! A fixed real centered variance-one subgaussian law. The parameter is arbitrary;
no support bound, density, or higher-moment input is imposed. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace SubgaussianSection8

structure Atom where
  law : Measure ℝ
  parameter : ℝ≥0
  probability : law Set.univ = 1
  centered : (∫ x : ℝ, x ∂law) = 0
  second_moment : (∫ x : ℝ, x ^ 2 ∂law) = 1
  subgaussian : HasSubgaussianMGF (fun x : ℝ => x) parameter law

instance (A : Atom) : IsProbabilityMeasure A.law := ⟨A.probability⟩

theorem Atom.integrable_sq (A : Atom) : Integrable (fun x : ℝ => x ^ 2) A.law := by
  have h : MemLp (fun x : ℝ => x) 2 A.law := by
    simpa using A.subgaussian.memLp 2
  exact (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mp h

end SubgaussianSection8
