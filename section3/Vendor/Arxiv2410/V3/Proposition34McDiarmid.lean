/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34McDiarmid.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.ComplexMcDiarmid
import Vendor.Arxiv2410.V3.Proposition34

/-!
# Proposition 3.4 with scalar concentration discharged by McDiarmid

The theorems here derive the paper's whole fixed-parameter scalar concentration estimate.
Given bounded Doob decompositions for the real and imaginary parts, the proved
McDiarmid pipeline constructs both the scalar estimate and its `1-n⁻¹⁰` event probability.

Only the three non-concentration comparisons in v3 formula (3.11) remain as inputs here.
-/

namespace Arxiv2410V3

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

/-- The three comparison inputs in v3 (3.11) other than scalar McDiarmid concentration,
retaining the paper's exact `sqrt(log n)` diagonal term. -/
structure Formula311ExactComparisonInputs
    (expectedTrace expectedGaussianTrace expectedCircularGaussianTrace freeTrace : ℂ)
    (n B v C : ℝ) : Prop where
  traceUniversality : External.BVHRemark613UnboundedExtensionHypothesis
    expectedTrace expectedGaussianTrace v (1 / Real.sqrt B) C
  diagonalCorrection :
    ‖expectedGaussianTrace - expectedCircularGaussianTrace‖ ≤
      C * Real.sqrt (Real.log n) / (Real.sqrt B * v ^ 2)
  gaussianFree : External.BBVTheorem28GaussianFreeHypothesis
    expectedCircularGaussianTrace freeTrace B v C

/-- The exact version of `formula311Inputs_complexConcentrationGood`. -/
theorem formula311Inputs_complexConcentrationGood_exact
    {Omega : Type*} {trace : Omega → ℂ}
    {expectedTrace expectedGaussianTrace expectedCircularGaussianTrace freeTrace : ℂ}
    {n B v C CD : ℝ}
    (comparisons : Formula311ExactComparisonInputs expectedTrace expectedGaussianTrace
      expectedCircularGaussianTrace freeTrace n B v C) :
    Formula311Inputs
      (ComplexConcentrationGood trace expectedTrace
        (CD * Real.sqrt (Real.log n) / (Real.sqrt n * v)))
      trace expectedTrace expectedGaussianTrace expectedCircularGaussianTrace freeTrace
      n B v C CD :=
  { scalarConcentration := scalarConcentrationHypothesis_complexConcentrationGood
    traceUniversality := comparisons.traceUniversality
    diagonalCorrection := comparisons.diagonalCorrection
    gaussianFree := comparisons.gaussianFree }

/-- v3 Proposition 3.4, `(3.11) => (3.9)`, with the former scalar concentration and event
probability interfaces both discharged by the proved McDiarmid pipeline.

The remaining `hre` and `him` arguments contain bounded Doob decompositions, not tail estimates.
The explicit `hexponent` is the elementary threshold choice which turns McDiarmid's displayed
exponential bound into `n⁻¹⁰`. -/
theorem proposition34_formula39_from_boundedDoobDifferences
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {filtration : Filtration ℕ mOmega}
    {trace : Omega → ℂ} (htraceMeasurable : Measurable trace)
    (htraceIntegrable : Integrable trace mu)
    {N : ℕ} {sensitivity : ℕ → ℝ≥0}
    (hre : BoundedDoobDifferences (ℱ := filtration) (mu := mu)
      (fun omega => (trace omega).re) N sensitivity)
    (him : BoundedDoobDifferences (ℱ := filtration) (mu := mu)
      (fun omega => (trace omega).im) N sensitivity)
    {expectedGaussianTrace expectedCircularGaussianTrace freeTrace : ℂ}
    {n B v C CD : ℝ} (hn : 0 < n) (hv : 0 < v) (hCD : 0 ≤ CD)
    (comparisons : Formula311ExactComparisonInputs (∫ omega, trace omega ∂mu)
      expectedGaussianTrace expectedCircularGaussianTrace freeTrace n B v C)
    (hexponent : 4 * Real.exp
      (-((CD * Real.sqrt (Real.log n) / (Real.sqrt n * v)) / 2) ^ 2 /
        (2 * (((∑ i ∈ Finset.range N,
          (sensitivity i / 2) ^ 2 : ℝ≥0)) : ℝ))) ≤ n ^ (-10 : ℤ))
    (rate : PolynomialRateCertificate n (formula311Error n B v C CD)) :
    Proposition34Formula39Conclusion mu
      (ComplexConcentrationGood trace (∫ omega, trace omega ∂mu)
        (CD * Real.sqrt (Real.log n) / (Real.sqrt n * v)))
      trace freeTrace n := by
  let bound : ℝ := CD * Real.sqrt (Real.log n) / (Real.sqrt n * v)
  have hbound : 0 ≤ bound := by
    dsimp only [bound]
    positivity
  have hprob :=
    probabilityAtLeast_complexConcentrationGood_of_boundedDoobDifferences_v3
      htraceMeasurable htraceIntegrable hre him hbound hexponent
  let inputs : Formula311Inputs
      (ComplexConcentrationGood trace (∫ omega, trace omega ∂mu) bound)
      trace (∫ omega, trace omega ∂mu) expectedGaussianTrace
      expectedCircularGaussianTrace freeTrace n B v C CD :=
    formula311Inputs_complexConcentrationGood_exact comparisons
  exact proposition34_formula39_from_interfaces inputs hprob rate

end Arxiv2410V3

