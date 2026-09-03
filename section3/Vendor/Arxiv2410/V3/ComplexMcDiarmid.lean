/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/ComplexMcDiarmid.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.McDiarmid
import Vendor.Arxiv2410.V3.ScalarConcentration
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Applying the proved McDiarmid core to a complex observable

The generic McDiarmid theorem in `McDiarmid.lean` is one-sided and real-valued.  This file proves
the sign-change construction and applies the theorem to the real and imaginary parts of a complex
observable.  Combined with `ScalarConcentration.lean`, two Doob bounded-difference witnesses give
the exact four-tail complex probability statement used in v3 Proposition 3.4.
-/

namespace Arxiv2410V3

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

section Negation

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}
  [StandardBorelSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
  {filtration : Filtration ℕ mOmega}

/-- Lower-tail form of the proved McDiarmid theorem, obtained by negating the complete Doob
decomposition. -/
theorem mcdiarmid_lowerTail_of_boundedDoobDifferences
    {F : Omega → ℝ} {N : ℕ} {c : ℕ → ℝ≥0}
    (h : BoundedDoobDifferences (ℱ := filtration) (mu := mu) F N c)
    {t : ℝ} (ht : 0 ≤ t) :
    mu.real (centeredLowerTail F (∫ x, F x ∂mu) t) ≤
      exp (-t ^ 2 /
        (2 * (((∑ i ∈ Finset.range N, (c i / 2) ^ 2 : ℝ≥0)) : ℝ))) := by
  simpa only [centeredLowerTail, neg_sub] using
    (mcdiarmid_lower_of_boundedDoobDifferences h ht)

/-- Upper-tail form with the event notation used by `ScalarConcentration.lean`. -/
theorem mcdiarmid_upperTail_of_boundedDoobDifferences
    {F : Omega → ℝ} {N : ℕ} {c : ℕ → ℝ≥0}
    (h : BoundedDoobDifferences (ℱ := filtration) (mu := mu) F N c)
    {t : ℝ} (ht : 0 ≤ t) :
    mu.real (centeredUpperTail F (∫ x, F x ∂mu) t) ≤
      exp (-t ^ 2 /
        (2 * (((∑ i ∈ Finset.range N, (c i / 2) ^ 2 : ℝ≥0)) : ℝ))) := by
  exact mcdiarmid_of_boundedDoobDifferences h ht

end Negation

section ComplexObservable

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}
  [StandardBorelSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
  {filtration : Filtration ℕ mOmega}

/-- v3 Proposition 3.4, proof step (3): complete conversion from real Doob bounded differences
to the complex scalar concentration event.

The two hypotheses contain no tail conclusion: they are bounded Doob decompositions for the real
and imaginary parts.  Hoeffding, Azuma--Hoeffding, sign reversal, and the four-event union bound
are all proved in Lean. -/
theorem probabilityAtLeast_complexConcentrationGood_of_boundedDoobDifferences
    {trace : Omega → ℂ} (htraceMeasurable : Measurable trace)
    (htraceIntegrable : Integrable trace mu)
    {N : ℕ} {c : ℕ → ℝ≥0}
    (hre : BoundedDoobDifferences (ℱ := filtration) (mu := mu)
      (fun omega => (trace omega).re) N c)
    (him : BoundedDoobDifferences (ℱ := filtration) (mu := mu)
      (fun omega => (trace omega).im) N c)
    {bound : ℝ} (hbound : 0 ≤ bound) :
    ProbabilityAtLeast mu
      (ComplexConcentrationGood trace (∫ omega, trace omega ∂mu) bound)
      (1 - 4 * exp (-(bound / 2) ^ 2 /
        (2 * (((∑ i ∈ Finset.range N, (c i / 2) ^ 2 : ℝ≥0)) : ℝ)))) := by
  have hreMean : (∫ omega, (trace omega).re ∂mu) =
      (∫ omega, trace omega ∂mu).re := integral_re htraceIntegrable
  have himMean : (∫ omega, (trace omega).im ∂mu) =
      (∫ omega, trace omega ∂mu).im := integral_im htraceIntegrable
  apply probabilityAtLeast_complexConcentrationGood_of_four_tails
    htraceMeasurable hbound
  · have h := mcdiarmid_upperTail_of_boundedDoobDifferences hre
      (by positivity : 0 ≤ bound / 2)
    rwa [hreMean] at h
  · have h := mcdiarmid_lowerTail_of_boundedDoobDifferences hre
      (by positivity : 0 ≤ bound / 2)
    rwa [hreMean] at h
  · have h := mcdiarmid_upperTail_of_boundedDoobDifferences him
      (by positivity : 0 ≤ bound / 2)
    rwa [himMean] at h
  · have h := mcdiarmid_lowerTail_of_boundedDoobDifferences him
      (by positivity : 0 ≤ bound / 2)
    rwa [himMean] at h

/-- The preceding fully proved McDiarmid pipeline at the exact `1-n⁻¹⁰` probability level of
v3 Proposition 3.4.  The final displayed inequality is only the elementary choice of threshold
relative to the explicit McDiarmid exponent. -/
theorem probabilityAtLeast_complexConcentrationGood_of_boundedDoobDifferences_v3
    {trace : Omega → ℂ} (htraceMeasurable : Measurable trace)
    (htraceIntegrable : Integrable trace mu)
    {N : ℕ} {c : ℕ → ℝ≥0}
    (hre : BoundedDoobDifferences (ℱ := filtration) (mu := mu)
      (fun omega => (trace omega).re) N c)
    (him : BoundedDoobDifferences (ℱ := filtration) (mu := mu)
      (fun omega => (trace omega).im) N c)
    {bound n : ℝ} (hbound : 0 ≤ bound)
    (hexponent : 4 * exp (-(bound / 2) ^ 2 /
      (2 * (((∑ i ∈ Finset.range N, (c i / 2) ^ 2 : ℝ≥0)) : ℝ))) ≤
        n ^ (-10 : ℤ)) :
    ProbabilityAtLeast mu
      (ComplexConcentrationGood trace (∫ omega, trace omega ∂mu) bound)
      (1 - n ^ (-10 : ℤ)) := by
  have hbase := probabilityAtLeast_complexConcentrationGood_of_boundedDoobDifferences
    htraceMeasurable htraceIntegrable hre him hbound
  exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hbase

end ComplexObservable

end Arxiv2410V3

