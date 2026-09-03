/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34RowMcDiarmid.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.DoobBridge
import Vendor.Arxiv2410.V3.McDiarmidArithmetic
import Vendor.Arxiv2410.V3.Proposition34McDiarmid

/-!
# Proposition 3.4 through the row-exposure McDiarmid step

This file is the strongest fixed-parameter route currently verified.  Its probability input is
only a pair of row-exposure Doob martingales with conditional increment intervals.  The
martingale centering/telescoping fields, absolute increment bounds, conditional Hoeffding,
Azuma--McDiarmid, complex four-tail union bound, and the explicit `n⁻¹⁰` exponent arithmetic are
all discharged internally.
-/

namespace Arxiv2410V3

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

/-- v3 Proposition 3.4, proof step (3), specialized to row sensitivity `2/(n v)`.

Taking the harmless explicit constant `C_D = 16`, this theorem removes both the old scalar
concentration/event interfaces and the separate McDiarmid exponent hypothesis.  The remaining
probabilistic certificate records only the model-specific row-exposure martingales and their
conditional increment intervals; it contains no concentration conclusion. -/
theorem proposition34_formula39_from_row_doobIntervalCertificates
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {filtration : Filtration ℕ mOmega}
    {trace : Omega → ℂ} (htraceMeasurable : Measurable trace)
    (htraceIntegrable : Integrable trace mu)
    {n : ℕ} (hn : 2 ≤ n) {v : ℝ} (hv : 0 < v)
    {sensitivity : ℕ → ℝ≥0}
    (hsensitivity : ∀ i < n,
      (sensitivity i : ℝ) ≤ 2 / ((n : ℝ) * v))
    (hsensitivityPos : ∃ i < n, 0 < sensitivity i)
    (hre : DoobIntervalCertificate (filtration := filtration) (mu := mu)
      (fun omega => (trace omega).re) n sensitivity)
    (him : DoobIntervalCertificate (filtration := filtration) (mu := mu)
      (fun omega => (trace omega).im) n sensitivity)
    {expectedGaussianTrace expectedCircularGaussianTrace freeTrace : ℂ}
    {B C : ℝ}
    (comparisons : Formula311ExactComparisonInputs (∫ omega, trace omega ∂mu)
      expectedGaussianTrace expectedCircularGaussianTrace freeTrace (n : ℝ) B v C)
    (rate : PolynomialRateCertificate (n : ℝ)
      (formula311Error (n : ℝ) B v C 16)) :
    Proposition34Formula39Conclusion mu
      (ComplexConcentrationGood trace (∫ omega, trace omega ∂mu)
        (16 * Real.sqrt (Real.log (n : ℝ)) / (Real.sqrt (n : ℝ) * v)))
      trace freeTrace (n : ℝ) := by
  exact proposition34_formula39_from_boundedDoobDifferences
    htraceMeasurable htraceIntegrable
    hre.toBoundedDoobDifferences him.toBoundedDoobDifferences
    (by
      have hnPos : 0 < n := by omega
      exact_mod_cast hnPos)
    hv (by norm_num : (0 : ℝ) ≤ 16) comparisons
    (four_exp_mcdiarmid_threshold_sixteen_le_of_one_pos
      hn hv hsensitivity hsensitivityPos)
    rate

end Arxiv2410V3

