import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Tactic.Linarith

/-!
# Actual polynomial circle means

The Section 6 radial monotonicity and Jensen lower bound are proved for the
circle integral of a polynomial, not supplied as a root-factorization premise.
Mathlib's analytic Jensen formula also handles roots on the integration circle.
-/

open Filter MeasureTheory Metric Set Real MeromorphicOn
open scoped Polynomial

namespace CircularLawSection6

noncomputable def polynomialCircleMean (p : ℂ[X]) (r : ℝ) : ℝ :=
  circleAverage (fun w => Real.log ‖p.eval w‖) 0 r

theorem polynomial_log_circleIntegrable (p : ℂ[X]) (r : ℝ) :
    CircleIntegrable (fun w => Real.log ‖p.eval w‖) 0 r := by
  exact (analyticOnNhd_id.aeval_polynomial p).meromorphicOn.circleIntegrable_log_norm

/-- Radial monotonicity, including polynomials with zero constant term. The
zero polynomial is harmless under Lean's totalized `Real.log` convention. -/
theorem polynomialCircleMean_monotoneOn (p : ℂ[X]) :
    MonotoneOn (polynomialCircleMean p) (Ioi 0) := by
  have ha : AnalyticOnNhd ℂ (fun w => p.eval w) univ :=
    analyticOnNhd_id.aeval_polynomial p
  have hm : Meromorphic (fun w => p.eval w) := fun w => (ha w (mem_univ w)).meromorphicAt
  intro r hr s hs hrs
  have hmono := Function.locallyFinsuppWithin.logCounting_mono
    ha.divisor_nonneg hr hs hrs
  rw [Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const hm hr.ne',
    Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const hm hs.ne'] at hmono
  exact (sub_le_sub_iff_right _).1 hmono

/-- Jensen's lower bound at the unit circle. Nonvanishing at zero is essential:
`Real.log 0` must not masquerade as negative infinity. -/
theorem log_norm_eval_zero_le_polynomialCircleMean
    (p : ℂ[X]) (hp : p.eval 0 ≠ 0) :
    Real.log ‖p.eval 0‖ ≤ polynomialCircleMean p 1 := by
  have ha : AnalyticOnNhd ℂ (fun w => p.eval w) univ :=
    analyticOnNhd_id.aeval_polynomial p
  have hm : Meromorphic (fun w => p.eval w) := fun w => (ha w (mem_univ w)).meromorphicAt
  have hnonneg := Function.locallyFinsuppWithin.logCounting_nonneg
    ha.divisor_nonneg (r := 1) le_rfl
  rw [Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
    hm one_ne_zero, (ha 0 (mem_univ 0)).meromorphicTrailingCoeffAt_of_ne_zero hp] at hnonneg
  exact sub_nonneg.1 hnonneg

end CircularLawSection6
