import ShortRingAnchor.BC12.CorrelationConvergence
import ShortRingAnchor.BC12.DiskPotential
import ShortRingAnchor.BC12.EigenvalueLogdet

/-!
# The BC12 logarithmic-determinant input from exact Ginibre formulas

Conditional on the explicitly named finite-dimensional correlation and
projection formulas, this file proves the full normalized logarithmic
determinant convergence used in Proposition 3.6.  No circular law,
logarithmic uniform integrability, variance estimate, disk-potential
formula, or nonsingularity conclusion is an assumption of this theorem.

The finite formulas themselves are **not** proved here.  In particular we
do not claim to have constructed the Ginibre ensemble from Gaussian entries
and derived its eigenvalue Jacobian.  See `KnownFormulas.lean` for the exact
external boundary, and `IsEigenvalueEnumeration` for the purely algebraic
identification of the supplied eigenvalues with the matrix.
-/

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace ShortRingAnchor.BC12

/-- The logarithmic eigenvalue statistic converges to formula (2.1).
Analytic admissibility of this unbounded test function and identification
of its limiting integral have both been proved in separate modules. -/
theorem ginibre_log_statistic_convergesInProbability_of_formulas
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {M : ℕ → ℕ} (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop)
    (eigenvalue : ∀ n, Omega → Fin (M n) → ℂ)
    (hprojection : ∀ n, GinibreProjectionIntegralFormula (M n))
    (hcorrelation : ∀ n, GinibreCorrelationFormulas mu (eigenvalue n)) (z : ℂ) :
    ConvergesInProbability mu
      (fun n => eigenvalueStatistic (eigenvalue n) (fun w => Real.log ‖w - z‖))
      (circularLogPotential z) := by
  have h := ginibre_statistic_convergesInProbability_of_formulas hMpos hM eigenvalue
    hprojection hcorrelation (by fun_prop : Measurable (fun w : ℂ => Real.log ‖w - z‖))
    (integrable_abs_log_mul_ginibreEnvelope z) (integrable_log_sq_mul_ginibreEnvelope z)
  simpa only [integral_log_mul_circularDensity] using h

/-- **The BC12 full-logdet input used in Proposition 3.6**, derived from
finite-dimensional formulas.  The conclusion is the exact
`normalizedShiftLogDet` expression, not a surrogate linear statistic.

The shift `z` is arbitrary and fixed.  The only random-matrix hypotheses
are the named exact formulas.  `henumeration` identifies algebraic
multiplicities and does not assert simplicity or avoid a fixed `z`; the
needed a.e. avoidance is itself proved from the first correlation formula. -/
theorem ginibre_logdet_convergesInProbability_of_formulas
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {M : ℕ → ℕ} (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop)
    (G : ∀ n, Omega → Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (eigenvalue : ∀ n, Omega → Fin (M n) → ℂ)
    (henumeration : ∀ n sample, IsEigenvalueEnumeration (G n sample) (eigenvalue n sample))
    (hprojection : ∀ n, GinibreProjectionIntegralFormula (M n))
    (hcorrelation : ∀ n, GinibreCorrelationFormulas mu (eigenvalue n)) (z : ℂ) :
    ConvergesInProbability mu
      (fun n sample => normalizedShiftLogDet (G n sample) z)
      (circularLogPotential z) := by
  have hstat := ginibre_log_statistic_convergesInProbability_of_formulas hMpos hM
    eigenvalue hprojection hcorrelation z
  apply MeasureTheory.TendstoInMeasure.congr_left (h_tendsto := hstat)
  intro n
  filter_upwards [eigenvalues_ne_fixed_ae_of_firstMoment (hMpos n) (hcorrelation n) z]
    with sample hsample
  exact (normalizedShiftLogDet_eq_eigenvalueStatistic (A := G n)
    (eigenvalue := eigenvalue n) (sample := sample) (z := z)
    (henumeration n sample) hsample).symm

/-- Matrix-only version: the eigenvalue enumeration is constructed by
Lean, so the user supplies only the finite Ginibre formulas, not an
algebraic factorization hypothesis.  This theorem can directly discharge
`hBC12Full` in the Proposition 3.6 assembly. -/
theorem ginibre_matrix_logdet_convergesInProbability_of_formulas
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {M : ℕ → ℕ} (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop)
    (G : ∀ n, Omega → Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (hprojection : ∀ n, GinibreProjectionIntegralFormula (M n))
    (hcorrelation : ∀ n, GinibreCorrelationFormulas mu
      (fun sample => matrixEigenvalues (G n sample))) (z : ℂ) :
    ConvergesInProbability mu
      (fun n sample => normalizedShiftLogDet (G n sample) z)
      (circularLogPotential z) :=
  ginibre_logdet_convergesInProbability_of_formulas hMpos hM G
    (fun n sample => matrixEigenvalues (G n sample))
    (fun _ _ => matrixEigenvalues_spec _) hprojection hcorrelation z

end ShortRingAnchor.BC12
