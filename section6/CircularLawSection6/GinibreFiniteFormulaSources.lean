import CircularLawSection6.DenseProfileEndpoint
import ShortRingAnchor.BC12.LogdetConvergence

/-! # Reusing Section 3's proved finite-formula logarithmic-potential route

Only the exact finite-dimensional formulas for the actual Gaussian matrix
are inputs. The full logarithmic-potential limit, including the unbounded
log test and circular center, is supplied by the existing Section 3 theorem.
The exact correlation formulas are not proved by this adapter.
-/

open MeasureTheory Filter Topology ShortRingAnchor
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete
  (BBVComparisonInput gaussianSequenceLaw ginibreOnSequence)
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace CircularLawSection6

structure GinibreFiniteFormulaInput : Prop where
  projection : ∀ N : ℕ, 0 < N → BC12.GinibreProjectionIntegralFormula N
  correlation : ∀ N : ℕ, 0 < N → BC12.GinibreCorrelationFormulas gaussianSequenceLaw
    (fun ω => BC12.matrixEigenvalues (ginibreOnSequence N ω))

theorem ginibreLogPotential_of_finiteFormulas (h : GinibreFiniteFormulaInput) :
    GinibreLogPotentialInput := by
  intro N hNpos hN z
  exact BC12.ginibre_matrix_logdet_convergesInProbability_of_formulas hNpos hN
    (fun n => ginibreOnSequence (N n))
    (fun n => h.projection (N n) (hNpos n))
    (fun n => h.correlation (N n) (hNpos n)) z

theorem bc12_of_bbv_and_finiteFormulas
    (hBBV : BBVComparisonInput) (h : GinibreFiniteFormulaInput) :
    CircularLawSections56.Section5.PublishedSection3Concrete.BC12GinibreInput :=
  bc12_of_bbv_and_logPotential hBBV (ginibreLogPotential_of_finiteFormulas h)

end CircularLawSection6
