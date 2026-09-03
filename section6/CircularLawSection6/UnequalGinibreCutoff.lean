import CircularLawSection6.UnequalGinibreComparison
import CircularLawSection6.PublishedCyclicGinibre
import CircularLawSection6.GinibreReferenceSources
import CircularLawSection6.CoupledCdfComparison

/-! # Fixed positive cutoffs for two unrelated Ginibre dimensions

Only BBV is used as a comparison source. The same infinite Gaussian array
couples the finite laws; the matrix identities and measure-preserving maps
are the existing cyclic Ginibre construction. The common exceptional set
of shifts is selected over all positive dimensions before any sequences
are quantified. There is no limiting singular-value law premise.
-/

open MeasureTheory Filter Topology ShortRingAnchor
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete
  (BBVComparisonInput gaussianSequenceLaw ginibreOnSequence)
open CircularLawSection6.GinibreReferenceSources
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem cyclicSamples_unequal_cdf (M N : ℕ) [NeZero M] [NeZero N]
    (ω : ℕ → ℂ) (z : ℂ) (R : ℝ) :
    matrixSquaredSingularCdfDistanceOn
      (ginibreMatrix M (cyclicSamples M ω) - z • 1)
      (ginibreMatrix N (cyclicSamples N ω) - z • 1) R =
    matrixSquaredSingularCdfDistanceOn
      (ginibreOnSequence M ω - z • 1) (ginibreOnSequence N ω - z • 1) R := by
  rw [← cyclicSamples_matrix M ω, ← cyclicSamples_matrix N ω]
  unfold matrixSquaredSingularCdfDistanceOn empiricalCdfDistanceOn
  simp_rw [matrixSquaredSingularCdf_eq_average,
    matrixSquaredSingularAverage_shifted_reindex (ZMod.finEquiv M).toEquiv.symm,
    matrixSquaredSingularAverage_shifted_reindex (ZMod.finEquiv N).toEquiv.symm]

/-- The target expectations are on the original finite cyclic laws, not
on a renamed or hypothesized limiting law. The conclusion is uniform in
the choice of dimension sequences on one full-measure set of shifts. -/
theorem unequal_ginibre_cutoff_of_bbv_ae (hBBV : BBVComparisonInput) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ M N : ℕ → ℕ+,
      Tendsto (fun n => (M n : ℕ)) atTop atTop →
      Tendsto (fun n => (N n : ℕ)) atTop atTop →
      ∀ a : ℝ, 0 < a →
      Tendsto (fun n =>
        (∫ ω, matrixCutoffPotential (ginibreMatrix (M n) ω - z • 1) a
          ∂cyclicAtomLaw (M n) circularComplexGaussian) -
        ∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) a
          ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 0) := by
  have hdet : ∀ᵐ z ∂(volume : Measure ℂ), ∀ m : ℕ+,
      ∀ᵐ ω ∂cyclicAtomLaw (m : ℕ) circularComplexGaussian,
        (ginibreMatrix (m : ℕ) ω - z • 1).det ≠ 0 :=
    ae_all_iff.2 (fun m => ae_shifted_matrix_det_ne_zero _ (ginibreMatrix (m : ℕ))
      (ginibreMatrix_measurable _))
  filter_upwards [hdet] with z hz
  intro M N hM hN a ha
  have hcdf (R : ℝ) (hR : 1 ≤ R) :
      TendstoInProbabilityTri (fun _ => gaussianSequenceLaw)
        (fun n ω => matrixSquaredSingularCdfDistanceOn
          (ginibreMatrix (M n) (cyclicSamples (M n) ω) - z • 1)
          (ginibreMatrix (N n) (cyclicSamples (N n) ω) - z • 1) R) 0 := by
    simpa only [cyclicSamples_unequal_cdf] using
      unequal_ginibre_cdf_of_bbv hBBV (fun n => (M n : ℕ)) (fun n => (N n : ℕ))
        (fun n => (M n).pos) (fun n => (N n).pos) hM hN z (zero_le_one.trans hR)
  exact matrixCutoff_expectation_difference_of_coupled_cdf
    (fun n => cyclicAtomLaw (M n) circularComplexGaussian)
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun _ => gaussianSequenceLaw)
    (fun n => cyclicSamples (M n)) (fun n => cyclicSamples (N n))
    (fun n => cyclicSamples_measurePreserving (M n))
    (fun n => cyclicSamples_measurePreserving (N n))
    (fun n ω => ginibreMatrix (M n) ω - z • 1)
    (fun n ω => ginibreMatrix (N n) ω - z • 1)
    (fun n => (ginibreMatrix_measurable (M n)).sub measurable_const)
    (fun n => (ginibreMatrix_measurable (N n)).sub measurable_const)
    (fun n => hz (M n)) (fun n => hz (N n))
    (fun n => (ginibre_shifted_expected_energy (M n) z).1)
    (fun n => (ginibre_shifted_expected_energy (N n) z).1)
    (2 + 2 * ‖z‖ ^ 2) (2 + 2 * ‖z‖ ^ 2)
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (M n) z).2)
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (N n) z).2)
    hcdf ha

end CircularLawSection6
