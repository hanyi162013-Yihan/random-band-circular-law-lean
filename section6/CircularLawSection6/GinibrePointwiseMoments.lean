import CircularLawSection6.GinibrePointwiseNonzero
import CircularLawSection6.GinibreLogMomentBounds

/-! # Pointwise-in-shift Ginibre moment and lower-cutoff estimates

The fixed-shift small-ball nonsingularity result replaces the generic
planar-a.e. parameter argument. All other ingredients are the proved BBV
negative moments, exact Gaussian energies, and centered concentration.
No raw logarithmic-potential limit is an input.
-/

open MeasureTheory Filter Topology ShortRingAnchor
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem ginibre_raw_tight_of_bbv (hBBV : BBVComparisonInput)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop) (z : ℂ) :
    BoundedInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
      (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1)) :=
  matrixRawPotential_boundedInProbabilityTri_of_energy_negativeMoment
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun n ω => ginibreMatrix (N n) ω - z • 1)
    (fun n => ginibre_shifted_det_ne_zero (N n) z)
    (fun n => (ginibre_shifted_expected_energy (N n) z).1) (2 + 2 * ‖z‖ ^ 2)
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (N n) z).2)
    (by norm_num : (0 : ℝ) < 1 / 128) (ginibre_negative_of_bbv hBBV N hN z)

theorem ginibre_raw_uniform_secondMoment_of_bbv (hBBV : BBVComparisonInput)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop) (z : ℂ) :
    ∃ C : ℝ, ∀ n,
      (∫ ω, matrixRawPotential (ginibreMatrix (N n) ω - z • 1) ^ 2
        ∂cyclicAtomLaw (N n) circularComplexGaussian) ≤ C :=
  exists_uniform_secondMoment_of_tight_and_centered
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1))
    (fun n => ginibre_raw_memLp (N n) z) (ginibre_raw_tight_of_bbv hBBV N hN z)
    (ginibre_raw_centered_tendsto N hN z) (ginibre_raw_variance_tendsto N hN z)

theorem ginibreLowerCutoff_L1_of_bbv (hBBV : BBVComparisonInput)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop) (z : ℂ)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,
      |matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) (a n) -
        matrixRawPotential (ginibreMatrix (N n) ω - z • 1)|
      ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := ginibre_raw_uniform_secondMoment_of_bbv hBBV N hN z
  exact matrixLowerCutoff_L1_of_negativeMoment
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun n ω => ginibreMatrix (N n) ω - z • 1)
    (fun n => (ginibreMatrix_measurable (N n)).sub measurable_const)
    (fun n => ginibre_shifted_det_ne_zero (N n) z)
    (fun n => (ginibre_shifted_expected_energy (N n) z).1)
    (fun n => ginibre_raw_memLp (N n) z) (2 + 2 * ‖z‖ ^ 2) C
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (N n) z).2)
    hC (by norm_num : (0 : ℝ) < 1 / 128) (ginibre_negative_of_bbv hBBV N hN z)
    a ha ha1 ha0

theorem ginibre_iterated_lowerCutoff_L1_of_bbv (hBBV : BBVComparisonInput)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop) (z : ℂ)
    (a : ℕ → ℝ) (ha : ∀ R, 0 < a R) (ha1 : ∀ R, a R ≤ 1)
    (ha0 : Tendsto a atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ R in atTop, ∀ᶠ n in atTop,
      (∫ ω, |matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) (a R) -
        matrixRawPotential (ginibreMatrix (N n) ω - z • 1)|
        ∂cyclicAtomLaw (N n) circularComplexGaussian) < ε := by
  obtain ⟨C, hC⟩ := ginibre_raw_uniform_secondMoment_of_bbv hBBV N hN z
  exact matrixLowerCutoff_iterated_L1_of_negativeMoment
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun n ω => ginibreMatrix (N n) ω - z • 1)
    (fun n => (ginibreMatrix_measurable (N n)).sub measurable_const)
    (fun n => ginibre_shifted_det_ne_zero (N n) z)
    (fun n => (ginibre_shifted_expected_energy (N n) z).1)
    (fun n => ginibre_raw_memLp (N n) z) (2 + 2 * ‖z‖ ^ 2) C
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (N n) z).2)
    hC (by norm_num : (0 : ℝ) < 1 / 128) (ginibre_negative_of_bbv hBBV N hN z)
    a ha ha1 ha0

end CircularLawSection6
