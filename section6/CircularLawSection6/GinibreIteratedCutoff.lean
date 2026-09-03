import CircularLawSection6.GinibreLowerCutoff
import CircularLawSection6.IteratedLowerCutoff

/-! # Concrete Ginibre cutoff control with size before cutoff

The BC12 probability inputs yield the actual expected lower-cutoff error
in the order needed for the noncompact-profile argument. No limiting
singular law or quantitative hard-edge density is assumed here.
-/

open MeasureTheory ProbabilityTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem ginibre_iterated_cutoff_error_ae (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ target : ℝ,
      TendstoInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
        (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1)) target →
      ∀ p : ℝ, 0 < p → BC12GinibreNegativeMomentTightnessTri N z p →
      ∀ a : ℕ → ℝ, (∀ R, 0 < a R) → (∀ R, a R ≤ 1) → Tendsto a atTop (𝓝 0) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ R in atTop, ∀ᶠ n in atTop,
        (∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) (a R)
          ∂cyclicAtomLaw (N n) circularComplexGaussian) ≤
        (∫ ω, matrixRawPotential (ginibreMatrix (N n) ω - z • 1)
          ∂cyclicAtomLaw (N n) circularComplexGaussian) + ε := by
  have hdet := ae_all_iff.2 (fun n => ae_shifted_matrix_det_ne_zero
    (cyclicAtomLaw (N n) circularComplexGaussian) (ginibreMatrix (N n)) (ginibreMatrix_measurable (N n)))
  filter_upwards [hdet] with z hz
  intro target hprob p hp hnegative a ha ha1 ha0 ε hε
  obtain ⟨C, hC⟩ := exists_uniform_secondMoment_of_mean_variance
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian) _
    (fun n => ginibre_raw_memLp (N n) z)
    (ginibre_raw_mean_of_probability N hN z hprob) (ginibre_raw_variance_tendsto N hN z)
  have herr := matrixLowerCutoff_iterated_L1_of_negativeMoment
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun n ω => ginibreMatrix (N n) ω - z • 1)
    (fun n => (ginibreMatrix_measurable (N n)).sub measurable_const) hz
    (fun n => (ginibre_shifted_expected_energy (N n) z).1)
    (fun n => ginibre_raw_memLp (N n) z) (2 + 2 * ‖z‖ ^ 2) C
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (N n) z).2)
    hC hp hnegative a ha ha1 ha0 ε hε
  filter_upwards [herr] with R hR
  filter_upwards [hR] with n hn
  have hiRaw := (ginibre_raw_memLp (N n) z).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hiCut := integrable_matrixCutoffPotential
    (cyclicAtomLaw (N n) circularComplexGaussian) (fun ω => ginibreMatrix (N n) ω - z • 1)
    ((ginibreMatrix_measurable (N n)).sub measurable_const) (hz n)
    (ginibre_shifted_expected_energy (N n) z).1 (ha R)
  have h := (le_abs_self (∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) (a R) -
    matrixRawPotential (ginibreMatrix (N n) ω - z • 1) ∂cyclicAtomLaw (N n) circularComplexGaussian)).trans
      abs_integral_le_integral_abs
  rw [integral_sub hiCut hiRaw] at h
  linarith

end CircularLawSection6
