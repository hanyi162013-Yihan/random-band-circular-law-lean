import CircularLawSection6.CoupledCdfComparison
import CircularLawSection6.GinibreReference

/-! # Actual routed Gaussian bands compared with finite Ginibre

The source CDF observable is evaluated on the independent product of the
two concrete finite sample laws. Normalized energies, shifted matrix
measurability and planar-a.e. nonsingularity are all discharged here.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem routed_gaussian_cutoff_comparison_ae
    {ι κ : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    [∀ n, Nonempty (ι n)] [∀ n, Fintype (κ n)]
    (route : ∀ n, ι n → κ n → ι n) (hroute : ∀ n i, Function.Injective (route n i))
    (b : ∀ n, κ n → ℂ) (hb : ∀ n, ∑ s, ‖b n s‖ ^ 2 = 1)
    (M : ℕ → ℕ) [∀ n, NeZero (M n)] :
    ∀ᵐ z ∂(volume : Measure ℂ),
      (∀ R : ℝ, 1 ≤ R → TendstoInProbabilityTri
        (fun n => (Measure.pi (fun _ : ι n × κ n => circularComplexGaussian)).prod
          (cyclicAtomLaw (M n) circularComplexGaussian))
        (fun n ω => matrixSquaredSingularCdfDistanceOn
          (routedBandMatrix (route n) (b n) ω.1 - z • 1) (ginibreMatrix (M n) ω.2 - z • 1) R) 0) →
      ∀ a : ℝ, 0 < a →
        Tendsto (fun n =>
          (∫ ω, matrixCutoffPotential (routedBandMatrix (route n) (b n) ω - z • 1) a
            ∂Measure.pi (fun _ : ι n × κ n => circularComplexGaussian)) -
          ∫ ω, matrixCutoffPotential (ginibreMatrix (M n) ω - z • 1) a
            ∂cyclicAtomLaw (M n) circularComplexGaussian) atTop (𝓝 0) := by
  let μ (n : ℕ) := Measure.pi (fun _ : ι n × κ n => circularComplexGaussian)
  let ν (n : ℕ) := cyclicAtomLaw (M n) circularComplexGaussian
  have hAr (n : ℕ) := routedBandMatrix_measurable (route n) (b n)
  have hdetA := ae_all_iff.2 (fun n => ae_shifted_matrix_det_ne_zero (μ n)
    (routedBandMatrix (route n) (b n)) (hAr n))
  have hdetB := ae_all_iff.2 (fun n => ae_shifted_matrix_det_ne_zero (ν n)
    (ginibreMatrix (M n)) (ginibreMatrix_measurable (M n)))
  have henergy (n : ℕ) := routedBand_expected_energy (route n) (hroute n) (b n) (hb n)
    circularComplexGaussian circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment
  filter_upwards [hdetA, hdetB] with z hzA hzB
  intro hcdf a ha
  have heA (n : ℕ) := expected_shifted_scaled_energy_le (μ n)
    (routedBandMatrix (route n) (b n)) (hAr n) (henergy n).1 (henergy n).2 (1 : ℂ) z
  simp only [one_smul, norm_one, one_pow, mul_one] at heA
  exact matrixCutoff_expectation_difference_of_coupled_cdf μ ν (fun n => (μ n).prod (ν n))
    (fun _ => Prod.fst) (fun _ => Prod.snd)
    (fun _ => measurePreserving_fst) (fun _ => measurePreserving_snd)
    (fun n ω => routedBandMatrix (route n) (b n) ω - z • 1)
    (fun n ω => ginibreMatrix (M n) ω - z • 1)
    (fun n => (hAr n).sub measurable_const) (fun n => (ginibreMatrix_measurable (M n)).sub measurable_const)
    hzA hzB (fun n => (heA n).1) (fun n => (ginibre_shifted_expected_energy (M n) z).1)
    (2 + 2 * ‖z‖ ^ 2) (2 + 2 * ‖z‖ ^ 2) (fun n => (heA n).2)
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (M n) z).2) hcdf ha

theorem ginibre_fixedCutoff_mean_of_squared_test_ae
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ σ : Measure ℝ, IsProbabilityMeasure σ →
      (∀ᵐ s ∂σ, 0 ≤ s) → Integrable (fun s : ℝ => s ^ 2) σ →
      (∀ φ : ℝ → ℝ, Continuous φ → (∃ B : ℝ, ∀ x, |φ x| ≤ B) →
        TendstoInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
          (fun n ω => matrixSquaredSingularAverage (ginibreMatrix (N n) ω - z • 1) φ)
          (∫ s, φ (s ^ 2) ∂σ)) →
      ∀ a : ℝ, 0 < a →
        Tendsto (fun n => ∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) a
          ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 (∫ s, Real.log (max s a) ∂σ)) := by
  have hdet := ae_all_iff.2 (fun n => ae_shifted_matrix_det_ne_zero
    (cyclicAtomLaw (N n) circularComplexGaussian) (ginibreMatrix (N n)) (ginibreMatrix_measurable (N n)))
  filter_upwards [hdet] with z hz
  intro σ hσ hσpos hσ2 hweak a ha
  let : IsProbabilityMeasure σ := hσ
  exact matrixCutoff_expectation_of_squared_singular_probability
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun n ω => ginibreMatrix (N n) ω - z • 1)
    (fun n => (ginibreMatrix_measurable (N n)).sub measurable_const) hz
    (fun n => (ginibre_shifted_expected_energy (N n) z).1) (2 + 2 * ‖z‖ ^ 2)
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (N n) z).2)
    σ hσpos hσ2 hweak ha

end CircularLawSection6
