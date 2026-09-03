import CircularLawSection6.GinibreReference
import CircularLawSection6.NegativeMomentCutoff

/-! # BC12 inputs close the concrete Ginibre lower-cutoff expectation

The inputs are the raw log-potential probability limit and tightness of
one negative empirical singular moment, both on the actual normalized
Ginibre model. The energy and uniform logarithmic second moments are
derived, not included in the source interface.
-/

open MeasureTheory ProbabilityTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

def BC12GinibreNegativeMomentTightnessTri (N : ℕ → ℕ) [∀ n, NeZero (N n)] (z : ℂ) (p : ℝ) : Prop :=
  BoundedInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun n ω => matrixNegativeMoment (ginibreMatrix (N n) ω - z • 1) p)

theorem ginibreLowerCutoff_L1_ae (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ target : ℝ,
      TendstoInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
        (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1)) target →
      ∀ p : ℝ, 0 < p → BC12GinibreNegativeMomentTightnessTri N z p →
      ∀ a : ℕ → ℝ, (∀ n, 0 < a n) → (∀ n, a n ≤ 1) → Tendsto a atTop (𝓝 0) →
      Tendsto (fun n => ∫ ω,
        |matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) (a n) -
          matrixRawPotential (ginibreMatrix (N n) ω - z • 1)|
        ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 0) := by
  have hdet := ae_all_iff.2 (fun n => ae_shifted_matrix_det_ne_zero
    (cyclicAtomLaw (N n) circularComplexGaussian) (ginibreMatrix (N n)) (ginibreMatrix_measurable (N n)))
  filter_upwards [hdet] with z hz
  intro target hprob p hp hnegative a ha ha1 ha0
  obtain ⟨C, hC⟩ := exists_uniform_secondMoment_of_mean_variance
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian) _
    (fun n => ginibre_raw_memLp (N n) z)
    (ginibre_raw_mean_of_probability N hN z hprob) (ginibre_raw_variance_tendsto N hN z)
  exact matrixLowerCutoff_L1_of_negativeMoment
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun n ω => ginibreMatrix (N n) ω - z • 1)
    (fun n => (ginibreMatrix_measurable (N n)).sub measurable_const) hz
    (fun n => (ginibre_shifted_expected_energy (N n) z).1)
    (fun n => ginibre_raw_memLp (N n) z) (2 + 2 * ‖z‖ ^ 2) C
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (N n) z).2)
    hC hp hnegative a ha ha1 ha0

theorem ginibre_vanishingCutoff_mean_ae (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ target : ℝ,
      TendstoInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
        (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1)) target →
      ∀ p : ℝ, 0 < p → BC12GinibreNegativeMomentTightnessTri N z p →
      ∀ a : ℕ → ℝ, (∀ n, 0 < a n) → (∀ n, a n ≤ 1) → Tendsto a atTop (𝓝 0) →
      Tendsto (fun n => ∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) (a n)
        ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 target) := by
  have hdet := ae_all_iff.2 (fun n => ae_shifted_matrix_det_ne_zero
    (cyclicAtomLaw (N n) circularComplexGaussian) (ginibreMatrix (N n)) (ginibreMatrix_measurable (N n)))
  filter_upwards [ginibreLowerCutoff_L1_ae N hN, hdet] with z hz hdz
  intro target hprob p hp hnegative a ha ha1 ha0
  have hiRaw (n : ℕ) := (ginibre_raw_memLp (N n) z).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hiCut (n : ℕ) := integrable_matrixCutoffPotential
    (cyclicAtomLaw (N n) circularComplexGaussian) (fun ω => ginibreMatrix (N n) ω - z • 1)
    ((ginibreMatrix_measurable (N n)).sub measurable_const) (hdz n)
    (ginibre_shifted_expected_energy (N n) z).1 (ha n)
  have hdiff : Tendsto (fun n => (∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) (a n)
      ∂cyclicAtomLaw (N n) circularComplexGaussian) -
      ∫ ω, matrixRawPotential (ginibreMatrix (N n) ω - z • 1)
        ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (hz target hprob p hp hnegative a ha ha1 ha0)
    rw [← integral_sub (hiCut n) (hiRaw n), Real.norm_eq_abs]
    exact abs_integral_le_integral_abs
  simpa only [sub_add_cancel, zero_add] using hdiff.add (ginibre_raw_mean_of_probability N hN z hprob)

end CircularLawSection6
