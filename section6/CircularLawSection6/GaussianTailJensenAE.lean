import CircularLawSection6.GaussianTailJensen
import CircularLawSection6.ReusedLogDetIntegrability

/-! # Closing the expected tail Jensen inequality by reuse

The Section 5 / replacement estimates discharge every integrability and
nonvanishing input for planar almost every spectral parameter. The final
theorem here has only the actual noncompact profile and finite-size data as
inputs. It is not the stronger, unnecessary assertion for every fixed `z`.
-/

open MeasureTheory

noncomputable section

namespace CircularLawSection6.NoncompactProfile

theorem gaussian_rawProfileLogDet_integrable_ae (p : NoncompactProfile)
    (N : ℕ) [NeZero N] (W : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ), Integrable (p.rawProfileLogDet N W z) (gaussianProfileLaw N) := by
  apply ae_cyclic_rawLogDet_integrable (gaussianProfileLaw N) N (p.matrix N W)
  · intro i j
    exact measurable_const.mul (measurable_pi_apply (i, j - i))
  · exact (p.gaussian_expected_energy N W).1

theorem gaussian_rawCoreLogDet_integrable_ae (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ), Integrable (p.rawCoreLogDet N H W z) (gaussianProfileLaw N) := by
  apply ae_cyclic_rawLogDet_integrable (gaussianProfileLaw N) N (p.coreMatrix N H W)
  · intro i j
    exact measurable_const.mul (measurable_pi_apply (i, j - i))
  · exact (p.gaussian_expected_core_energy N H W).1

theorem gaussian_core_det_nonzero_ae (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ ω ∂gaussianProfileLaw N,
      (p.coreMatrix N H W ω - z • 1).det ≠ 0 := by
  apply ae_shifted_cyclic_det_ne_zero (gaussianProfileLaw N) N (p.coreMatrix N H W)
  intro i j
  exact measurable_const.mul (measurable_pi_apply (i, j - i))

/-- Literal expected tail Jensen inequality with no remaining logarithmic
integrability or determinant-nonvanishing hypothesis. -/
theorem gaussian_expected_tail_jensen_ae (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      (∫ ω, p.rawCoreLogDet N H W z ω ∂gaussianProfileLaw N) / (N : ℝ) ≤
        (∫ ω, p.rawProfileLogDet N W z ω ∂gaussianProfileLaw N) / (N : ℝ) := by
  filter_upwards [p.gaussian_rawProfileLogDet_integrable_ae N W,
    p.gaussian_rawCoreLogDet_integrable_ae N H W, p.gaussian_core_det_nonzero_ae N H W]
    with z hfull hcore hdet
  exact p.gaussian_expected_tail_jensen N H W z hfull hcore hdet

/-- One common planar full-measure set works for all sizes and all integer
core radii, including radii subsequently chosen as functions of size. -/
theorem gaussian_expected_tail_jensen_triangular (p : NoncompactProfile)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ n H,
      (∫ ω, p.rawCoreLogDet (N n) H (W n) z ω ∂gaussianProfileLaw (N n)) / (N n : ℝ) ≤
        (∫ ω, p.rawProfileLogDet (N n) (W n) z ω ∂gaussianProfileLaw (N n)) / (N n : ℝ) :=
  ae_all_iff.2 (fun n => ae_all_iff.2 (fun H => p.gaussian_expected_tail_jensen_ae (N n) H (W n)))

end CircularLawSection6.NoncompactProfile
