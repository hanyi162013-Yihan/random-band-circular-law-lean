import CircularLawSection6.BBVCoreSources
import CircularLawSection6.CutoffPointwiseExtension

/-! # Fixed-shift canonical core cutoff comparison

The BBV/Cook comparison is reused exactly as proved on a planar full-measure
set.  Positive-cutoff expectations for both the unit core and Ginibre are
uniformly Lipschitz in the spectral parameter, so density of that set extends
the comparison to every prescribed `z`.
-/

open MeasureTheory Filter Topology TaoVuReplacement ShortRingAnchor
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput)

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6
namespace CoreRadiusBounds

variable {p : NoncompactProfile} {R : ℝ}

theorem canonical_core_cutoff_comparison_of_bbv_at (B : CoreRadiusBounds p R)
    (hBBV : BBVComparisonInput)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (N n : ℝ)) atTop (𝓝 0))
    (hR : 0 < R) {a : ℝ} (ha : 0 < a) (z : ℂ) :
    Tendsto (fun n =>
      (∫ ω, matrixCutoffPotential
        (p.unitCoreMatrix (N n) ⌊R * W n⌋₊ (W n) ω - z • 1) a
        ∂gaussianProfileLaw (N n)) -
      ∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) a
        ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 0) := by
  let F : ℕ → ℂ → ℝ := fun n u =>
    (∫ ω, matrixCutoffPotential
      (p.unitCoreMatrix (N n) ⌊R * W n⌋₊ (W n) ω - u • 1) a
      ∂gaussianProfileLaw (N n)) -
    ∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - u • 1) a
      ∂cyclicAtomLaw (N n) circularComplexGaussian
  have hAE : ∀ᵐ u ∂(volume : Measure ℂ), Tendsto (fun n => F n u) atTop (𝓝 0) := by
    simpa only [F] using B.canonical_core_cutoff_comparison_of_bbv hBBV N hN W hW hWlim
      hsparse hR ha
  have hLip (n : ℕ) (u v : ℂ) : |F n u - F n v| ≤ (2 / a) * dist u v := by
    have hm : Measurable (p.unitCoreMatrix (N n) ⌊R * W n⌋₊ (W n)) :=
      weightedCyclicMatrix_measurable_matrix _ _
    have hEU := integrable_hilbertSchmidtSq_of_cyclicEnergy
      (gaussianProfileLaw (N n)) (N n)
      (p.unitCoreMatrix (N n) ⌊R * W n⌋₊ (W n))
      (p.gaussian_expected_unitCore_energy (N n) ⌊R * W n⌋₊ (W n)).1
    have hp := expected_matrixCutoff_shift_lipschitz
      (gaussianProfileLaw (N n))
      (p.unitCoreMatrix (N n) ⌊R * W n⌋₊ (W n)) hm
      (fun w => p.gaussian_unitCore_det_nonzero (N n) ⌊R * W n⌋₊ (W n) w)
      hEU ha u v
    have hg := expected_matrixCutoff_shift_lipschitz
      (cyclicAtomLaw (N n) circularComplexGaussian) (ginibreMatrix (N n))
      (ginibreMatrix_measurable (N n)) (fun w => ginibre_shifted_det_ne_zero (N n) w)
      (ginibre_expected_energy (N n)).1 ha u v
    dsimp only [F]
    calc
      |_ - _| = |((∫ ω, matrixCutoffPotential
          (p.unitCoreMatrix (N n) ⌊R * W n⌋₊ (W n) ω - u • 1) a
          ∂gaussianProfileLaw (N n)) -
        ∫ ω, matrixCutoffPotential
          (p.unitCoreMatrix (N n) ⌊R * W n⌋₊ (W n) ω - v • 1) a
          ∂gaussianProfileLaw (N n)) -
        ((∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - u • 1) a
          ∂cyclicAtomLaw (N n) circularComplexGaussian) -
        ∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - v • 1) a
          ∂cyclicAtomLaw (N n) circularComplexGaussian)| := by ring_nf
      _ ≤ ‖u - v‖ / a + ‖u - v‖ / a := (abs_sub _ _).trans (add_le_add hp hg)
      _ = (2 / a) * dist u v := by rw [dist_eq_norm]; ring
  simpa only [F] using tendsto_zero_everywhere_of_ae_lipschitz F (2 / a)
    (by positivity) hAE hLip z

end CoreRadiusBounds
end CircularLawSection6
