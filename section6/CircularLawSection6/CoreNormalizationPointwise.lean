import CircularLawSection6.CanonicalCoreLimits
import CircularLawSection6.CutoffPointwiseExtension

/-! # Pointwise cutoff normalization for Gaussian cores -/

open MeasureTheory Filter Topology TaoVuReplacement

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

theorem gaussian_core_cutoff_normalization_error_at (p : NoncompactProfile)
    (N H : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ) {v a : ℝ}
    (hv : 0 < v)
    (hmass : Tendsto (fun n => p.coreMass (N n) (H n) (W n)) atTop (𝓝 v))
    (ha : 0 < a) (z : ℂ) :
    Tendsto (fun n =>
      |(∫ ω, matrixCutoffPotential (p.coreMatrix (N n) (H n) (W n) ω - z • 1) a
        ∂gaussianProfileLaw (N n)) -
      ∫ ω, matrixCutoffPotential ((Real.sqrt v : ℂ) •
        p.unitCoreMatrix (N n) (H n) (W n) ω - z • 1) a
        ∂gaussianProfileLaw (N n)|) atTop (𝓝 0) := by
  let F : ℕ → ℂ → ℝ := fun n u =>
    (∫ ω, matrixCutoffPotential (p.coreMatrix (N n) (H n) (W n) ω - u • 1) a
      ∂gaussianProfileLaw (N n)) -
    ∫ ω, matrixCutoffPotential ((Real.sqrt v : ℂ) •
      p.unitCoreMatrix (N n) (H n) (W n) ω - u • 1) a
      ∂gaussianProfileLaw (N n)
  have hAE : ∀ᵐ u ∂(volume : Measure ℂ), Tendsto (fun n => F n u) atTop (𝓝 0) := by
    filter_upwards [p.gaussian_core_cutoff_normalization_error N H W hmass ha] with u hu
    apply tendsto_zero_iff_norm_tendsto_zero.2
    simpa only [F, Real.norm_eq_abs] using hu
  have hroot : (Real.sqrt v : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hv).ne'
  have hLip (n : ℕ) (u w : ℂ) : |F n u - F n w| ≤ (2 / a) * dist u w := by
    have hmcore : Measurable (p.coreMatrix (N n) (H n) (W n)) :=
      weightedCyclicMatrix_measurable_matrix _ _
    have hEcore := integrable_hilbertSchmidtSq_of_cyclicEnergy
      (gaussianProfileLaw (N n)) (N n) (p.coreMatrix (N n) (H n) (W n))
      (p.gaussian_expected_core_energy (N n) (H n) (W n)).1
    have hp := expected_matrixCutoff_shift_lipschitz (gaussianProfileLaw (N n))
      (p.coreMatrix (N n) (H n) (W n)) hmcore
      (fun x => p.gaussian_core_det_nonzero (N n) (H n) (W n) x) hEcore ha u w
    let B := fun ω => (Real.sqrt v : ℂ) • p.unitCoreMatrix (N n) (H n) (W n) ω
    have hmB : Measurable B :=
      (weightedCyclicMatrix_measurable_matrix _ _).const_smul (Real.sqrt v : ℂ)
    have hEB : Integrable (fun ω => hilbertSchmidtSq (B ω)) (gaussianProfileLaw (N n)) :=
      integrable_hilbertSchmidtSq_smul _ _
        (integrable_hilbertSchmidtSq_of_cyclicEnergy
          (gaussianProfileLaw (N n)) (N n) (p.unitCoreMatrix (N n) (H n) (W n))
          (p.gaussian_expected_unitCore_energy (N n) (H n) (W n)).1) _
    have hdetB (x : ℂ) : ∀ᵐ ω ∂gaussianProfileLaw (N n), (B ω - x • 1).det ≠ 0 := by
      filter_upwards [p.gaussian_unitCore_det_nonzero (N n) (H n) (W n)
        (x / (Real.sqrt v : ℂ))] with ω hω
      have heq : B ω - x • 1 = (Real.sqrt v : ℂ) •
          (p.unitCoreMatrix (N n) (H n) (W n) ω -
            (x / (Real.sqrt v : ℂ)) • 1) := by
        dsimp only [B]
        rw [smul_sub, smul_smul]
        congr 2
        field_simp
      rw [heq, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ hroot) hω
    have hg := expected_matrixCutoff_shift_lipschitz (gaussianProfileLaw (N n))
      B hmB hdetB hEB ha u w
    dsimp only [F]
    calc
      |_ - _| = |((∫ ω, matrixCutoffPotential
          (p.coreMatrix (N n) (H n) (W n) ω - u • 1) a
          ∂gaussianProfileLaw (N n)) -
        ∫ ω, matrixCutoffPotential
          (p.coreMatrix (N n) (H n) (W n) ω - w • 1) a
          ∂gaussianProfileLaw (N n)) -
        ((∫ ω, matrixCutoffPotential (B ω - u • 1) a
          ∂gaussianProfileLaw (N n)) -
        ∫ ω, matrixCutoffPotential (B ω - w • 1) a
          ∂gaussianProfileLaw (N n))| := by
        dsimp only [B]
        ring
      _ ≤ ‖u - w‖ / a + ‖u - w‖ / a := (abs_sub _ _).trans (add_le_add hp hg)
      _ = (2 / a) * dist u w := by rw [dist_eq]; ring
  have hF := tendsto_zero_everywhere_of_ae_lipschitz F (2 / a)
    (by positivity) hAE hLip z
  simpa only [F, Real.norm_eq_abs] using hF.norm

end CircularLawSection6.NoncompactProfile
