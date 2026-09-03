import CircularLawSection6.VaryingCoreCutoff

/-! # The full raw mean is bounded by the unit-core cutoff

The normalization is compared directly to variance one. The exact finite
error is `(sqrt(tailMass) + |sqrt(coreMass)-1|)/a`. Consequently the
reference in the final squeeze can remain the variance-one Ginibre model
at the same spectral parameter throughout.
-/

open MeasureTheory

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

theorem gaussian_expected_unitCore_upper_ae (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ a : ℝ, 0 < a →
      (∫ ω, p.rawCoreLogDet N H W z ω ∂gaussianProfileLaw N) / (N : ℝ) ≤
        (∫ ω, p.rawProfileLogDet N W z ω ∂gaussianProfileLaw N) / (N : ℝ) ∧
      (∫ ω, p.rawProfileLogDet N W z ω ∂gaussianProfileLaw N) / (N : ℝ) ≤
        (∫ ω, matrixCutoffPotential (p.unitCoreMatrix N H W ω - z • 1) a ∂gaussianProfileLaw N) +
          (Real.sqrt (p.tailMass N H W) + |Real.sqrt (p.coreMass N H W) - 1|) / a := by
  filter_upwards [p.gaussian_expected_core_full_cutoff_sandwich_ae N H W,
    p.gaussian_unitCore_cutoff_scaling_ae N H W (Real.sqrt (p.coreMass N H W)) 1] with z hz hs
  intro a ha
  obtain ⟨hi, hj, hb⟩ := hs a ha
  have hcmp : (∫ ω, matrixCutoffPotential (p.coreMatrix N H W ω - z • 1) a ∂gaussianProfileLaw N) -
      (∫ ω, matrixCutoffPotential (p.unitCoreMatrix N H W ω - z • 1) a ∂gaussianProfileLaw N) ≤
        |Real.sqrt (p.coreMass N H W) - 1| / a := by
    have h := (le_abs_self (∫ ω, matrixCutoffPotential
      ((Real.sqrt (p.coreMass N H W) : ℂ) • p.unitCoreMatrix N H W ω - z • 1) a -
      matrixCutoffPotential ((1 : ℂ) • p.unitCoreMatrix N H W ω - z • 1) a ∂gaussianProfileLaw N)).trans
        (abs_integral_le_integral_abs.trans hb)
    rw [integral_sub hi hj] at h
    simpa only [← p.coreMatrix_eq_scale_unitCoreMatrix, Complex.ofReal_one, one_smul] using h
  refine ⟨(hz a ha).2.1, ?_⟩
  have hu := (hz a ha).2.2
  rw [add_div]
  linarith

theorem gaussian_expected_unitCore_upper_triangular (p : NoncompactProfile)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ n H, ∀ a : ℝ, 0 < a →
      (∫ ω, p.rawCoreLogDet (N n) H (W n) z ω ∂gaussianProfileLaw (N n)) / (N n : ℝ) ≤
        (∫ ω, p.rawProfileLogDet (N n) (W n) z ω ∂gaussianProfileLaw (N n)) / (N n : ℝ) ∧
      (∫ ω, p.rawProfileLogDet (N n) (W n) z ω ∂gaussianProfileLaw (N n)) / (N n : ℝ) ≤
        (∫ ω, matrixCutoffPotential (p.unitCoreMatrix (N n) H (W n) ω - z • 1) a
          ∂gaussianProfileLaw (N n)) +
          (Real.sqrt (p.tailMass (N n) H (W n)) + |Real.sqrt (p.coreMass (N n) H (W n)) - 1|) / a :=
  ae_all_iff.2 (fun n => ae_all_iff.2 (fun H => p.gaussian_expected_unitCore_upper_ae (N n) H (W n)))

end CircularLawSection6.NoncompactProfile
