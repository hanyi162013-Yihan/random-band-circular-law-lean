import CircularLawSection6.ExpectedCutoffComparison
import CircularLawSection6.GaussianTailJensenAE

/-! # The literal core/tail cutoff error

The already proved expected tail energy, a.e.-parameter nonsingularity,
and actual finite-matrix cutoff comparison give exactly `sqrt(tailMass)/a`.
No matrix-comparison or cutoff-integrability input remains.
-/

open MeasureTheory
open TaoVuReplacement

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

theorem shifted_full_sub_core (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) (z : ℂ) (ω : ZMod N × ZMod N → ℂ) :
    (p.matrix N W ω - z • 1) - (p.coreMatrix N H W ω - z • 1) = p.tailMatrix N H W ω := by
  rw [← p.coreMatrix_add_tailMatrix N H W ω]
  abel

theorem gaussian_expected_full_core_difference_energy (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) (z : ℂ) :
    Integrable (fun ω => hilbertSchmidtSq
      ((p.matrix N W ω - z • 1) - (p.coreMatrix N H W ω - z • 1))) (gaussianProfileLaw N) ∧
      (∫ ω, hilbertSchmidtSq
        ((p.matrix N W ω - z • 1) - (p.coreMatrix N H W ω - z • 1)) ∂gaussianProfileLaw N) =
        p.tailMass N H W * (N : ℝ) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have heq (ω : ZMod N × ZMod N → ℂ) :
      hilbertSchmidtSq ((p.matrix N W ω - z • 1) - (p.coreMatrix N H W ω - z • 1)) =
        cyclicEnergy N (p.tailMatrix N H W ω) * (N : ℝ) := by
    rw [p.shifted_full_sub_core, cyclicEnergy, div_mul_cancel₀ _ hn]
  constructor
  · exact ((p.gaussian_expected_tail_energy N H W).1.mul_const (N : ℝ)).congr
      (ae_of_all _ fun ω => (heq ω).symm)
  · simp_rw [heq]
    rw [integral_mul_const, (p.gaussian_expected_tail_energy N H W).2]

theorem gaussian_expected_tail_cutoff_ae (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ a : ℝ, 0 < a →
      Integrable (fun ω => |matrixCutoffPotential (p.matrix N W ω - z • 1) a -
        matrixCutoffPotential (p.coreMatrix N H W ω - z • 1) a|) (gaussianProfileLaw N) ∧
      (∫ ω, |matrixCutoffPotential (p.matrix N W ω - z • 1) a -
        matrixCutoffPotential (p.coreMatrix N H W ω - z • 1) a| ∂gaussianProfileLaw N) ≤
        Real.sqrt (p.tailMass N H W) / a := by
  have hf := ae_shifted_cyclic_det_ne_zero (gaussianProfileLaw N) N (p.matrix N W)
    (fun i j => weightedCyclicMatrix_measurable N (p.weight N W) i j)
  filter_upwards [hf, p.gaussian_core_det_nonzero_ae N H W] with z hfull hcore
  intro a ha
  have hmfull : Measurable (fun ω => p.matrix N W ω - z • 1) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact (weightedCyclicMatrix_measurable N (p.weight N W) i j).sub measurable_const
  have hmcore : Measurable (fun ω => p.coreMatrix N H W ω - z • 1) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact (weightedCyclicMatrix_measurable N (maskedWeight (coreOffsets N H) (p.weight N W)) i j).sub
      measurable_const
  have hE := p.gaussian_expected_full_core_difference_energy N H W z
  obtain ⟨hi, hb⟩ := expected_matrixCutoff_difference_le (gaussianProfileLaw N)
    (fun ω => p.matrix N W ω - z • 1) (fun ω => p.coreMatrix N H W ω - z • 1)
    hmfull hmcore hfull hcore hE.1 ha
  refine ⟨hi, ?_⟩
  rw [hE.2, ZMod.card, Real.sqrt_mul (p.tailMass_nonneg N H W)] at hb
  have hn : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))).ne'
  convert hb using 1
  field_simp

end CircularLawSection6.NoncompactProfile
