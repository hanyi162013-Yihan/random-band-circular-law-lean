import CircularLawSection6.GaussianTailCutoff
import CircularLawSection6.CutoffIntegrability
import CircularLawSection6.RawPotentialScaling

/-! # The actual expected core/full cutoff sandwich

The raw lower bound is the rotation/Jensen theorem. The upper bound combines
the determinant/singular-log formula, the proved spectral comparison, and
the exact tail energy. All sample integrability and nonsingularity inputs
are discharged for planar almost every spectral parameter. The statement
includes every positive cutoff and hence permits subsequent choices of it.
-/

open MeasureTheory
open TaoVuReplacement

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem expected_raw_le_cutoff_of_error
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Ω → Matrix ι ι ℂ) (a error : ℝ)
    (hdet : ∀ᵐ ω ∂μ, (A ω).det ≠ 0)
    (hraw : Integrable (fun ω => matrixRawPotential (A ω)) μ)
    (hcore : Integrable (fun ω => matrixCutoffPotential (B ω) a) μ)
    (hdiff : Integrable (fun ω =>
      |matrixCutoffPotential (A ω) a - matrixCutoffPotential (B ω) a|) μ)
    (herror : (∫ ω,
      |matrixCutoffPotential (A ω) a - matrixCutoffPotential (B ω) a| ∂μ) ≤ error) :
    (∫ ω, matrixRawPotential (A ω) ∂μ) ≤
      (∫ ω, matrixCutoffPotential (B ω) a ∂μ) + error := by
  calc
    _ ≤ ∫ ω, matrixCutoffPotential (B ω) a +
        |matrixCutoffPotential (A ω) a - matrixCutoffPotential (B ω) a| ∂μ := by
      apply integral_mono_ae hraw (hcore.add hdiff)
      filter_upwards [hdet] with ω hω
      have h := matrixRawPotential_le_cutoff (A ω) hω a
      have h' := le_abs_self (matrixCutoffPotential (A ω) a - matrixCutoffPotential (B ω) a)
      linarith
    _ = (∫ ω, matrixCutoffPotential (B ω) a ∂μ) +
        ∫ ω, |matrixCutoffPotential (A ω) a - matrixCutoffPotential (B ω) a| ∂μ :=
      integral_add hcore hdiff
    _ ≤ _ := add_le_add_left herror _

theorem integrable_hilbertSchmidtSq_of_cyclicEnergy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : ℕ) [NeZero N]
    (A : Ω → Matrix (ZMod N) (ZMod N) ℂ)
    (hE : Integrable (fun ω => cyclicEnergy N (A ω)) μ) :
    Integrable (fun ω => hilbertSchmidtSq (A ω)) μ := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simpa only [cyclicEnergy, div_mul_cancel₀ _ hn] using hE.mul_const (N : ℝ)

namespace NoncompactProfile

theorem gaussian_expected_core_full_cutoff_sandwich_ae (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ a : ℝ, 0 < a →
      Integrable (fun ω => matrixCutoffPotential (p.coreMatrix N H W ω - z • 1) a)
        (gaussianProfileLaw N) ∧
      (∫ ω, p.rawCoreLogDet N H W z ω ∂gaussianProfileLaw N) / (N : ℝ) ≤
        (∫ ω, p.rawProfileLogDet N W z ω ∂gaussianProfileLaw N) / (N : ℝ) ∧
      (∫ ω, p.rawProfileLogDet N W z ω ∂gaussianProfileLaw N) / (N : ℝ) ≤
        (∫ ω, matrixCutoffPotential (p.coreMatrix N H W ω - z • 1) a ∂gaussianProfileLaw N) +
          Real.sqrt (p.tailMass N H W) / a := by
  have hf := ae_shifted_cyclic_det_ne_zero (gaussianProfileLaw N) N (p.matrix N W)
    (fun i j => weightedCyclicMatrix_measurable N (p.weight N W) i j)
  filter_upwards [hf, p.gaussian_core_det_nonzero_ae N H W,
    p.gaussian_rawProfileLogDet_integrable_ae N W,
    p.gaussian_expected_tail_cutoff_ae N H W,
    p.gaussian_expected_tail_jensen_ae N H W] with z hfull hcore hraw hdiff hlower
  intro a ha
  have hmcore : Measurable (p.coreMatrix N H W) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact weightedCyclicMatrix_measurable N
      (maskedWeight (coreOffsets N H) (p.weight N W)) i j
  have hEcore := integrable_hilbertSchmidtSq_of_cyclicEnergy (gaussianProfileLaw N) N
    (p.coreMatrix N H W) (p.gaussian_expected_core_energy N H W).1
  have hEshift := integrable_hilbertSchmidtSq_sub (gaussianProfileLaw N)
    (p.coreMatrix N H W) (fun _ => z • (1 : Matrix (ZMod N) (ZMod N) ℂ))
    hmcore measurable_const hEcore (integrable_const _)
  have hcutoff := integrable_matrixCutoffPotential (gaussianProfileLaw N)
    (fun ω => p.coreMatrix N H W ω - z • 1)
    (hmcore.sub measurable_const) hcore hEshift ha
  refine ⟨hcutoff, hlower, ?_⟩
  have hraw' : Integrable (fun ω => matrixRawPotential (p.matrix N W ω - z • 1))
      (gaussianProfileLaw N) := by
    simpa only [matrixRawPotential, ZMod.card, rawProfileLogDet] using hraw.div_const (N : ℝ)
  have h := expected_raw_le_cutoff_of_error (gaussianProfileLaw N)
    (fun ω => p.matrix N W ω - z • 1) (fun ω => p.coreMatrix N H W ω - z • 1)
    a (Real.sqrt (p.tailMass N H W) / a) hfull hraw' hcutoff (hdiff a ha).1 (hdiff a ha).2
  simpa only [matrixRawPotential, ZMod.card, rawProfileLogDet, integral_div] using h

/-- A single full-measure parameter set supports every size, integer core
radius, and positive cutoff, including choices depending on the size. -/
theorem gaussian_expected_core_full_cutoff_sandwich_triangular (p : NoncompactProfile)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ n H, ∀ a : ℝ, 0 < a →
      Integrable (fun ω => matrixCutoffPotential (p.coreMatrix (N n) H (W n) ω - z • 1) a)
        (gaussianProfileLaw (N n)) ∧
      (∫ ω, p.rawCoreLogDet (N n) H (W n) z ω ∂gaussianProfileLaw (N n)) / (N n : ℝ) ≤
        (∫ ω, p.rawProfileLogDet (N n) (W n) z ω ∂gaussianProfileLaw (N n)) / (N n : ℝ) ∧
      (∫ ω, p.rawProfileLogDet (N n) (W n) z ω ∂gaussianProfileLaw (N n)) / (N n : ℝ) ≤
        (∫ ω, matrixCutoffPotential (p.coreMatrix (N n) H (W n) ω - z • 1) a
          ∂gaussianProfileLaw (N n)) + Real.sqrt (p.tailMass (N n) H (W n)) / a :=
  ae_all_iff.2 (fun n => ae_all_iff.2 (fun H =>
    p.gaussian_expected_core_full_cutoff_sandwich_ae (N n) H (W n)))

end NoncompactProfile
end CircularLawSection6
