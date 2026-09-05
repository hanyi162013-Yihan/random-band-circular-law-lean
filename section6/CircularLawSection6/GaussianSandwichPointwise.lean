import CircularLawSection6.GaussianUpperCutoff
import CircularLawSection6.VaryingCoreCutoff
import CircularLawSection6.WeightedCyclicPointwiseNonzero
import CircularLawSection6.GaussianAllDimensions
import CircularLawSection6.ProfileDiagonalBound

/-! # Fixed-shift Gaussian core/full sandwich

The historical API packages these estimates on one planar full-measure set.
For a prescribed spectral parameter, the Gaussian row moment theorem and the
determinant-polynomial zero-set theorem instead discharge every finite-size
integrability and nonsingularity premise directly.  Thus no exceptional
spectral parameter occurs in this finite-matrix sandwich.
-/

open MeasureTheory
open TaoVuReplacement

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

theorem gaussian_rawProfileLogDet_integrable_at (p : NoncompactProfile)
    (N : ℕ) [NeZero N] (W : ℝ) (z : ℂ) :
    Integrable (p.rawProfileLogDet N W z) (gaussianProfileLaw N) := by
  have h := (gaussian_cyclic_memLp_and_variance_all N (p.weight N W)
    p.diagonalComparisonConstant_pos (r := 1) zero_lt_one z
    (p.diagonal_weight_ge N W)).1
  refine (h.integrable (by norm_num)).congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [cyclicRawLogDet, rawProfileLogDet, matrix]

theorem gaussian_rawCoreLogDet_integrable_at (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) (z : ℂ) :
    Integrable (p.rawCoreLogDet N H W z) (gaussianProfileLaw N) := by
  have hq : p.diagonalComparisonConstant / (N : ℝ) ≤
      maskedWeight (coreOffsets N H) (p.weight N W) 0 := by
    simpa only [maskedWeight, if_pos (zero_mem_coreOffsets N H)] using
      p.diagonal_weight_ge N W
  have h := (gaussian_cyclic_memLp_and_variance_all N _
    p.diagonalComparisonConstant_pos (r := 1) zero_lt_one z hq).1
  refine (h.integrable (by norm_num)).congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [cyclicRawLogDet, rawCoreLogDet, coreMatrix]

theorem gaussian_expected_tail_jensen_at (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) (z : ℂ) :
    (∫ ω, p.rawCoreLogDet N H W z ω ∂gaussianProfileLaw N) / (N : ℝ) ≤
      (∫ ω, p.rawProfileLogDet N W z ω ∂gaussianProfileLaw N) / (N : ℝ) :=
  p.gaussian_expected_tail_jensen N H W z
    (p.gaussian_rawProfileLogDet_integrable_at N W z)
    (p.gaussian_rawCoreLogDet_integrable_at N H W z)
    (p.gaussian_core_det_nonzero N H W z)

theorem gaussian_expected_tail_cutoff_at (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) (z : ℂ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun ω => |matrixCutoffPotential (p.matrix N W ω - z • 1) a -
      matrixCutoffPotential (p.coreMatrix N H W ω - z • 1) a|) (gaussianProfileLaw N) ∧
    (∫ ω, |matrixCutoffPotential (p.matrix N W ω - z • 1) a -
      matrixCutoffPotential (p.coreMatrix N H W ω - z • 1) a| ∂gaussianProfileLaw N) ≤
      Real.sqrt (p.tailMass N H W) / a := by
  have hmfull : Measurable (fun ω => p.matrix N W ω - z • 1) :=
    (weightedCyclicMatrix_measurable_matrix N _).sub measurable_const
  have hmcore : Measurable (fun ω => p.coreMatrix N H W ω - z • 1) :=
    (weightedCyclicMatrix_measurable_matrix N _).sub measurable_const
  have hE := p.gaussian_expected_full_core_difference_energy N H W z
  obtain ⟨hi, hb⟩ := expected_matrixCutoff_difference_le (gaussianProfileLaw N)
    (fun ω => p.matrix N W ω - z • 1) (fun ω => p.coreMatrix N H W ω - z • 1)
    hmfull hmcore (p.gaussian_profile_det_nonzero N W z)
    (p.gaussian_core_det_nonzero N H W z) hE.1 ha
  refine ⟨hi, ?_⟩
  rw [hE.2, ZMod.card, Real.sqrt_mul (p.tailMass_nonneg N H W)] at hb
  have hn : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))).ne'
  convert hb using 1
  field_simp

theorem gaussian_expected_core_full_cutoff_sandwich_at (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) (z : ℂ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun ω => matrixCutoffPotential (p.coreMatrix N H W ω - z • 1) a)
      (gaussianProfileLaw N) ∧
    (∫ ω, p.rawCoreLogDet N H W z ω ∂gaussianProfileLaw N) / (N : ℝ) ≤
      (∫ ω, p.rawProfileLogDet N W z ω ∂gaussianProfileLaw N) / (N : ℝ) ∧
    (∫ ω, p.rawProfileLogDet N W z ω ∂gaussianProfileLaw N) / (N : ℝ) ≤
      (∫ ω, matrixCutoffPotential (p.coreMatrix N H W ω - z • 1) a
        ∂gaussianProfileLaw N) + Real.sqrt (p.tailMass N H W) / a := by
  have hmcore : Measurable (p.coreMatrix N H W) :=
    weightedCyclicMatrix_measurable_matrix N _
  have hEcore := integrable_hilbertSchmidtSq_of_cyclicEnergy (gaussianProfileLaw N) N
    (p.coreMatrix N H W) (p.gaussian_expected_core_energy N H W).1
  have hEshift := integrable_hilbertSchmidtSq_sub (gaussianProfileLaw N)
    (p.coreMatrix N H W) (fun _ => z • (1 : Matrix (ZMod N) (ZMod N) ℂ))
    hmcore measurable_const hEcore (integrable_const _)
  have hcutoff := integrable_matrixCutoffPotential (gaussianProfileLaw N)
    (fun ω => p.coreMatrix N H W ω - z • 1)
    (hmcore.sub measurable_const) (p.gaussian_core_det_nonzero N H W z) hEshift ha
  refine ⟨hcutoff, p.gaussian_expected_tail_jensen_at N H W z, ?_⟩
  have hraw : Integrable (fun ω => matrixRawPotential (p.matrix N W ω - z • 1))
      (gaussianProfileLaw N) := by
    simpa only [matrixRawPotential, ZMod.card, rawProfileLogDet] using
      (p.gaussian_rawProfileLogDet_integrable_at N W z).div_const (N : ℝ)
  have hdiff := p.gaussian_expected_tail_cutoff_at N H W z ha
  have h := expected_raw_le_cutoff_of_error (gaussianProfileLaw N)
    (fun ω => p.matrix N W ω - z • 1) (fun ω => p.coreMatrix N H W ω - z • 1)
    a (Real.sqrt (p.tailMass N H W) / a) (p.gaussian_profile_det_nonzero N W z)
    hraw hcutoff hdiff.1 hdiff.2
  simpa only [matrixRawPotential, ZMod.card, rawProfileLogDet, integral_div] using h

theorem gaussian_unitCore_cutoff_scaling_at (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (z : ℂ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun ω => matrixCutoffPotential
      ((r : ℂ) • p.unitCoreMatrix N H W ω - z • 1) a) (gaussianProfileLaw N) ∧
    Integrable (fun ω => matrixCutoffPotential
      ((s : ℂ) • p.unitCoreMatrix N H W ω - z • 1) a) (gaussianProfileLaw N) ∧
    (∫ ω, |matrixCutoffPotential ((r : ℂ) • p.unitCoreMatrix N H W ω - z • 1) a -
      matrixCutoffPotential ((s : ℂ) • p.unitCoreMatrix N H W ω - z • 1) a|
      ∂gaussianProfileLaw N) ≤ |r - s| / a := by
  have hm : Measurable (p.unitCoreMatrix N H W) :=
    weightedCyclicMatrix_measurable_matrix N _
  have hms (t : ℝ) : Measurable (fun ω => (t : ℂ) • p.unitCoreMatrix N H W ω) :=
    hm.const_smul (t : ℂ)
  have hdet (t : ℝ) (ht : 0 < t) : ∀ᵐ ω ∂gaussianProfileLaw N,
      ((t : ℂ) • p.unitCoreMatrix N H W ω - z • 1).det ≠ 0 := by
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    filter_upwards [p.gaussian_unitCore_det_nonzero N H W (z / (t : ℂ))] with ω hω
    have heq : (t : ℂ) • p.unitCoreMatrix N H W ω - z • 1 =
        (t : ℂ) • (p.unitCoreMatrix N H W ω - (z / (t : ℂ)) • 1) := by
      rw [smul_sub, smul_smul]
      congr 2
      field_simp
    rw [heq, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ htC) hω
  have hEU := integrable_hilbertSchmidtSq_of_cyclicEnergy (gaussianProfileLaw N) N
    (p.unitCoreMatrix N H W) (p.gaussian_expected_unitCore_energy N H W).1
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hmean : (∫ ω, hilbertSchmidtSq (p.unitCoreMatrix N H W ω)
      ∂gaussianProfileLaw N) = (N : ℝ) := by
    have heq (ω : ZMod N × ZMod N → ℂ) :
        hilbertSchmidtSq (p.unitCoreMatrix N H W ω) =
          cyclicEnergy N (p.unitCoreMatrix N H W ω) * (N : ℝ) := by
      rw [cyclicEnergy, div_mul_cancel₀ _ hn]
    simp_rw [heq]
    rw [integral_mul_const, (p.gaussian_expected_unitCore_energy N H W).2, one_mul]
  have hscaled (t : ℝ) : Integrable (fun ω =>
      hilbertSchmidtSq ((t : ℂ) • p.unitCoreMatrix N H W ω - z • 1))
      (gaussianProfileLaw N) :=
    integrable_hilbertSchmidtSq_sub (gaussianProfileLaw N)
      (fun ω => (t : ℂ) • p.unitCoreMatrix N H W ω) (fun _ => z • 1)
      (hms t) measurable_const (integrable_hilbertSchmidtSq_smul _ _ hEU _)
      (integrable_const _)
  have hcut (t : ℝ) (ht : 0 < t) := integrable_matrixCutoffPotential
    (gaussianProfileLaw N) (fun ω => (t : ℂ) • p.unitCoreMatrix N H W ω - z • 1)
    ((hms t).sub measurable_const) (hdet t ht) (hscaled t) ha
  refine ⟨hcut r hr, hcut s hs, ?_⟩
  have hd (ω : ZMod N × ZMod N → ℂ) :
      ((r : ℂ) • p.unitCoreMatrix N H W ω - z • 1) -
        ((s : ℂ) • p.unitCoreMatrix N H W ω - z • 1) =
      ((r - s : ℝ) : ℂ) • p.unitCoreMatrix N H W ω := by
    push_cast
    module
  have hE : Integrable (fun ω => hilbertSchmidtSq
      (((r : ℂ) • p.unitCoreMatrix N H W ω - z • 1) -
        ((s : ℂ) • p.unitCoreMatrix N H W ω - z • 1))) (gaussianProfileLaw N) := by
    simpa only [hd] using integrable_hilbertSchmidtSq_smul _ _ hEU ((r - s : ℝ) : ℂ)
  have hb := (expected_matrixCutoff_difference_le (gaussianProfileLaw N)
    (fun ω => (r : ℂ) • p.unitCoreMatrix N H W ω - z • 1)
    (fun ω => (s : ℂ) • p.unitCoreMatrix N H W ω - z • 1)
    ((hms r).sub measurable_const) ((hms s).sub measurable_const)
    (hdet r hr) (hdet s hs) hE ha).2
  simp_rw [hd, hilbertSchmidtSq_smul] at hb
  rw [integral_const_mul, hmean, ZMod.card,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Complex.norm_real, Real.norm_eq_abs] at hb
  have hnroot : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))).ne'
  convert hb using 1
  field_simp

theorem gaussian_expected_unitCore_upper_at (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) (z : ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ ω, p.rawCoreLogDet N H W z ω ∂gaussianProfileLaw N) / (N : ℝ) ≤
      (∫ ω, p.rawProfileLogDet N W z ω ∂gaussianProfileLaw N) / (N : ℝ) ∧
    (∫ ω, p.rawProfileLogDet N W z ω ∂gaussianProfileLaw N) / (N : ℝ) ≤
      (∫ ω, matrixCutoffPotential (p.unitCoreMatrix N H W ω - z • 1) a
        ∂gaussianProfileLaw N) +
        (Real.sqrt (p.tailMass N H W) + |Real.sqrt (p.coreMass N H W) - 1|) / a := by
  have hroot : 0 < Real.sqrt (p.coreMass N H W) :=
    Real.sqrt_pos.2 (p.coreMass_pos N H W)
  obtain ⟨hi, hj, hb⟩ := p.gaussian_unitCore_cutoff_scaling_at N H W hroot
    zero_lt_one z ha
  simp only [Complex.ofReal_one] at hj hb
  have hcmp : (∫ ω, matrixCutoffPotential (p.coreMatrix N H W ω - z • 1) a
      ∂gaussianProfileLaw N) -
      (∫ ω, matrixCutoffPotential (p.unitCoreMatrix N H W ω - z • 1) a
        ∂gaussianProfileLaw N) ≤ |Real.sqrt (p.coreMass N H W) - 1| / a := by
    have h := (le_abs_self (∫ ω, matrixCutoffPotential
      ((Real.sqrt (p.coreMass N H W) : ℂ) • p.unitCoreMatrix N H W ω - z • 1) a -
      matrixCutoffPotential ((1 : ℂ) • p.unitCoreMatrix N H W ω - z • 1) a
      ∂gaussianProfileLaw N)).trans (abs_integral_le_integral_abs.trans hb)
    rw [integral_sub hi hj] at h
    simpa only [← p.coreMatrix_eq_scale_unitCoreMatrix, one_smul] using h
  have hz := p.gaussian_expected_core_full_cutoff_sandwich_at N H W z ha
  refine ⟨hz.2.1, ?_⟩
  rw [add_div]
  linarith [hz.2.2]

end CircularLawSection6.NoncompactProfile
