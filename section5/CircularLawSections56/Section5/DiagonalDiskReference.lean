import CircularLawSections56.Section5.DiskReferenceLaw
import CircularLawSections56.Section6.PhysicalReplacementBridge

/-!
# Fully proved comparison ensemble

The diagonal entries are IID uniform disk points.  Both the empirical spectral
limit and the logarithmic-potential limit are consequences of the strong law;
neither is an input.  The expected normalized Hilbert--Schmidt energy is at most
one.  This elementary ensemble is sufficient for the replacement principle,
which imposes no Gaussian or independence assumptions on the matrix entries.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal BigOperators

noncomputable section

namespace CircularLawSections56.Section5

open Section6 TaoVuReplacement ShortRingAnchor

def diagonalDiskReference (k : ℕ) (ω : ℕ → ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal (fun i => ω i)

theorem diagonalDiskReference_measurable (k : ℕ) (i j : Fin (k + 1)) :
    Measurable (fun ω => diagonalDiskReference k ω i j) := by
  classical
  simp only [diagonalDiskReference, Matrix.diagonal_apply]
  split_ifs <;> fun_prop

theorem realEsdTest_diagonal {n : ℕ} (a : Fin n → ℂ) (f : ℂ → ℝ) :
    realEsdTest (Matrix.diagonal a) f = (∑ i, f (a i)) / (n : ℝ) := by
  classical
  have hroots : eigenvalueMultiset (Matrix.diagonal a) = Finset.univ.val.map a := by
    unfold eigenvalueMultiset
    rw [Matrix.charpoly_diagonal]
    simpa only [Multiset.map_map, Finset.prod, Function.comp_def] using
      Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map a)
  simp only [realEsdTest, realSpectralSum, hroots, Multiset.map_map, Fintype.card_fin]
  rfl

theorem diagonalDiskReference_energy_eq (k : ℕ) (ω : ℕ → ℂ) :
    physicalEnergy (diagonalDiskReference k ω) =
      (∑ i : Fin (k + 1), ‖ω i‖ ^ 2) / (k + 1 : ℝ) := by
  classical
  simp [physicalEnergy, hilbertSchmidtSq, diagonalDiskReference, Matrix.diagonal_apply,
    apply_ite, eq_comm]

theorem circularMeasure_norm_sq_integrable :
    Integrable (fun w : ℂ => ‖w‖ ^ 2) circularMeasure := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
  filter_upwards [circularMeasure_norm_lt_one] with w hw
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg w]

theorem diagonalDiskReference_energy_integrable_and_le_one (k : ℕ) :
    Integrable (fun ω => physicalEnergy (diagonalDiskReference k ω)) circularSampleMeasure ∧
      (∫ ω, physicalEnergy (diagonalDiskReference k ω) ∂circularSampleMeasure) ≤ 1 := by
  have hInt : Integrable (fun ω : ℕ → ℂ =>
      (∑ i : Fin (k + 1), ‖ω i‖ ^ 2) / (k + 1 : ℝ)) circularSampleMeasure := by
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    exact (circularSample_eval i.val).integrable_comp_of_integrable
      circularMeasure_norm_sq_integrable
  simp_rw [diagonalDiskReference_energy_eq]
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ _ω : ℕ → ℂ, (1 : ℝ) ∂circularSampleMeasure := by
      apply integral_mono_ae hInt (integrable_const _)
      have hall : ∀ᵐ ω ∂circularSampleMeasure, ∀ i : ℕ, ‖ω i‖ < 1 :=
        ae_all_iff.2 (fun i => (circularSample_eval i).quasiMeasurePreserving.ae
          circularMeasure_norm_lt_one)
      filter_upwards [hall] with ω hω
      apply (div_le_one (by positivity : (0 : ℝ) < k + 1)).2
      calc
        _ ≤ ∑ _i : Fin (k + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          nlinarith [hω i, norm_nonneg (ω i)]
        _ = _ := by simp
    _ = 1 := by simp

theorem diagonalDiskReference_logPotential_ae (k : ℕ) (z : ℂ) :
    (fun ω => physicalLogPotential (diagonalDiskReference k ω) z) =ᵐ[circularSampleMeasure]
      (fun ω => (∑ i : Fin (k + 1), Real.log ‖ω i - z‖) / (k + 1 : ℝ)) := by
  have hall : ∀ᵐ ω ∂circularSampleMeasure, ∀ i : ℕ, ω i ≠ z :=
    ae_all_iff.2 (fun i => (circularSample_eval i).quasiMeasurePreserving.ae
      (circularMeasure.ae_ne z))
  filter_upwards [hall] with ω hω
  have hdet : (diagonalDiskReference k ω - z • 1).det ≠ 0 := by
    classical
    rw [diagonalDiskReference, ← Matrix.diagonal_one, ← Matrix.diagonal_smul,
      Matrix.diagonal_sub, Matrix.det_diagonal]
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one] using
      (Finset.prod_ne_zero_iff.2 (fun i _ => sub_ne_zero.2 (hω i)) :
        (∏ i : Fin (k + 1), (ω i - z)) ≠ 0)
  calc
    _ = realEsdTest (diagonalDiskReference k ω) (fun w => Real.log ‖w - z‖) := by
      simpa [physicalLogPotential] using
        normalized_log_norm_det_sub_scalar_eq_realEsdTest (diagonalDiskReference k ω) z hdet
    _ = _ := by
      simpa only [diagonalDiskReference, Nat.cast_add, Nat.cast_one] using
        realEsdTest_diagonal (fun i : Fin (k + 1) => ω i) (fun w => Real.log ‖w - z‖)

theorem diagonalDiskReference_logPotential_limit (z : ℂ) :
    TendstoInMeasure circularSampleMeasure
      (fun k ω => physicalLogPotential (diagonalDiskReference k ω) z) atTop
      (fun _ => circularLogPotential z) := by
  apply TendstoInMeasure.congr_left (fun k => (diagonalDiskReference_logPotential_ae k z).symm)
  apply tendstoInMeasure_of_tendsto_ae (fun _ => Measurable.aestronglyMeasurable (by
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i _
    exact (measurable_norm.comp ((measurable_pi_apply i.val).sub measurable_const)).log))
  simpa only [circularMeasure_log_potential] using
    circularSample_average_tendsto (fun w => Real.log ‖w - z‖) (by fun_prop)
      (circularMeasure_log_integrable z)

/-- The reference ESD itself converges to normalized area, not only to another ESD. -/
theorem diagonalDiskReference_esd_limit (f : ℂ → ℝ) (hf : Continuous f)
    (hc : HasCompactSupport f) :
    TendstoInMeasure circularSampleMeasure
      (fun k ω => realEsdTest (diagonalDiskReference k ω) f) atTop
      (fun _ => ∫ w, f w ∂circularMeasure) := by
  simp_rw [diagonalDiskReference, realEsdTest_diagonal, Nat.cast_add, Nat.cast_one]
  apply tendstoInMeasure_of_tendsto_ae (fun _ => Measurable.aestronglyMeasurable (by
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i _
    exact hf.measurable.comp (measurable_pi_apply i.val)))
  exact circularSample_average_tendsto f hf.measurable (hf.integrable_of_hasCompactSupport hc)

end CircularLawSections56.Section5
