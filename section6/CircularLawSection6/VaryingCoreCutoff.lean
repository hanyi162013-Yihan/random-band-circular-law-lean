import CircularLawSection6.GaussianUpperCutoff

/-! # Actual cutoff stability for the varying core normalization

The unit core has expected squared Hilbert--Schmidt norm exactly `N`.
Consequently the cutoff error under two real scalings is at most
`|r-s|/a`, including zero or negative scalings. Countable parameter
intersection then handles the varying normalizing radius on one planar
full-measure set. No uniform-in-scale compact-core limit is assumed.
-/

open MeasureTheory Filter Topology
open TaoVuReplacement

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem integrable_hilbertSchmidtSq_smul {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → Matrix ι ι ℂ)
    (hE : Integrable (fun ω => hilbertSchmidtSq (A ω)) μ) (c : ℂ) :
    Integrable (fun ω => hilbertSchmidtSq (c • A ω)) μ := by
  classical
  simpa only [hilbertSchmidtSq_smul] using hE.const_mul (‖c‖ ^ 2)

namespace NoncompactProfile

theorem gaussian_unitCore_cutoff_scaling_ae (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W r s : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ a : ℝ, 0 < a →
      Integrable (fun ω => matrixCutoffPotential ((r : ℂ) • p.unitCoreMatrix N H W ω - z • 1) a)
        (gaussianProfileLaw N) ∧
      Integrable (fun ω => matrixCutoffPotential ((s : ℂ) • p.unitCoreMatrix N H W ω - z • 1) a)
        (gaussianProfileLaw N) ∧
      (∫ ω, |matrixCutoffPotential ((r : ℂ) • p.unitCoreMatrix N H W ω - z • 1) a -
        matrixCutoffPotential ((s : ℂ) • p.unitCoreMatrix N H W ω - z • 1) a|
        ∂gaussianProfileLaw N) ≤ |r - s| / a := by
  have hm : Measurable (p.unitCoreMatrix N H W) :=
    weightedCyclicMatrix_measurable_matrix N _
  have hms (t : ℝ) : Measurable (fun ω => (t : ℂ) • p.unitCoreMatrix N H W ω) := by
    simpa only [Pi.smul_apply] using hm.const_smul (t : ℂ)
  have hdet (t : ℝ) := ae_shifted_cyclic_det_ne_zero (gaussianProfileLaw N) N
    (fun ω => (t : ℂ) • p.unitCoreMatrix N H W ω)
    (fun i j => measurable_const.mul (weightedCyclicMatrix_measurable N
      (maskedWeight (coreOffsets N H) (p.normalizedCoreWeight N H W)) i j))
  have hEU := integrable_hilbertSchmidtSq_of_cyclicEnergy (gaussianProfileLaw N) N
    (p.unitCoreMatrix N H W) (p.gaussian_expected_unitCore_energy N H W).1
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hmean : (∫ ω, hilbertSchmidtSq (p.unitCoreMatrix N H W ω) ∂gaussianProfileLaw N) =
      (N : ℝ) := by
    have heq (ω : ZMod N × ZMod N → ℂ) :
        hilbertSchmidtSq (p.unitCoreMatrix N H W ω) =
          cyclicEnergy N (p.unitCoreMatrix N H W ω) * (N : ℝ) := by
      rw [cyclicEnergy, div_mul_cancel₀ _ hn]
    simp_rw [heq]
    rw [integral_mul_const, (p.gaussian_expected_unitCore_energy N H W).2, one_mul]
  filter_upwards [hdet r, hdet s] with z hr hs
  intro a ha
  have hscaled (t : ℝ) : Integrable (fun ω =>
      hilbertSchmidtSq ((t : ℂ) • p.unitCoreMatrix N H W ω - z • 1)) (gaussianProfileLaw N) :=
    integrable_hilbertSchmidtSq_sub (gaussianProfileLaw N)
      (fun ω => (t : ℂ) • p.unitCoreMatrix N H W ω) (fun _ => z • 1)
      (hms t) measurable_const
      (integrable_hilbertSchmidtSq_smul _ _ hEU _) (integrable_const _)
  have hcut (t : ℝ) (ht : ∀ᵐ ω ∂gaussianProfileLaw N,
      ((t : ℂ) • p.unitCoreMatrix N H W ω - z • 1).det ≠ 0) :=
    integrable_matrixCutoffPotential (gaussianProfileLaw N)
      (fun ω => (t : ℂ) • p.unitCoreMatrix N H W ω - z • 1)
      ((hms t).sub measurable_const) ht (hscaled t) ha
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
    hr hs hE ha).2
  simp_rw [hd, hilbertSchmidtSq_smul] at hb
  rw [integral_const_mul, hmean, ZMod.card,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Complex.norm_real, Real.norm_eq_abs] at hb
  have hnroot : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))).ne'
  convert hb using 1
  field_simp

theorem gaussian_unitCore_cutoff_varying_scale (p : NoncompactProfile)
    (N H : ℕ → ℕ) [∀ n, NeZero (N n)] (W r : ℕ → ℝ) {s a : ℝ}
    (hr : Tendsto r atTop (𝓝 s)) (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n =>
        |(∫ ω, matrixCutoffPotential ((r n : ℂ) • p.unitCoreMatrix (N n) (H n) (W n) ω - z • 1) a
          ∂gaussianProfileLaw (N n)) -
          ∫ ω, matrixCutoffPotential ((s : ℂ) • p.unitCoreMatrix (N n) (H n) (W n) ω - z • 1) a
            ∂gaussianProfileLaw (N n)|) atTop (𝓝 0) := by
  have hall := ae_all_iff.2 (fun n => p.gaussian_unitCore_cutoff_scaling_ae (N n) (H n) (W n) (r n) s)
  filter_upwards [hall] with z hz
  apply squeeze_zero (fun _ => abs_nonneg _) (fun n => ?_)
    (show Tendsto (fun n => |r n - s| / a) atTop (𝓝 0) by
      simpa only [sub_self, abs_zero, zero_div] using (hr.sub tendsto_const_nhds).abs.div_const a)
  obtain ⟨hi, hj, hb⟩ := hz n a ha
  rw [← integral_sub hi hj]
  exact abs_integral_le_integral_abs.trans hb

end NoncompactProfile
end CircularLawSection6
