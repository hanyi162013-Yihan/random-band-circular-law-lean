import CircularLawSections56.Section5.LiteralNonvanishing
import CircularLawSection6.CyclicMatrix

/-! # Reusing Section 5 / replacement logarithmic-potential estimates

The existing replacement library proves local squared-logarithmic-potential
bounds in terms of matrix energy. Fubini turns these into integrability over
the random samples for planar almost every spectral parameter. No Gaussian
small-ball theorem is needed for this a.e.-parameter conclusion.
-/

open MeasureTheory Set Filter
open TaoVuReplacement CircularLawSections56.Section6

noncomputable section

namespace CircularLawSection6

theorem normalizedLogDet_sq_integrableOn_closedBall {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (R : ℝ) :
    IntegrableOn (fun z => (normalizedLogDet A z) ^ 2) (Metric.closedBall 0 R) := by
  apply (integrableOn_multisetLogPotential_sq R (eigenvalueMultiset (normalizedMatrix A))).congr
  filter_upwards [ae_restrict_of_ae (ae_normalizedLogDet_eq_matrixLogPotential A)] with z hz
  simpa only [matrixLogPotential_eq_multisetLogPotential] using (congrArg (· ^ 2) hz).symm

theorem exists_integral_normalizedLogDet_sq_le (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
      (∫ z in Metric.closedBall 0 R, (normalizedLogDet A z) ^ 2) ≤
        C * (1 + normalizedHilbertSchmidtSq A) := by
  obtain ⟨C, hC, hb⟩ := exists_integral_normalizedMatrixLogPotential_sq_closedBall_le R hR
  refine ⟨C, hC, fun {k} A => ?_⟩
  calc
    _ = ∫ z in Metric.closedBall 0 R,
        (multisetLogPotential (eigenvalueMultiset (normalizedMatrix A)) z) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (ae_normalizedLogDet_eq_matrixLogPotential A)] with z hz
      simpa only [matrixLogPotential_eq_multisetLogPotential] using congrArg (· ^ 2) hz
    _ ≤ _ := hb A

theorem normalizedLogDet_sq_integrable_prod {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {k : ℕ}
    (A : Ω → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j))
    (hE : Integrable (fun ω => normalizedHilbertSchmidtSq (A ω)) μ)
    (R : ℝ) (hR : 0 ≤ R) :
    Integrable (fun v : Ω × ℂ => (normalizedLogDet (A v.1) v.2) ^ 2)
      (μ.prod (volume.restrict (Metric.closedBall 0 R))) := by
  have hm : Measurable (fun v : Ω × ℂ => (normalizedLogDet (A v.1) v.2) ^ 2) :=
    ((measurable_normalizedLogDet_joint_of_entrywise A hA).comp measurable_swap).pow_const 2
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ (fun ω => normalizedLogDet_sq_integrableOn_closedBall (A ω) R)
  · obtain ⟨C, _, hb⟩ := exists_integral_normalizedLogDet_sq_le R hR
    apply ((hE.const_add 1).const_mul C).mono'
    · exact hm.aestronglyMeasurable.norm.integral_prod_right'
    · filter_upwards with ω
      simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [abs_of_nonneg (integral_nonneg (fun z => sq_nonneg _))]
      exact hb (A ω)

theorem ae_normalizedLogDet_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {k : ℕ}
    (A : Ω → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j))
    (hE : Integrable (fun ω => normalizedHilbertSchmidtSq (A ω)) μ) :
    ∀ᵐ z ∂(volume : Measure ℂ), Integrable (fun ω => normalizedLogDet (A ω) z) μ := by
  have hball (R : ℕ) : ∀ᵐ z ∂(volume.restrict (Metric.closedBall (0 : ℂ) (R : ℝ))),
      Integrable (fun ω => normalizedLogDet (A ω) z) μ := by
    filter_upwards [(normalizedLogDet_sq_integrable_prod μ A hA hE R (Nat.cast_nonneg R)).prod_left_ae]
      with z hz
    exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      ((memLp_two_iff_integrable_sq
        (measurable_normalizedLogDet_fixed_of_entrywise A hA z).aestronglyMeasurable).2 hz)
  have h := (ae_restrict_iUnion_iff (fun R : ℕ => Metric.closedBall (0 : ℂ) (R : ℝ))
    (fun z => Integrable (fun ω => normalizedLogDet (A ω) z) μ)).2 hball
  simpa only [Metric.iUnion_closedBall_nat, Measure.restrict_univ] using h

/-- The same nonvanishing theorem already used by Section 5, with cyclic
indices and physical (already normalized) matrices. -/
theorem ae_shifted_cyclic_det_ne_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (N : ℕ) [NeZero N]
    (A : Ω → Matrix (ZMod N) (ZMod N) ℂ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j)) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ ω ∂μ, (A ω - z • 1).det ≠ 0 := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k =>
    have h := ae_ae_normalizedShiftDet_ne_zero_of_entrywise μ
      (fun ω => undoPhysicalNormalization (A ω))
      (fun i j => measurable_const.mul (hA i j))
    simpa only [normalizedShiftDet, normalizedMatrix_undoPhysicalNormalization] using h

/-- A finite expected energy is enough for the raw shifted determinant's
logarithm to be integrable for almost every `z`; no density input is required. -/
theorem ae_cyclic_rawLogDet_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (N : ℕ) [NeZero N]
    (A : Ω → Matrix (ZMod N) (ZMod N) ℂ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j))
    (hE : Integrable (fun ω => cyclicEnergy N (A ω)) μ) :
    ∀ᵐ z ∂(volume : Measure ℂ), Integrable (fun ω => Real.log ‖(A ω - z • 1).det‖) μ := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k =>
    have hEn : Integrable (fun ω => normalizedHilbertSchmidtSq (undoPhysicalNormalization (A ω))) μ := by
      simpa only [normalizedEnergy_undoPhysicalNormalization, physicalEnergy,
        cyclicEnergy, Nat.cast_add, Nat.cast_one] using hE
    have h := ae_normalizedLogDet_integrable μ (fun ω => undoPhysicalNormalization (A ω))
      (fun i j => measurable_const.mul (hA i j)) hEn
    filter_upwards [h] with z hz
    have hn : (k + 1 : ℝ) ≠ 0 := by positivity
    simpa only [normalizedLogDet_undoPhysicalNormalization, physicalLogPotential,
      div_mul_cancel₀ hn] using hz.mul_const (k + 1 : ℝ)

end CircularLawSection6
