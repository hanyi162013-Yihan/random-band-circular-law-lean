import CircularLawSection6.ExpectedCutoffComparison

/-! # Finite expected matrix energy implies cutoff integrability

Compare with the identity matrix, whose cutoff is a finite constant.
The square-integrability needed for the comparison is obtained from the
two original energies. This avoids a separate spectral measurability or
cutoff-integrability hypothesis in the random-matrix applications.
-/

open MeasureTheory
open TaoVuReplacement
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem hilbertSchmidtSq_sub_le (A B : Matrix ι ι ℂ) :
    hilbertSchmidtSq (A - B) ≤ 2 * hilbertSchmidtSq A + 2 * hilbertSchmidtSq B := by
  have hentry (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg (x - y)) (add_nonneg (norm_nonneg x) (norm_nonneg y))).mpr
      (norm_sub_le x y)
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  unfold hilbertSchmidtSq
  calc
    _ ≤ ∑ i, ∑ j, (2 * ‖A i j‖ ^ 2 + 2 * ‖B i j‖ ^ 2) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hentry (A i j) (B i j)))
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

omit [DecidableEq ι] in
theorem integrable_hilbertSchmidtSq_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Ω → Matrix ι ι ℂ) (hA : Measurable A) (hB : Measurable B)
    (hEA : Integrable (fun ω => hilbertSchmidtSq (A ω)) μ)
    (hEB : Integrable (fun ω => hilbertSchmidtSq (B ω)) μ) :
    Integrable (fun ω => hilbertSchmidtSq (A ω - B ω)) μ := by
  apply ((hEA.const_mul 2).add (hEB.const_mul 2)).mono'
  · exact (continuous_hilbertSchmidtSq.measurable.comp (hA.sub hB)).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hilbertSchmidtSq_nonneg _)]
    exact hilbertSchmidtSq_sub_le _ _

theorem integrable_matrixCutoffPotential [Nonempty ι]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix ι ι ℂ) (hA : Measurable A)
    (hdet : ∀ᵐ ω ∂μ, (A ω).det ≠ 0)
    (hE : Integrable (fun ω => hilbertSchmidtSq (A ω)) μ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun ω => matrixCutoffPotential (A ω) a) μ := by
  have hEI := integrable_hilbertSchmidtSq_sub μ A (fun _ => (1 : Matrix ι ι ℂ))
    hA measurable_const hE (integrable_const _)
  have hi := (expected_matrixCutoff_difference_le μ A (fun _ => (1 : Matrix ι ι ℂ))
    hA measurable_const hdet (ae_of_all _ fun _ => by simp) hEI ha).1
  have hsub : Integrable (fun ω => matrixCutoffPotential (A ω) a -
      matrixCutoffPotential (1 : Matrix ι ι ℂ) a) μ := by
    apply (integrable_norm_iff
      ((aestronglyMeasurable_matrixCutoffPotential μ A hA hdet ha).sub aestronglyMeasurable_const)).mp
    simpa only [Real.norm_eq_abs] using hi
  apply (hsub.add (integrable_const (matrixCutoffPotential (1 : Matrix ι ι ℂ) a))).congr
  filter_upwards with ω
  exact sub_add_cancel _ _

end CircularLawSection6
