import CircularLawSection6.ClippedCutoffTail
import CircularLawSection6.CutoffIntegrability

/-! # The actual bounded squared-singular test and its matrix energy error

The bounded test is identified with a difference of two actual cutoff
potentials. Its measurability and integrability therefore follow from
the already proved matrix results. The upper error uses the exact sum
of squared singular values, identified with entrywise matrix energy.
-/

open MeasureTheory ShortRingAnchor TaoVuReplacement
open scoped BigOperators InnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem singularValues_sq_sum_eq_energy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : Module.End ℂ E) (hT : Function.Injective T) :
    (∑ i : Fin (Module.finrank ℂ E), T.singularValues i ^ 2) = operatorHilbertSchmidtSq T := by
  obtain ⟨u, v, hTv, _⟩ := exists_canonical_positive_singular_bases T hT
  have hnorm (i : Fin (Module.finrank ℂ E)) : ‖T (v i)‖ ^ 2 = T.singularValues i ^ 2 := by
    rw [hTv, norm_smul, u.orthonormal.1 i, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ = ∑ i, ‖T (v i)‖ ^ 2 := Finset.sum_congr rfl fun i _ => (hnorm i).symm
    _ = ∑ i, ∑ j, ‖⟪u j, T (v i)⟫_ℂ‖ ^ 2 := by simp_rw [u.sum_sq_norm_inner_right]
    _ = _ := by rw [Finset.sum_comm]; exact crossBasis_energy_eq u v T

theorem clippedLog_eq_cutoff_difference {a R s : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hs : 0 ≤ s) :
    clippedLog a R (s ^ 2) = Real.log (max s a) - Real.log (max s R) + Real.log R := by
  have h := cutoffLog_eq_clippedLog_add_upper ha haR hs
  by_cases hRs : R < s
  · rw [upperLogCorrection, if_pos hRs] at h
    rw [max_eq_left hRs.le]
    linarith
  · rw [upperLogCorrection, if_neg hRs] at h
    rw [max_eq_right (le_of_not_gt hRs)]
    linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def matrixClippedPotential (A : Matrix ι ι ℂ) (a R : ℝ) : ℝ :=
  (∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)),
    clippedLog a R (A.toEuclideanLin.singularValues i ^ 2)) /
      (Module.finrank ℂ (EuclideanSpace ℂ ι) : ℝ)

theorem matrixClippedPotential_eq_cutoff_difference (A : Matrix ι ι ℂ)
    {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    matrixClippedPotential A a R =
      matrixCutoffPotential A a - matrixCutoffPotential A R + Real.log R := by
  have hn : (Module.finrank ℂ (EuclideanSpace ℂ ι) : ℝ) ≠ 0 := by
    simp only [finrank_euclideanSpace]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold matrixClippedPotential matrixCutoffPotential operatorCutoffPotential
  simp_rw [clippedLog_eq_cutoff_difference ha haR (A.toEuclideanLin.singularValues_nonneg _),
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [add_div, sub_div, mul_div_cancel_left₀ _ hn]

theorem matrixClippedPotential_abs_le (A : Matrix ι ι ℂ)
    {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    |matrixClippedPotential A a R| ≤ max |Real.log a| |Real.log R| := by
  have hnabs : |(Module.finrank ℂ (EuclideanSpace ℂ ι) : ℝ)| =
      (Module.finrank ℂ (EuclideanSpace ℂ ι) : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
  unfold matrixClippedPotential
  rw [abs_div, hnabs]
  calc
    _ ≤ (∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)),
        |clippedLog a R (A.toEuclideanLin.singularValues i ^ 2)|) / _ :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
    _ ≤ (∑ _i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)),
        max |Real.log a| |Real.log R|) / _ :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun _ _ => clippedLog_abs_le ha haR _)
        (Nat.cast_nonneg _)
    _ = _ := by simp

omit [Nonempty ι] in
theorem matrixCutoff_clipped_error_le (A : Matrix ι ι ℂ) (hA : A.det ≠ 0)
    {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) (hR : 1 ≤ R) :
    |matrixCutoffPotential A a - matrixClippedPotential A a R| ≤
      hilbertSchmidtSq A / ((Fintype.card ι : ℝ) * R) := by
  have hnabs : |(Module.finrank ℂ (EuclideanSpace ℂ ι) : ℝ)| =
      (Module.finrank ℂ (EuclideanSpace ℂ ι) : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
  unfold matrixCutoffPotential operatorCutoffPotential matrixClippedPotential
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, hnabs]
  calc
    _ ≤ (∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)),
        |Real.log (max (A.toEuclideanLin.singularValues i) a) -
          clippedLog a R (A.toEuclideanLin.singularValues i ^ 2)|) / _ :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
    _ ≤ (∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)),
        A.toEuclideanLin.singularValues i ^ 2 / R) / _ :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ =>
        cutoffLog_clipped_abs_error_le_sq_div ha haR hR (A.toEuclideanLin.singularValues_nonneg i))
        (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.sum_div, singularValues_sq_sum_eq_energy A.toEuclideanLin
        (toEuclideanLin_injective_of_det_ne_zero A hA), operatorHilbertSchmidtSq_toEuclideanLin,
        finrank_euclideanSpace]
      ring

theorem integrable_matrixClippedPotential {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → Matrix ι ι ℂ)
    (hA : Measurable A) (hdet : ∀ᵐ ω ∂μ, (A ω).det ≠ 0)
    (hE : Integrable (fun ω => hilbertSchmidtSq (A ω)) μ)
    {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    Integrable (fun ω => matrixClippedPotential (A ω) a R) μ := by
  simp_rw [matrixClippedPotential_eq_cutoff_difference _ ha haR]
  exact ((integrable_matrixCutoffPotential μ A hA hdet hE ha).sub
    (integrable_matrixCutoffPotential μ A hA hdet hE (ha.trans_le haR))).add (integrable_const _)

theorem expected_matrixCutoff_clipped_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → Matrix ι ι ℂ)
    (hA : Measurable A) (hdet : ∀ᵐ ω ∂μ, (A ω).det ≠ 0)
    (hE : Integrable (fun ω => hilbertSchmidtSq (A ω)) μ)
    {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) (hR : 1 ≤ R) :
    |(∫ ω, matrixCutoffPotential (A ω) a ∂μ) -
      ∫ ω, matrixClippedPotential (A ω) a R ∂μ| ≤
        (∫ ω, hilbertSchmidtSq (A ω) ∂μ) / ((Fintype.card ι : ℝ) * R) := by
  have hint := integrable_matrixCutoffPotential μ A hA hdet hE ha
  have hc := integrable_matrixClippedPotential μ A hA hdet hE ha haR
  rw [← integral_sub hint hc]
  calc
    _ ≤ ∫ ω, |matrixCutoffPotential (A ω) a - matrixClippedPotential (A ω) a R| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω, hilbertSchmidtSq (A ω) / ((Fintype.card ι : ℝ) * R) ∂μ := by
      apply integral_mono_ae (hint.sub hc).abs (hE.div_const _)
      filter_upwards [hdet] with ω hω
      exact matrixCutoff_clipped_error_le (A ω) hω ha haR hR
    _ = _ := integral_div _ _

end CircularLawSection6
