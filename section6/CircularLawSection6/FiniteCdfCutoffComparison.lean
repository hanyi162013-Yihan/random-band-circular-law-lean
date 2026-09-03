import CircularLawSection6.CompactCutoffExpectation
import ShortRingAnchor.BulkClippedLog

/-! # Finite-matrix CDF comparison gives cutoff expectation comparison

The source comparison is between the squared-singular CDFs of two finite
matrices, not directly a limiting measure. This file connects that exact
quantity to the actual cutoff expectations. It reuses the proved Section 3
finite-CDF integration-by-parts inequality; bounded probability convergence
and the two matrix energies remove both expectation and upper-tail gaps.
-/

open MeasureTheory Filter Topology ShortRingAnchor TaoVuReplacement
open CircularLawSections56.Section5
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem tendstoInProbabilityTri_of_abs_le_mul
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X Y : ∀ n, Ω n → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ n ω, |X n ω| ≤ K * |Y n ω|)
    (hY : TendstoInProbabilityTri μ Y 0) : TendstoInProbabilityTri μ X 0 := by
  intro ε hε
  by_cases hzero : K = 0
  · have hX (n : ℕ) (ω : Ω n) : X n ω = 0 := by
      have h := hbound n ω
      rw [hzero, zero_mul] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    simpa only [hX, sub_zero, abs_zero, not_le.mpr hε, Set.ofPred_false, measureReal_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have hKpos := hK.lt_of_ne' hzero
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) (hY (ε / K) (div_pos hε hKpos))
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    change ε ≤ |X n ω - 0| at hω
    rw [sub_zero] at hω
    change ε / K ≤ |Y n ω - 0|
    rw [sub_zero]
    apply (div_le_iff₀ hKpos).mpr
    nlinarith [hbound n ω]

def matrixSquaredSingularCdfDistanceOn
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (R : ℝ) : ℝ :=
  empiricalCdfDistanceOn 0 (R ^ 2)
    (fun i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)) => A.toEuclideanLin.singularValues i ^ 2)
    (fun i : Fin (Module.finrank ℂ (EuclideanSpace ℂ κ)) => B.toEuclideanLin.singularValues i ^ 2)

theorem matrixClipped_difference_le_cdf
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    |matrixClippedPotential A a R - matrixClippedPotential B a R| ≤
      matrixSquaredSingularCdfDistanceOn A B R * (Real.log R - Real.log a) := by
  let : NeZero (Module.finrank ℂ (EuclideanSpace ℂ ι)) := ⟨by simp⟩
  let : NeZero (Module.finrank ℂ (EuclideanSpace ℂ κ)) := ⟨by simp⟩
  simpa only [matrixClippedPotential, matrixSquaredSingularCdfDistanceOn,
    empiricalClippedLog, empiricalAverage, Fintype.card_fin] using
    abs_empiricalClippedLog_sub_le_cdfDistanceOn_zero_sq ha haR
      (fun i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)) => A.toEuclideanLin.singularValues i ^ 2)
      (fun i : Fin (Module.finrank ℂ (EuclideanSpace ℂ κ)) => B.toEuclideanLin.singularValues i ^ 2)

theorem matrixClipped_expectation_difference_of_cdf_probability
    {Ω ι κ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Nonempty (ι n)]
    [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)] [∀ n, Nonempty (κ n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (ι n) (ι n) ℂ) (B : ∀ n, Ω n → Matrix (κ n) (κ n) ℂ)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (hAdet : ∀ n, ∀ᵐ ω ∂μ n, (A n ω).det ≠ 0) (hBdet : ∀ n, ∀ᵐ ω ∂μ n, (B n ω).det ≠ 0)
    (hAE : ∀ n, Integrable (fun ω => hilbertSchmidtSq (A n ω)) (μ n))
    (hBE : ∀ n, Integrable (fun ω => hilbertSchmidtSq (B n ω)) (μ n))
    {a R : ℝ} (ha : 0 < a) (haR : a ≤ R)
    (hcdf : TendstoInProbabilityTri μ (fun n ω => matrixSquaredSingularCdfDistanceOn (A n ω) (B n ω) R) 0) :
    Tendsto (fun n => (∫ ω, matrixClippedPotential (A n ω) a R ∂μ n) -
      ∫ ω, matrixClippedPotential (B n ω) a R ∂μ n) atTop (𝓝 0) := by
  have hiA (n : ℕ) := integrable_matrixClippedPotential (μ n) (A n) (hA n) (hAdet n) (hAE n) ha haR
  have hiB (n : ℕ) := integrable_matrixClippedPotential (μ n) (B n) (hB n) (hBdet n) (hBE n) ha haR
  have hw : 0 ≤ Real.log R - Real.log a := sub_nonneg.mpr (Real.log_le_log ha haR)
  have hprob := tendstoInProbabilityTri_of_abs_le_mul μ
    (fun n ω => matrixClippedPotential (A n ω) a R - matrixClippedPotential (B n ω) a R)
    (fun n ω => matrixSquaredSingularCdfDistanceOn (A n ω) (B n ω) R) hw
    (fun n ω => (matrixClipped_difference_le_cdf (A n ω) (B n ω) ha haR).trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (le_abs_self _) hw)) hcdf
  have hlim := tendsto_expectation_of_ae_bounded_probability μ
    (fun n ω => matrixClippedPotential (A n ω) a R - matrixClippedPotential (B n ω) a R)
    (fun n => ((hiA n).sub (hiB n)).aestronglyMeasurable)
    (2 * max |Real.log a| |Real.log R|) 0 (fun n => ae_of_all (μ n) fun ω => by
      have h := abs_sub (matrixClippedPotential (A n ω) a R) (matrixClippedPotential (B n ω) a R)
      have h1 := matrixClippedPotential_abs_le (A n ω) ha haR
      have h2 := matrixClippedPotential_abs_le (B n ω) ha haR
      linarith) hprob
  simpa only [integral_sub (hiA _) (hiB _)] using hlim

theorem matrixCutoff_expectation_difference_of_cdf_probability
    {Ω ι κ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Nonempty (ι n)]
    [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)] [∀ n, Nonempty (κ n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (ι n) (ι n) ℂ) (B : ∀ n, Ω n → Matrix (κ n) (κ n) ℂ)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (hAdet : ∀ n, ∀ᵐ ω ∂μ n, (A n ω).det ≠ 0) (hBdet : ∀ n, ∀ᵐ ω ∂μ n, (B n ω).det ≠ 0)
    (hAE : ∀ n, Integrable (fun ω => hilbertSchmidtSq (A n ω)) (μ n))
    (hBE : ∀ n, Integrable (fun ω => hilbertSchmidtSq (B n ω)) (μ n))
    (CA CB : ℝ)
    (hAbound : ∀ n, (∫ ω, hilbertSchmidtSq (A n ω) ∂μ n) / (Fintype.card (ι n) : ℝ) ≤ CA)
    (hBbound : ∀ n, (∫ ω, hilbertSchmidtSq (B n ω) ∂μ n) / (Fintype.card (κ n) : ℝ) ≤ CB)
    (hcdf : ∀ R : ℝ, 1 ≤ R → TendstoInProbabilityTri μ
      (fun n ω => matrixSquaredSingularCdfDistanceOn (A n ω) (B n ω) R) 0)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (∫ ω, matrixCutoffPotential (A n ω) a ∂μ n) -
      ∫ ω, matrixCutoffPotential (B n ω) a ∂μ n) atTop (𝓝 0) := by
  apply tendsto_of_uniform_upper_truncations _
    (fun R n => (∫ ω, matrixClippedPotential (A n ω) a R ∂μ n) -
      ∫ ω, matrixClippedPotential (B n ω) a R ∂μ n) (fun _ => 0) 0 (CA + CB) 0 a
  · intro R haR hR n
    have h1 := expected_matrixCutoff_clipped_error (μ n) (A n) (hA n) (hAdet n) (hAE n) ha haR hR
    have h2 := expected_matrixCutoff_clipped_error (μ n) (B n) (hB n) (hBdet n) (hBE n) ha haR hR
    have hb1 : |(∫ ω, matrixCutoffPotential (A n ω) a ∂μ n) -
        ∫ ω, matrixClippedPotential (A n ω) a R ∂μ n| ≤ CA / R := by
      rw [← div_div] at h1
      exact h1.trans (div_le_div_of_nonneg_right (hAbound n) (zero_le_one.trans hR))
    have hb2 : |(∫ ω, matrixCutoffPotential (B n ω) a ∂μ n) -
        ∫ ω, matrixClippedPotential (B n ω) a R ∂μ n| ≤ CB / R := by
      rw [← div_div] at h2
      exact h2.trans (div_le_div_of_nonneg_right (hBbound n) (zero_le_one.trans hR))
    have h := abs_sub
      ((∫ ω, matrixCutoffPotential (A n ω) a ∂μ n) - ∫ ω, matrixClippedPotential (A n ω) a R ∂μ n)
      ((∫ ω, matrixCutoffPotential (B n ω) a ∂μ n) - ∫ ω, matrixClippedPotential (B n ω) a R ∂μ n)
    have heq (x y u v : ℝ) : (x - y) - (u - v) = (x - u) - (y - v) := by ring
    rw [heq, add_div]
    exact h.trans (add_le_add hb1 hb2)
  · intro R haR hR
    exact matrixClipped_expectation_difference_of_cdf_probability μ A B hA hB hAdet hBdet hAE hBE
      ha haR (hcdf R hR)
  · intro R _ _
    simp

end CircularLawSection6
