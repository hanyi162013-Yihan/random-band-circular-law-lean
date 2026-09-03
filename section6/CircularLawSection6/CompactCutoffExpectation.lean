import CircularLawSection6.MatrixClippedCutoff
import CircularLawSection6.BoundedProbabilityExpectation

/-! # Fixed cutoff expectation from bounded squared-singular convergence

The random-matrix input is convergence in probability against bounded
continuous tests of the actual squared singular values. All expectation
convergence, matrix upper-tail removal, and limiting-law upper-tail removal
are proved here using second moments. The random-matrix comparison input
itself, and identification of its limiting singular law, remain visible.
-/

open MeasureTheory Filter Topology Set ShortRingAnchor TaoVuReplacement
open CircularLawSections56.Section5
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem tendsto_of_uniform_upper_truncations
    (F : ℕ → ℝ) (G : ℝ → ℕ → ℝ) (c : ℝ → ℝ) (target C D a : ℝ)
    (herror : ∀ R, a ≤ R → 1 ≤ R → ∀ n, |F n - G R n| ≤ C / R)
    (hG : ∀ R, a ≤ R → 1 ≤ R → Tendsto (G R) atTop (𝓝 (c R)))
    (hc : ∀ R, a ≤ R → 1 ≤ R → |c R - target| ≤ D / R) :
    Tendsto F atTop (𝓝 target) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hlim : Tendsto (fun R : ℝ => (C + D) / R) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop (C + D)
  have hsmall : ∀ᶠ R : ℝ in atTop, a ≤ R ∧ 1 ≤ R ∧ (C + D) / R < ε / 2 := by
    filter_upwards [eventually_ge_atTop a, eventually_ge_atTop (1 : ℝ),
      hlim.eventually (gt_mem_nhds (half_pos hε))] with R hRa hR hsmall
    exact ⟨hRa, hR, hsmall⟩
  obtain ⟨R, hRa, hR, hsmall⟩ := hsmall.exists
  filter_upwards [(hG R hRa hR).eventually (Metric.ball_mem_nhds (c R) (half_pos hε))] with n hn
  have hmiddle : |G R n - c R| < ε / 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hn
  have h1 := herror R hRa hR n
  have h2 := hc R hRa hR
  have h3 := abs_sub_le (F n) (G R n) target
  have h4 := abs_sub_le (G R n) (c R) target
  rw [Real.dist_eq]
  rw [add_div] at hsmall
  linarith

def matrixSquaredSingularAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (φ : ℝ → ℝ) : ℝ :=
  (∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)),
    φ (A.toEuclideanLin.singularValues i ^ 2)) /
      (Module.finrank ℂ (EuclideanSpace ℂ ι) : ℝ)

/-- This is a bounded-test probability hypothesis, not an expectation
limit and not a hard-edge hypothesis. The cutoff conclusion is derived. -/
theorem matrixCutoff_expectation_of_squared_singular_probability
    {Ω ι : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Nonempty (ι n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (ι n) (ι n) ℂ) (hA : ∀ n, Measurable (A n))
    (hdet : ∀ n, ∀ᵐ ω ∂μ n, (A n ω).det ≠ 0)
    (hE : ∀ n, Integrable (fun ω => hilbertSchmidtSq (A n ω)) (μ n))
    (C : ℝ) (hbound : ∀ n,
      (∫ ω, hilbertSchmidtSq (A n ω) ∂μ n) / (Fintype.card (ι n) : ℝ) ≤ C)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνpos : ∀ᵐ s ∂ν, 0 ≤ s) (hνsecond : Integrable (fun s : ℝ => s ^ 2) ν)
    (hweak : ∀ φ : ℝ → ℝ, Continuous φ → (∃ B : ℝ, ∀ x, |φ x| ≤ B) →
      TendstoInProbabilityTri μ (fun n ω => matrixSquaredSingularAverage (A n ω) φ)
        (∫ s, φ (s ^ 2) ∂ν)) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => ∫ ω, matrixCutoffPotential (A n ω) a ∂μ n)
      atTop (𝓝 (∫ s, Real.log (max s a) ∂ν)) := by
  apply tendsto_of_uniform_upper_truncations
    (fun n => ∫ ω, matrixCutoffPotential (A n ω) a ∂μ n)
    (fun R n => ∫ ω, matrixClippedPotential (A n ω) a R ∂μ n)
    (fun R => ∫ s, clippedLog a R (s ^ 2) ∂ν)
    (∫ s, Real.log (max s a) ∂ν) C (∫ s : ℝ, s ^ 2 ∂ν) a
  · intro R haR hR n
    calc
      _ ≤ (∫ ω, hilbertSchmidtSq (A n ω) ∂μ n) / ((Fintype.card (ι n) : ℝ) * R) :=
        expected_matrixCutoff_clipped_error (μ n) (A n) (hA n) (hdet n) (hE n) ha haR hR
      _ = ((∫ ω, hilbertSchmidtSq (A n ω) ∂μ n) / (Fintype.card (ι n) : ℝ)) / R := by ring
      _ ≤ C / R := div_le_div_of_nonneg_right (hbound n) (zero_le_one.trans hR)
  · intro R haR _hR
    apply tendsto_expectation_of_ae_bounded_probability μ
      (fun n ω => matrixClippedPotential (A n ω) a R)
      (fun n => (integrable_matrixClippedPotential (μ n) (A n) (hA n) (hdet n) (hE n)
        ha haR).aestronglyMeasurable)
      (max |Real.log a| |Real.log R|) (∫ s, clippedLog a R (s ^ 2) ∂ν)
    · exact fun n => ae_of_all (μ n) fun ω => matrixClippedPotential_abs_le (A n ω) ha haR
    · exact hweak (clippedLog a R) (continuous_clippedLog ha haR)
        ⟨max |Real.log a| |Real.log R|, clippedLog_abs_le ha haR⟩
  · intro R haR hR
    rw [abs_sub_comm]
    exact (expected_cutoffLog_clipped_error ν id measurable_id hνpos hνsecond ha haR hR).2

end CircularLawSection6
