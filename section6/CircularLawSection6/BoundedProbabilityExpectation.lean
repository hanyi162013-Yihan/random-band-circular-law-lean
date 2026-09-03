import CircularLawSections56.Section5.TriangularProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Bounded probability limits on varying spaces give expectation limits

The compact singular-value test is bounded independently of the matrix
dimension. This file proves the probability-to-expectation passage for
the actual triangular array, without a common probability space or an
expectation-convergence assumption.
-/

open MeasureTheory Filter Topology Set
open CircularLawSections56.Section5

noncomputable section

namespace CircularLawSection6

theorem integral_abs_sub_le_threshold_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (B target ε : ℝ) (hε : 0 ≤ ε)
    (hB : ∀ᵐ ω ∂μ, |X ω| ≤ B) :
    Integrable (fun ω => |X ω - target|) μ ∧
      (∫ ω, |X ω - target| ∂μ) ≤
        ε + (B + |target|) * μ.real {ω | ε ≤ |X ω - target|} := by
  classical
  let bad : Set Ω := {ω | ε ≤ |X ω - target|}
  have hmeas : Measurable (fun ω => |X ω - target|) := by
    simpa only [Real.norm_eq_abs] using (hX.sub_const target).norm
  have hbad : MeasurableSet bad := measurableSet_le measurable_const hmeas
  have hbound : ∀ᵐ ω ∂μ, |X ω - target| ≤ B + |target| := by
    filter_upwards [hB] with ω hω
    exact (abs_sub _ _).trans (add_le_add hω le_rfl)
  have hint : Integrable (fun ω => |X ω - target|) μ :=
    (integrable_const (B + |target|)).mono' hmeas.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs, abs_abs] using hbound)
  refine ⟨hint, ?_⟩
  have hind : Integrable (bad.indicator fun _ : Ω => B + |target|) μ :=
    (integrable_const _).indicator hbad
  calc
    _ ≤ ∫ ω, ε + bad.indicator (fun _ : Ω => B + |target|) ω ∂μ := by
      apply integral_mono_ae hint ((integrable_const ε).add hind)
      filter_upwards [hbound] with ω hω
      change |X ω - target| ≤ ε + bad.indicator (fun _ : Ω => B + |target|) ω
      by_cases hb : ω ∈ bad
      · rw [indicator_of_mem hb]
        linarith
      · rw [indicator_of_notMem hb, add_zero]
        exact (not_le.mp hb).le
    _ = _ := by
      rw [integral_add (integrable_const ε) hind, integral_const,
        integral_indicator hbad, setIntegral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rw [mul_comm]

theorem tendsto_L1_of_bounded_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (hX : ∀ n, Measurable (X n))
    (B target : ℝ) (hB : ∀ n, ∀ᵐ ω ∂μ n, |X n ω| ≤ B)
    (hprob : TendstoInProbabilityTri μ X target) :
    Tendsto (fun n => ∫ ω, |X n ω - target| ∂μ n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hlim : Tendsto
      (fun n => (B + |target|) * (μ n).real {ω | ε / 2 ≤ |X n ω - target|})
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (hprob (ε / 2) (half_pos hε)).const_mul (B + |target|)
  filter_upwards [hlim.eventually (gt_mem_nhds (half_pos hε))] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  have hb := (integral_abs_sub_le_threshold_probability (μ n) (X n) (hX n)
    B target (ε / 2) (half_pos hε).le (hB n)).2
  linarith

theorem tendsto_expectation_of_bounded_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (hX : ∀ n, Measurable (X n))
    (B target : ℝ) (hB : ∀ n, ∀ᵐ ω ∂μ n, |X n ω| ≤ B)
    (hprob : TendstoInProbabilityTri μ X target) :
    Tendsto (fun n => ∫ ω, X n ω ∂μ n) atTop (𝓝 target) := by
  have hL1 := tendsto_L1_of_bounded_probability μ X hX B target hB hprob
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [hL1.eventually (gt_mem_nhds hε)] with n hn
  have hXi : Integrable (X n) (μ n) :=
    (integrable_const B).mono' (hX n).aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hB n)
  have h := abs_integral_le_integral_abs (f := fun ω => X n ω - target) (μ := μ n)
  rw [integral_sub hXi (integrable_const target), integral_const] at h
  simpa only [Real.dist_eq, probReal_univ, smul_eq_mul, one_mul] using h.trans_lt hn

theorem tendstoInProbabilityTri_congr_ae
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (X Y : ∀ n, Ω n → ℝ) (hXY : ∀ n, X n =ᵐ[μ n] Y n) (target : ℝ)
    (hprob : TendstoInProbabilityTri μ X target) :
    TendstoInProbabilityTri μ Y target := by
  intro ε hε
  apply (hprob ε hε).congr'
  apply Eventually.of_forall
  intro n
  apply measureReal_congr
  filter_upwards [hXY n] with ω hω
  change (ε ≤ |X n ω - target|) = (ε ≤ |Y n ω - target|)
  rw [hω]

theorem tendsto_expectation_of_ae_bounded_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (hX : ∀ n, AEStronglyMeasurable (X n) (μ n))
    (B target : ℝ) (hB : ∀ n, ∀ᵐ ω ∂μ n, |X n ω| ≤ B)
    (hprob : TendstoInProbabilityTri μ X target) :
    Tendsto (fun n => ∫ ω, X n ω ∂μ n) atTop (𝓝 target) := by
  let Y : ∀ n, Ω n → ℝ := fun n => (hX n).mk (X n)
  have hXY : ∀ n, X n =ᵐ[μ n] Y n := fun n => (hX n).ae_eq_mk
  have hYB : ∀ n, ∀ᵐ ω ∂μ n, |Y n ω| ≤ B := by
    intro n
    filter_upwards [hXY n, hB n] with ω heq hω
    simpa only [← heq] using hω
  have hp := tendstoInProbabilityTri_congr_ae μ X Y hXY target hprob
  have hlim := tendsto_expectation_of_bounded_probability μ Y
    (fun n => (hX n).stronglyMeasurable_mk.measurable) B target hYB hp
  apply hlim.congr'
  exact Eventually.of_forall fun n => integral_congr_ae (hXY n).symm

end CircularLawSection6
