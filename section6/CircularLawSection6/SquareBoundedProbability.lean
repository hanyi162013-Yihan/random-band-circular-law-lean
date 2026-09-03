import CircularLawSection6.BoundedProbabilityExpectation
import Mathlib.MeasureTheory.Function.L2Space

/-! # A uniform second moment upgrades triangular probability to L1

The threshold estimate is proved directly by splitting small values,
moderate values on the bad event, and large values controlled by the
second moment. This is the expectation-uniform-integrability step needed
to reuse a negative-moment tightness input; tightness alone is not treated
as an expectation bound.
-/

open MeasureTheory Filter Topology Set
open CircularLawSections56.Section5

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem integral_abs_le_secondMoment_threshold_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hX2 : MemLp X 2 μ)
    {ε M : ℝ} (hε : 0 ≤ ε) (hM : 0 < M) :
    (∫ ω, |X ω| ∂μ) ≤ ε + (∫ ω, X ω ^ 2 ∂μ) / M + M * μ.real {ω | ε ≤ |X ω|} := by
  classical
  let bad : Set Ω := {ω | ε ≤ |X ω|}
  have hbad : MeasurableSet bad := by
    exact measurableSet_le measurable_const (by simpa only [Real.norm_eq_abs] using hX.norm)
  have hsq := (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mp hX2
  have hind : Integrable (bad.indicator fun _ : Ω => M) μ := (integrable_const M).indicator hbad
  have habs : Integrable (fun ω => |X ω|) μ := (hX2.integrable (by norm_num)).abs
  calc
    _ ≤ ∫ ω, ε + X ω ^ 2 / M + bad.indicator (fun _ : Ω => M) ω ∂μ := by
      apply integral_mono habs (((integrable_const ε).add (hsq.div_const M)).add hind)
      intro ω
      change |X ω| ≤ ε + X ω ^ 2 / M + bad.indicator (fun _ : Ω => M) ω
      have hpos : 0 ≤ X ω ^ 2 / M := div_nonneg (sq_nonneg _) hM.le
      by_cases hb : ω ∈ bad
      · rw [indicator_of_mem hb]
        by_cases hm : |X ω| ≤ M
        · linarith
        · have hlarge : |X ω| ≤ X ω ^ 2 / M := by
            apply (le_div_iff₀ hM).mpr
            have hm' := le_of_lt (not_le.mp hm)
            nlinarith [sq_abs (X ω), mul_le_mul_of_nonneg_left hm' (abs_nonneg (X ω))]
          linarith
      · rw [indicator_of_notMem hb, add_zero]
        have hsmall : |X ω| < ε := not_le.mp hb
        linarith
    _ = _ := by
      have hsum := integral_add ((integrable_const ε).add (hsq.div_const M)) hind
      simp only [Pi.add_apply] at hsum
      rw [hsum,
        integral_add (integrable_const ε) (hsq.div_const M), integral_const, integral_div,
        integral_indicator hbad, setIntegral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rw [mul_comm (μ.real bad) M]

theorem tendsto_L1_of_uniform_secondMoment_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (hX : ∀ n, Measurable (X n)) (hX2 : ∀ n, MemLp (X n) 2 (μ n))
    (C : ℝ) (hbound : ∀ n, (∫ ω, X n ω ^ 2 ∂μ n) ≤ C)
    (hprob : TendstoInProbabilityTri μ X 0) :
    Tendsto (fun n => ∫ ω, |X n ω| ∂μ n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  have hlim : Tendsto (fun M : ℝ => C / M) atTop (𝓝 0) := tendsto_id.const_div_atTop C
  have hlarge : ∀ᶠ M : ℝ in atTop, 0 < M ∧ C / M < ε / 3 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hlim.eventually (gt_mem_nhds hthird)] with M hM hC
    exact ⟨hM, hC⟩
  obtain ⟨M, hM, hC⟩ := hlarge.exists
  have hp : Tendsto (fun n => M * (μ n).real {ω | ε / 3 ≤ |X n ω|}) atTop (𝓝 0) := by
    simpa only [sub_zero, mul_zero] using (hprob (ε / 3) hthird).const_mul M
  filter_upwards [hp.eventually (gt_mem_nhds hthird)] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  have h := integral_abs_le_secondMoment_threshold_probability (μ n) (X n) (hX n) (hX2 n) hthird.le hM
  have hb := div_le_div_of_nonneg_right (hbound n) hM.le
  linarith

theorem tendsto_L1_of_ae_uniform_secondMoment_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (hX2 : ∀ n, MemLp (X n) 2 (μ n))
    (C : ℝ) (hbound : ∀ n, (∫ ω, X n ω ^ 2 ∂μ n) ≤ C)
    (hprob : TendstoInProbabilityTri μ X 0) :
    Tendsto (fun n => ∫ ω, |X n ω| ∂μ n) atTop (𝓝 0) := by
  let Y : ∀ n, Ω n → ℝ := fun n => (hX2 n).aestronglyMeasurable.mk (X n)
  have hXY : ∀ n, X n =ᵐ[μ n] Y n := fun n => (hX2 n).aestronglyMeasurable.ae_eq_mk
  have hY2 : ∀ n, MemLp (Y n) 2 (μ n) := fun n => (hX2 n).ae_eq (hXY n)
  have hYbound : ∀ n, (∫ ω, Y n ω ^ 2 ∂μ n) ≤ C := by
    intro n
    have heq : (∫ ω, Y n ω ^ 2 ∂μ n) = ∫ ω, X n ω ^ 2 ∂μ n := by
      apply integral_congr_ae
      filter_upwards [hXY n] with ω hω
      rw [hω]
    rw [heq]
    exact hbound n
  have hlim := tendsto_L1_of_uniform_secondMoment_probability μ Y
    (fun n => (hX2 n).aestronglyMeasurable.measurable_mk) hY2 C hYbound
    (tendstoInProbabilityTri_congr_ae μ X Y hXY 0 hprob)
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  apply integral_congr_ae
  filter_upwards [hXY n] with ω hω
  rw [hω]

end CircularLawSection6
