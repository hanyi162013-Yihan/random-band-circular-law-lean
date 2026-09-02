import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Fixed-space probability bridges

This file contains generic convergence-in-measure bridges on one fixed finite measure
space.  They are deliberately separate from the triangular-array interfaces needed by
the manuscript: no identification of varying sample spaces is hidden here.

The first two results are Markov/Chebyshev estimates for first and second norm moments.
The remaining results specialize them to deterministic centering and to an explicit
variance-type upper bound for centered second moments.
-/

open Filter Topology
open MeasureTheory

namespace CircularLawSections56.Section5

variable {Ω E : Type*} [MeasurableSpace Ω]

/-- Vanishing `L¹` error implies convergence in measure on a fixed finite measure space.

All measurability needed by Markov's inequality is included in the explicit
integrability hypothesis. -/
theorem tendstoInMeasure_of_integral_norm_tendsto_zero
    [NormedAddCommGroup E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → E) (limit : Ω → E)
    (hIntegrable : ∀ n, Integrable (fun ω => ‖X n ω - limit ω‖) μ)
    (hL1 : Tendsto (fun n => ∫ ω, ‖X n ω - limit ω‖ ∂μ)
      atTop (𝓝 0)) :
    TendstoInMeasure μ X atTop limit := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hUpper :
      Tendsto (fun n => (∫ ω, ‖X n ω - limit ω‖ ∂μ) / ε)
        atTop (𝓝 0) := by
    simpa using hL1.div_const ε
  apply squeeze_zero
    (g := fun n => (∫ ω, ‖X n ω - limit ω‖ ∂μ) / ε)
  · intro n
    exact measureReal_nonneg
  · intro n
    apply (le_div_iff₀ hε).2
    have hMarkov := mul_meas_ge_le_integral_of_nonneg
      (μ := μ)
      (Eventually.of_forall fun ω => norm_nonneg (X n ω - limit ω))
      (hIntegrable n) ε
    simpa only [mul_comm] using hMarkov
  · exact hUpper

/-- Vanishing second norm moment implies convergence in measure on a fixed finite
measure space.

This is Chebyshev's estimate in the form used for normalized variance bounds. -/
theorem tendstoInMeasure_of_integral_norm_sq_tendsto_zero
    [NormedAddCommGroup E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → E) (limit : Ω → E)
    (hIntegrable : ∀ n,
      Integrable (fun ω => ‖X n ω - limit ω‖ ^ 2) μ)
    (hSecondMoment : Tendsto
      (fun n => ∫ ω, ‖X n ω - limit ω‖ ^ 2 ∂μ)
      atTop (𝓝 0)) :
    TendstoInMeasure μ X atTop limit := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hUpper :
      Tendsto (fun n => (∫ ω, ‖X n ω - limit ω‖ ^ 2 ∂μ) / ε ^ 2)
        atTop (𝓝 0) := by
    simpa using hSecondMoment.div_const (ε ^ 2)
  apply squeeze_zero
    (g := fun n => (∫ ω, ‖X n ω - limit ω‖ ^ 2 ∂μ) / ε ^ 2)
  · intro n
    exact measureReal_nonneg
  · intro n
    have hSet :
        {ω | ε ^ 2 ≤ ‖X n ω - limit ω‖ ^ 2} =
          {ω | ε ≤ ‖X n ω - limit ω‖} := by
      ext ω
      exact sq_le_sq₀ hε.le (norm_nonneg (X n ω - limit ω))
    apply (le_div_iff₀ hεsq).2
    have hMarkov := mul_meas_ge_le_integral_of_nonneg
      (μ := μ)
      (Eventually.of_forall fun ω => sq_nonneg ‖X n ω - limit ω‖)
      (hIntegrable n) (ε ^ 2)
    rw [hSet] at hMarkov
    simpa only [mul_comm] using hMarkov
  · exact hUpper

/-- A real-valued second moment around a deterministic center sequence gives
concentration of the centered variables at zero. -/
theorem tendstoInMeasure_centered_zero_of_secondMoment
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (center : ℕ → ℝ)
    (hIntegrable : ∀ n,
      Integrable (fun ω => (X n ω - center n) ^ 2) μ)
    (hSecondMoment : Tendsto
      (fun n => ∫ ω, (X n ω - center n) ^ 2 ∂μ)
      atTop (𝓝 0)) :
    TendstoInMeasure μ (fun n ω => X n ω - center n)
      atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_integral_norm_sq_tendsto_zero
    μ (fun n ω => X n ω - center n) (fun _ => 0)
  · intro n
    simpa only [sub_zero, Real.norm_eq_abs, sq_abs] using hIntegrable n
  · simpa only [sub_zero, Real.norm_eq_abs, sq_abs] using hSecondMoment

/-- A vanishing deterministic upper bound for centered second moments gives
concentration in measure.

This is the variance-type interface used when an upstream theorem has already bounded
the actual variance or centered second moment by `varianceBound`.  No probability
variance API is needed in this lightweight module. -/
theorem tendstoInMeasure_centered_zero_of_secondMoment_bound
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (center varianceBound : ℕ → ℝ)
    (hIntegrable : ∀ n,
      Integrable (fun ω => (X n ω - center n) ^ 2) μ)
    (hSecondMomentLe : ∀ n,
      (∫ ω, (X n ω - center n) ^ 2 ∂μ) ≤ varianceBound n)
    (hVarianceBoundZero : Tendsto varianceBound atTop (𝓝 0)) :
    TendstoInMeasure μ (fun n ω => X n ω - center n)
      atTop (fun _ => 0) := by
  apply tendstoInMeasure_centered_zero_of_secondMoment μ X center hIntegrable
  exact squeeze_zero
    (fun n => integral_nonneg fun ω => sq_nonneg (X n ω - center n))
    hSecondMomentLe hVarianceBoundZero

/-- Deterministic centers may be reattached to a centered convergence-in-measure
statement.

If `Xₙ - centerₙ` converges in measure to zero and `centerₙ → c`, then `Xₙ` converges
in measure to the constant `c`. -/
theorem tendstoInMeasure_of_centered_concentration
    [NormedAddCommGroup E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → E) (center : ℕ → E) (c : E)
    (hCentered : TendstoInMeasure μ
      (fun n ω => X n ω - center n) atTop (fun _ => 0))
    (hCenter : Tendsto center atTop (𝓝 c)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hCenteredMeasure :
      Tendsto
        (fun n => μ.real {ω | ε / 2 ≤ ‖X n ω - center n‖})
        atTop (𝓝 0) := by
    have h := (tendstoInMeasure_iff_measureReal_norm.mp hCentered)
      (ε / 2) (half_pos hε)
    simpa only [sub_zero] using h
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hCenter
    (ε / 2) (half_pos hε)
  apply squeeze_zero'
    (g := fun n => μ.real {ω | ε / 2 ≤ ‖X n ω - center n‖})
  · exact Eventually.of_forall fun n => measureReal_nonneg
  · filter_upwards [eventually_atTop.2 ⟨N, hN⟩] with n hn
    refine measureReal_mono ?_ (by finiteness)
    intro ω hω
    have hCenterClose : ‖center n - c‖ < ε / 2 := by
      simpa only [dist_eq_norm] using hn
    have hTriangle :
        ‖X n ω - c‖ ≤
          ‖X n ω - center n‖ + ‖center n - c‖ := by
      calc
        ‖X n ω - c‖ =
            ‖(X n ω - center n) + (center n - c)‖ := by
          congr 1
          abel
        _ ≤ ‖X n ω - center n‖ + ‖center n - c‖ :=
          norm_add_le _ _
    change ε ≤ ‖X n ω - c‖ at hω
    change ε / 2 ≤ ‖X n ω - center n‖
    linarith
  · exact hCenteredMeasure

/-- A variance-type second-moment bound plus convergence of deterministic centers gives
convergence in measure to the limiting center. -/
theorem tendstoInMeasure_of_secondMoment_bound_and_center_tendsto
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ) (center varianceBound : ℕ → ℝ) (c : ℝ)
    (hIntegrable : ∀ n,
      Integrable (fun ω => (X n ω - center n) ^ 2) μ)
    (hSecondMomentLe : ∀ n,
      (∫ ω, (X n ω - center n) ^ 2 ∂μ) ≤ varianceBound n)
    (hVarianceBoundZero : Tendsto varianceBound atTop (𝓝 0))
    (hCenter : Tendsto center atTop (𝓝 c)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  exact tendstoInMeasure_of_centered_concentration
    μ X center c
    (tendstoInMeasure_centered_zero_of_secondMoment_bound
      μ X center varianceBound hIntegrable hSecondMomentLe hVarianceBoundZero)
    hCenter

end CircularLawSections56.Section5
