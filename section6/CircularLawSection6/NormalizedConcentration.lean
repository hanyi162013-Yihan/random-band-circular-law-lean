import CircularLawSection4.PressureProbability
import CircularLawSections56.Section5.TriangularProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # From the actual determinant variance bound to concentration

This uses the existing Section 4 Cauchy--Schwarz estimate and Section 5
triangular-array probability interface. The logarithmic rate itself tends
to zero here; it is not supplied as another asymptotic hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open CircularLawSection4 CircularLawSections56.Section5

noncomputable section

namespace CircularLawSection6

theorem integral_abs_centered_le_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ) :
    (∫ ω, |X ω - ∫ x, X x ∂μ| ∂μ) ≤ Real.sqrt (variance X μ) := by
  have h := integral_maxCenteredAbs_le_sqrt_sum_variance
    (Y := fun _ : Fin 1 => X) (fun _ => hX)
  simpa [maxCenteredAbs, finiteMaxAbs, centered] using h

theorem variance_div_const {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (a : ℝ) :
    variance (fun ω => X ω / a) μ = variance X μ / a ^ 2 := by
  simp only [div_eq_mul_inv, variance_mul_const, inv_pow]

theorem tendsto_logEN_sq_div (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => (Real.log (Real.exp 1 * (N n : ℝ))) ^ 2 / (N n : ℝ))
      atTop (𝓝 0) := by
  have hn : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have h := (Real.tendsto_pow_log_div_mul_add_atTop (Real.exp 1)⁻¹ 0 2
    (inv_ne_zero (Real.exp_pos 1).ne')).comp (hn.const_mul_atTop (Real.exp_pos 1))
  simpa only [Function.comp_def, ← mul_assoc, inv_mul_cancel₀ (Real.exp_pos 1).ne',
    one_mul, add_zero] using h

theorem normalized_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) {N C : ℝ} (hN : 0 < N)
    (hV : variance X μ ≤ C * N * (Real.log (Real.exp 1 * N)) ^ 2) :
    variance (fun ω => X ω / N) μ ≤ C * (Real.log (Real.exp 1 * N)) ^ 2 / N := by
  rw [variance_div_const]
  calc
    _ ≤ (C * N * (Real.log (Real.exp 1 * N)) ^ 2) / N ^ 2 :=
      div_le_div_of_nonneg_right hV (sq_nonneg N)
    _ = _ := by field_simp [hN.ne']; ring

/-- `N log²(eN)` variance gives normalized `L¹` concentration on the literal
varying sample spaces, and hence convergence in probability. -/
theorem concentration_of_logarithmic_variance
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop) (C : ℝ)
    (hX : ∀ n, MemLp (X n) 2 (μ n))
    (hV : ∀ n, variance (X n) (μ n) ≤
      C * (N n : ℝ) * (Real.log (Real.exp 1 * (N n : ℝ))) ^ 2) :
    Tendsto (fun n => ∫ ω,
      |X n ω / (N n : ℝ) - ∫ x, X n x / (N n : ℝ) ∂μ n| ∂μ n) atTop (𝓝 0) ∧
    TendstoInProbabilityTri μ (fun n ω =>
      X n ω / (N n : ℝ) - ∫ x, X n x / (N n : ℝ) ∂μ n) 0 := by
  let Y : ∀ n, Ω n → ℝ := fun n ω => X n ω / (N n : ℝ)
  have hY (n : ℕ) : MemLp (Y n) 2 (μ n) := (hX n).div_const _
  have hv0 : Tendsto (fun n => variance (Y n) (μ n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => variance_nonneg _ _)
      (fun n => normalized_variance_le (μ n) (X n) (by exact_mod_cast hNpos n) (hV n))
    simpa only [mul_zero, mul_div_assoc] using (tendsto_logEN_sq_div N hN).const_mul C
  have hsqrt : Tendsto (fun n => Real.sqrt (variance (Y n) (μ n))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hv0.sqrt
  have hl1 : Tendsto (fun n => ∫ ω, |Y n ω - ∫ x, Y n x ∂μ n| ∂μ n) atTop (𝓝 0) :=
    squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _))
      (fun n => integral_abs_centered_le_sqrt_variance (μ n) (Y n) (hY n)) hsqrt
  refine ⟨hl1, ?_⟩
  apply tendstoInProbabilityTri_of_L1 μ _ 0
    (fun n => ∫ ω, |Y n ω - ∫ x, Y n x ∂μ n| ∂μ n)
  · intro n
    simpa only [sub_zero] using
      (((hY n).integrable (by norm_num : (1 : ENNReal) ≤ 2)).sub (integrable_const _)).abs
  · intro n
    simp only [sub_zero]
    exact le_rfl
  · exact hl1

end CircularLawSection6
