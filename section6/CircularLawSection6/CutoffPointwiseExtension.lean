import CircularLawSection6.WeightedCyclicPointwiseNonzero
import CircularLawSection6.GinibrePointwiseNonzero
import CircularLawSection6.CutoffIntegrability
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Extending cutoff limits from planar a.e. shifts to every shift

At a positive cutoff, normalized singular-value logarithms are uniformly
Lipschitz in a scalar spectral shift.  Since a full Lebesgue-measure set is
dense, convergence on that set extends to every fixed complex parameter.
-/

open MeasureTheory Filter Topology TaoVuReplacement

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem tendsto_zero_everywhere_of_ae_lipschitz
    (F : ℕ → ℂ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hAE : ∀ᵐ z ∂(volume : Measure ℂ), Tendsto (fun n => F n z) atTop (𝓝 0))
    (hLip : ∀ n z w, |F n z - F n w| ≤ C * dist z w)
    (z : ℂ) : Tendsto (fun n => F n z) atTop (𝓝 0) := by
  have hdense : Dense {w : ℂ | Tendsto (fun n => F n w) atTop (𝓝 0)} :=
    (volume : Measure ℂ).dense_of_ae hAE
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hdenom : 0 < 2 * (C + 1) := by positivity
  have hδ : 0 < ε / (2 * (C + 1)) := div_pos hε hdenom
  obtain ⟨w, hw, hzw⟩ := hdense.exists_dist_lt z hδ
  have hwε := (Metric.tendsto_atTop.1 hw) (ε / 2) (half_pos hε)
  filter_upwards [hwε] with n hn
  rw [Real.dist_eq, sub_zero] at hn ⊢
  have hfirst : C * dist z w < ε / 2 := by
    calc
      C * dist z w ≤ C * (ε / (2 * (C + 1))) :=
        mul_le_mul_of_nonneg_left hzw.le hC
      _ = (C * ε) / (2 * (C + 1)) := by ring
      _ < ε / 2 := by
        apply (div_lt_iff₀ hdenom).2
        nlinarith
  calc
    |F n z| = |(F n z - F n w) + F n w| := by rw [sub_add_cancel]
    _ ≤ |F n z - F n w| + |F n w| := abs_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt ((hLip n z w).trans hfirst.le) hn
    _ = ε := by ring

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [MeasurableSpace Ω]

theorem hilbertSchmidtSq_smul_one (c : ℂ) :
    hilbertSchmidtSq (c • (1 : Matrix ι ι ℂ)) = ‖c‖ ^ 2 * (Fintype.card ι : ℝ) := by
  rw [hilbertSchmidtSq_smul]
  congr 1
  unfold hilbertSchmidtSq
  simp [Matrix.one_apply]

/-- Expected positive-cutoff potentials are Lipschitz in the scalar shift.
The nonsingularity assumption is pointwise in the shift and almost sure only
in the random sample. -/
theorem expected_matrixCutoff_shift_lipschitz
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix ι ι ℂ) (hA : Measurable A)
    (hdet : ∀ z : ℂ, ∀ᵐ ω ∂μ, (A ω - z • 1).det ≠ 0)
    (hE : Integrable (fun ω => hilbertSchmidtSq (A ω)) μ)
    {a : ℝ} (ha : 0 < a) (z w : ℂ) :
    |(∫ ω, matrixCutoffPotential (A ω - z • 1) a ∂μ) -
      ∫ ω, matrixCutoffPotential (A ω - w • 1) a ∂μ| ≤ ‖z - w‖ / a := by
  have hshift (u : ℂ) : Integrable (fun ω => hilbertSchmidtSq (A ω - u • 1)) μ :=
    integrable_hilbertSchmidtSq_sub μ A (fun _ => u • (1 : Matrix ι ι ℂ))
      hA measurable_const hE (integrable_const _)
  have hcut (u : ℂ) : Integrable (fun ω => matrixCutoffPotential (A ω - u • 1) a) μ :=
    integrable_matrixCutoffPotential μ (fun ω => A ω - u • 1)
      (hA.sub measurable_const) (hdet u) (hshift u) ha
  have hpoint : ∀ᵐ ω ∂μ,
      |matrixCutoffPotential (A ω - z • 1) a -
        matrixCutoffPotential (A ω - w • 1) a| ≤ ‖z - w‖ / a := by
    filter_upwards [hdet z, hdet w] with ω hz hw
    have h := matrixCutoffPotential_difference_le
      (A ω - z • 1) (A ω - w • 1) hz hw ha
    have hd : (A ω - z • 1) - (A ω - w • 1) = (w - z) • 1 := by module
    rw [hd, hilbertSchmidtSq_smul_one,
      Real.sqrt_mul (sq_nonneg ‖w - z‖), Real.sqrt_sq (norm_nonneg (w - z))] at h
    have hroot : Real.sqrt (Fintype.card ι : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 (Nat.cast_pos.mpr Fintype.card_pos)).ne'
    have heq : ‖w - z‖ * Real.sqrt (Fintype.card ι : ℝ) /
        (a * Real.sqrt (Fintype.card ι : ℝ)) = ‖z - w‖ / a := by
      rw [norm_sub_rev]
      field_simp
    rw [heq] at h
    exact h
  rw [← integral_sub (hcut z) (hcut w)]
  have hdiff := ((hcut z).sub (hcut w)).norm
  exact (abs_integral_le_integral_abs.trans
    (integral_mono_ae hdiff (integrable_const (‖z - w‖ / a)) hpoint)).trans_eq (by simp)

end CircularLawSection6
