import ShortRingAnchor.BC12.KnownFormulas
import ShortRingAnchor.BC12.WeightedDensityConvergence
import ShortRingAnchor.BC12.ScalarConcentration

/-!
# From the finite Ginibre formulas to convergence of linear statistics

The only random-matrix inputs are the explicitly named finite-dimensional
formulas in `KnownFormulas`.  We prove the variance estimate and the limit,
including Gaussian-integrable unbounded test functions.  Specializing this
theorem to `log |w-z|` requires its ordinary analytic integrability and the
disk-potential computation, not a circular-law input.
-/

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace ShortRingAnchor.BC12

/-- Measurability of the explicit squared finite kernel. -/
theorem measurable_ginibreKernelWeight (n : ℕ) : Measurable (ginibreKernelWeight n) := by
  unfold ginibreKernelWeight ginibreKernel
  fun_prop

/-- The two-point formula and the exact projection identity imply a
variance bound, also for unbounded test functions.  This is a proved
inequality; it is deliberately not a field of the external interface. -/
theorem ginibre_variance_le_of_formulas
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {n : ℕ} (hn : 0 < n)
    {eigenvalue : Omega → Fin n → ℂ}
    (hprojection : GinibreProjectionIntegralFormula n)
    (hcorrelation : GinibreCorrelationFormulas mu eigenvalue)
    {f : ℂ → ℝ} (hf : Measurable f)
    (hint : Integrable (fun w => (f w) ^ 2 * ginibreOnePointDensity n w)) :
    (∫ sample,
      (eigenvalueStatistic eigenvalue f sample -
        ∫ other, eigenvalueStatistic eigenvalue f other ∂mu) ^ 2 ∂mu) ≤
      2 * (∫ w, (f w) ^ 2 * ginibreOnePointDensity n w) / (n : ℝ) := by
  obtain ⟨hweightInt, hweightEq⟩ := hprojection.weightedProjection
    (fun w => (f w) ^ 2) (hf.pow_const 2) (fun w => sq_nonneg _) hint
  have hpoint (wv : ℂ × ℂ) :
      (f wv.1 - f wv.2) ^ 2 * ginibreKernelWeight n wv ≤
        2 * (((f wv.1) ^ 2 + (f wv.2) ^ 2) * ginibreKernelWeight n wv) := by
    have hk : 0 ≤ ginibreKernelWeight n wv := sq_nonneg _
    calc
      _ ≤ (2 * ((f wv.1) ^ 2 + (f wv.2) ^ 2)) * ginibreKernelWeight n wv :=
        mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (f wv.1 + f wv.2)]) hk
      _ = _ := by ring
  have henergyInt : Integrable (fun wv : ℂ × ℂ =>
      (f wv.1 - f wv.2) ^ 2 * ginibreKernelWeight n wv) := by
    apply (hweightInt.const_mul 2).mono'
      ((((hf.comp measurable_fst).sub (hf.comp measurable_snd)).pow_const 2).mul
        (measurable_ginibreKernelWeight n)).aestronglyMeasurable
    exact .of_forall fun wv => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact hpoint wv
  have henergy : (∫ wv : ℂ × ℂ,
      (f wv.1 - f wv.2) ^ 2 * ginibreKernelWeight n wv) ≤
        4 * (n : ℝ) * ∫ w, (f w) ^ 2 * ginibreOnePointDensity n w := by
    calc
      _ ≤ ∫ wv : ℂ × ℂ,
          2 * (((f wv.1) ^ 2 + (f wv.2) ^ 2) * ginibreKernelWeight n wv) :=
        integral_mono henergyInt (hweightInt.const_mul 2) hpoint
      _ = _ := by rw [integral_const_mul, hweightEq]; ring
  rw [(hcorrelation.secondMoment f hf hint).2]
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine (div_le_div_of_nonneg_right henergy (by positivity)).trans_eq ?_
  field_simp
  ring

/-- Conditional Ginibre linear-statistic convergence from finite formulas.

Neither a weak circular law, mean convergence, a variance bound, nor
logarithmic-tail control is assumed here.  All dimension-dependent
estimates are proved from the displayed correlation formulas and explicit
one-point density.  The two Gaussian integrability premises are analytic
conditions on the chosen test function, not probabilistic interfaces. -/
theorem ginibre_statistic_convergesInProbability_of_formulas
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {M : ℕ → ℕ} (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop)
    (eigenvalue : ∀ n, Omega → Fin (M n) → ℂ)
    (hprojection : ∀ n, GinibreProjectionIntegralFormula (M n))
    (hcorrelation : ∀ n, GinibreCorrelationFormulas mu (eigenvalue n))
    {f : ℂ → ℝ} (hf : Measurable f)
    (hL1 : Integrable (fun w => |f w| * ginibreEnvelope w))
    (hL2 : Integrable (fun w => (f w) ^ 2 * ginibreEnvelope w)) :
    ConvergesInProbability mu (fun n => eigenvalueStatistic (eigenvalue n) f)
      (∫ w, f w * circularDensity w) := by
  have hsquare n : Integrable (fun w => (f w) ^ 2 * ginibreOnePointDensity (M n) w) :=
    integrable_mul_ginibreOnePointDensity (hf.pow_const 2)
      (by simpa only [abs_pow, sq_abs] using hL2) (M n)
  apply convergesInProbability_of_mean_and_square_bound
    (m := fun n => ∫ sample, eigenvalueStatistic (eigenvalue n) f sample ∂mu)
    (rate := fun n => 2 * (∫ w, (f w) ^ 2 * ginibreEnvelope w) / (M n : ℝ))
  · intro n
    exact (hcorrelation n |>.secondMoment f hf (hsquare n)).1
  · intro n
    refine (ginibre_variance_le_of_formulas (hMpos n) (hprojection n)
      (hcorrelation n) hf (hsquare n)).trans ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (integral_sq_mul_ginibreOnePointDensity_le hf hL2 (M n)) (by norm_num))
      (Nat.cast_nonneg _)
  · exact const_div_dimension_tendsto_zero hM _
  · have hlimit := (integral_mul_ginibreOnePointDensity_tendsto hf hL1).comp hM
    convert hlimit using 1
    funext n
    exact (hcorrelation n |>.firstMoment f hf
      (integrable_mul_ginibreOnePointDensity hf hL1 (M n))).2

end ShortRingAnchor.BC12
