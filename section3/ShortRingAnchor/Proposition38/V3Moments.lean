import ShortRingAnchor.Proposition38.Model

/-! # Proposition 3.8: the upper-edge moment calculation

Equation (3.25). Doubly stochastic entry variances imply the exact row
second moment one. This is proved from the v3 model's entry laws and is
not a separately supplied moment bound.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Arxiv2410V3
open scoped BigOperators
namespace ShortRingAnchor.Proposition38

/-- Proposition 3.8, (3.25): any v3 model has exact centered row second
moments. This applies to both the full-block ring and dense Ginibre. -/
theorem centeredRowMoments_of_v3
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {N : ℕ → ℕ} (model : ∀ k, RandomMatrixModelV3 (N k) Ω Ξ μ ν) :
    CenteredMatrixRowSecondMomentInputs μ (fun k => (model k).matrix) 1 := by
  have hsecond (k) : Integrable (fun x => ‖(model k).atom x‖ ^ 2) ν :=
    integrable_norm_pow_of_le (model k).atom_integrable.aestronglyMeasurable
      (by omega) (model k).atom_third_moment_finite
  have hint (k) (i j : Fin (N k)) : Integrable
      (fun x => ‖((model k).profile.coefficient i j : ℂ) * (model k).atom x‖ ^ 2) ν := by
    simpa only [norm_mul, mul_pow] using
      (hsecond k).const_mul (‖((model k).profile.coefficient i j : ℂ)‖ ^ 2)
  refine ⟨zero_le_one, ?_, ?_, ?_, ?_⟩
  · intro k i j
    exact ((model k).entry_law i j).integrable_iff.mpr
      ((model k).atom_integrable.const_mul _)
  · intro k i j
    exact ((model k).entry_law i j).norm.pow.integrable_iff.mpr (hint k i j)
  · intro k i j
    rw [((model k).entry_law i j).integral_eq, integral_const_mul,
      (model k).atom_mean_zero, mul_zero]
  · intro k i
    have heq (j : Fin (N k)) :
        (∫ sample, ‖(model k).matrix sample i j‖ ^ 2 ∂μ) =
          (model k).profile.coefficient i j ^ 2 := by
      rw [((model k).entry_law i j).norm.pow.integral_eq]
      simp only [norm_mul, mul_pow, integral_const_mul,
        (model k).atom_variance_one, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp_rw [heq]
    exact (model k).profile.row_sq_sum i

end ShortRingAnchor.Proposition38
