/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/ModelMoments.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.BVH.GaussianMoments
import Vendor.Arxiv2410.V3.VarianceProfile

/-!
# Entry third moments for the v3 model

This file transports the atom third moment through the entry laws of
`RandomMatrixModelV3` and connects the resulting finite sum to the already proved
variance-profile ledger below v3 formula (3.12).  It contains no comparison hypothesis.
-/

namespace Arxiv2410V3.BVH

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

variable {Omega OmegaXi : Type*}
  [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
  {mu : Measure Omega} {nu : Measure OmegaXi}
  [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
  {n : ℕ}

/-- The finite third absolute moment of the standardized atom in v3 Proposition 3.4. -/
def atomThirdMoment
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) : ℝ :=
  ∫ omegaXi, ‖model.atom omegaXi‖ ^ 3 ∂nu

theorem atomThirdMoment_nonneg
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    0 ≤ atomThirdMoment model := by
  exact integral_nonneg fun _ ↦ pow_nonneg (norm_nonneg _) 3

/-- Every actual entry is integrable, by transport of the integrable standardized atom. -/
theorem entry_integrable
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    Integrable (fun omega ↦ model.matrix omega i j) mu := by
  apply (model.entry_law i j).integrable_iff.mpr
  simpa using model.atom_integrable.const_mul
    (model.profile.coefficient i j : ℂ)

/-- The common zero mean of the standardized atom transports to every actual entry. -/
theorem integral_entry_eq_zero
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    (∫ omega, model.matrix omega i j ∂mu) = 0 := by
  have h := (model.entry_law i j).integral_eq
  rw [integral_const_mul, model.atom_mean_zero, mul_zero] at h
  exact h

theorem integral_entry_re_eq_zero
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    (∫ omega, (model.matrix omega i j).re ∂mu) = 0 := by
  have h : (∫ omega, (model.matrix omega i j).re ∂mu) =
      (∫ omega, model.matrix omega i j ∂mu).re :=
    integral_re (entry_integrable model i j)
  rw [integral_entry_eq_zero] at h
  simpa using h

theorem integral_entry_im_eq_zero
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    (∫ omega, (model.matrix omega i j).im ∂mu) = 0 := by
  have h : (∫ omega, (model.matrix omega i j).im ∂mu) =
      (∫ omega, model.matrix omega i j ∂mu).im :=
    integral_im (entry_integrable model i j)
  rw [integral_entry_eq_zero] at h
  simpa using h

/-- The entrywise third absolute moment is integrable; this is the actual unbounded input used
by the specialized Lindeberg argument. -/
theorem integrable_entry_norm_cube
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    Integrable (fun omega ↦ ‖model.matrix omega i j‖ ^ 3) mu := by
  have hlaw : IdentDistrib
      (fun omega ↦ ‖model.matrix omega i j‖ ^ 3)
      (fun omegaXi ↦ ‖(model.profile.coefficient i j : ℂ) * model.atom omegaXi‖ ^ 3)
      mu nu := by
    simpa only [Function.comp_def] using
      (model.entry_law i j).comp
        (show Measurable (fun w : ℂ ↦ ‖w‖ ^ 3) by fun_prop)
  apply hlaw.integrable_iff.mpr
  simpa [norm_mul, Complex.norm_real,
    abs_of_nonneg (model.profile.coefficient_nonneg i j), mul_pow] using
      model.atom_third_moment_finite.const_mul
        (model.profile.coefficient i j ^ 3)

/-- The entrywise second absolute moment is integrable as a consequence of the third one. -/
theorem integrable_entry_norm_square
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    Integrable (fun omega ↦ ‖model.matrix omega i j‖ ^ 2) mu := by
  exact integrable_norm_pow_of_le
    (model.entry_measurable i j).aestronglyMeasurable (by norm_num)
    (integrable_entry_norm_cube model i j)

/-- Transport of the variance-one normalization to one actual entry. -/
theorem integral_entry_norm_square_eq
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    (∫ omega, ‖model.matrix omega i j‖ ^ 2 ∂mu) =
      model.profile.coefficient i j ^ 2 := by
  have hlaw : IdentDistrib
      (fun omega ↦ ‖model.matrix omega i j‖ ^ 2)
      (fun omegaXi ↦ ‖(model.profile.coefficient i j : ℂ) * model.atom omegaXi‖ ^ 2)
      mu nu := by
    simpa only [Function.comp_def] using
      (model.entry_law i j).comp
        (show Measurable (fun w : ℂ ↦ ‖w‖ ^ 2) by fun_prop)
  rw [hlaw.integral_eq]
  have hcoeff : ‖(model.profile.coefficient i j : ℂ)‖ =
      model.profile.coefficient i j := by
    simpa [Complex.norm_real,
      abs_of_nonneg (model.profile.coefficient_nonneg i j)]
  simp_rw [norm_mul, hcoeff, mul_pow]
  rw [integral_const_mul, model.atom_variance_one, mul_one]

/-- Each real coordinate second moment is bounded by the full complex second moment. -/
theorem integral_entry_re_sq_le_coefficient_sq
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    (∫ omega, (model.matrix omega i j).re ^ 2 ∂mu) ≤
      model.profile.coefficient i j ^ 2 := by
  rw [← integral_entry_norm_square_eq model i j]
  apply integral_mono_of_nonneg
    (ae_of_all _ fun _ ↦ sq_nonneg _)
    (integrable_entry_norm_square model i j)
  filter_upwards [] with omega
  simpa [sq_abs] using
    (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2)

theorem integral_entry_im_sq_le_coefficient_sq
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    (∫ omega, (model.matrix omega i j).im ^ 2 ∂mu) ≤
      model.profile.coefficient i j ^ 2 := by
  rw [← integral_entry_norm_square_eq model i j]
  apply integral_mono_of_nonneg
    (ae_of_all _ fun _ ↦ sq_nonneg _)
    (integrable_entry_norm_square model i j)
  filter_upwards [] with omega
  simpa [sq_abs] using
    (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2)

/-- Transport of the common scaled atom law to the third absolute moment of one entry. -/
theorem integral_entry_norm_cube_eq
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    (∫ omega, ‖model.matrix omega i j‖ ^ 3 ∂mu) =
      model.profile.coefficient i j ^ 3 * atomThirdMoment model := by
  have hlaw : IdentDistrib
      (fun omega ↦ ‖model.matrix omega i j‖ ^ 3)
      (fun omegaXi ↦ ‖(model.profile.coefficient i j : ℂ) * model.atom omegaXi‖ ^ 3)
      mu nu := by
    simpa only [Function.comp_def] using
      (model.entry_law i j).comp
        (show Measurable (fun w : ℂ ↦ ‖w‖ ^ 3) by fun_prop)
  rw [hlaw.integral_eq]
  have hcoeff : ‖(model.profile.coefficient i j : ℂ)‖ =
      model.profile.coefficient i j := by
    simpa [Complex.norm_real,
      abs_of_nonneg (model.profile.coefficient_nonneg i j)]
  simp_rw [norm_mul, hcoeff]
  simp_rw [mul_pow]
  rw [integral_const_mul]
  rfl

/-- The normalized sum of actual-entry third moments has the `B⁻¹ᐟ² = 1 / √B` scale used in
v3 formula (3.12). -/
theorem normalized_sum_integral_entry_norm_cube_le
    [NeZero n]
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    {B : ℝ} (hB : IsBandwidth model.profile B) :
    (∑ i : Fin n, ∑ j : Fin n,
        ∫ omega, ‖model.matrix omega i j‖ ^ 3 ∂mu) / (n : ℝ) ≤
      atomThirdMoment model / Real.sqrt B := by
  simp_rw [integral_entry_norm_cube_eq model]
  rw [show (∑ i : Fin n, ∑ j : Fin n,
      model.profile.coefficient i j ^ 3 * atomThirdMoment model) =
      atomThirdMoment model *
        (∑ i : Fin n, ∑ j : Fin n, model.profile.coefficient i j ^ 3) by
    simp_rw [mul_comm _ (atomThirdMoment model), Finset.mul_sum]]
  calc
    (atomThirdMoment model *
          (∑ i : Fin n, ∑ j : Fin n, model.profile.coefficient i j ^ 3)) /
        (n : ℝ) = atomThirdMoment model *
          ((∑ i : Fin n, ∑ j : Fin n, model.profile.coefficient i j ^ 3) /
            (n : ℝ)) := by ring
    _ ≤ atomThirdMoment model / Real.sqrt B := by
      simpa [Fintype.card_fin] using
        third_moment_mul_normalized_sum_cube_le model.profile hB
          (atomThirdMoment_nonneg model)

end

end Arxiv2410V3.BVH

