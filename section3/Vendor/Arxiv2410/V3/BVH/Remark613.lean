/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/Remark613.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.BVH.GaussianModelMoments
import Vendor.Arxiv2410.V3.BVH.TraceUniversality

/-!
# The specialized content of BVH Remark 6.13 used in v3 Proposition 3.4

Brailovskaya--van Handel, Remark 6.13 gives a normalized resolvent-trace comparison with a
fourth power of the inverse imaginary part and a sum of third moments.  This file proves the
precise specialization needed by arXiv:2410.16457v3, formula (3.12), from the application-specific
entrywise Lindeberg development in the preceding files.

No boundedness of the entries is assumed.  The actual entries only use the finite third moment
in `RandomMatrixModelV3`; the companion third moments are proved from joint Gaussianity and
matching first and second moments.
-/

namespace Arxiv2410V3.BVH

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

private theorem sum_integral_entryCoordinateLaw_norm_cube_eq
    {Omega : Type*} [MeasurableSpace Omega] {rho : Measure Omega} {n : ℕ}
    {X : Omega → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j)) :
    (∑ k : Fin (n * n),
        ∫ w, ‖w‖ ^ 3 ∂entryCoordinateLaw rho X k) =
      ∑ i : Fin n, ∑ j : Fin n, ∫ omega, ‖X omega i j‖ ^ 3 ∂rho := by
  calc
    (∑ k : Fin (n * n),
        ∫ w, ‖w‖ ^ 3 ∂entryCoordinateLaw rho X k) =
        ∑ k : Fin (n * n),
          ∫ omega, ‖matrixCoordinates (X omega) k‖ ^ 3 ∂rho := by
      apply Fintype.sum_congr
      intro k
      rw [entryCoordinateLaw]
      exact integral_map_of_stronglyMeasurable
        ((measurable_pi_apply k).comp (measurable_matrixCoordinates hX)) (by fun_prop)
    _ = ∑ ij : Fin n × Fin n,
          ∫ omega, ‖X omega ij.1 ij.2‖ ^ 3 ∂rho := by
      simpa only [matrixCoordinates] using
        (finProdFinEquiv.symm.sum_comp
          (fun ij : Fin n × Fin n ↦ ∫ omega, ‖X omega ij.1 ij.2‖ ^ 3 ∂rho))
    _ = ∑ i : Fin n, ∑ j : Fin n,
          ∫ omega, ‖X omega i j‖ ^ 3 ∂rho := by
      rw [Fintype.sum_prod_type]

/-- Machine-checked application-specific version of BVH Remark 6.13, yielding exactly the
`B⁻¹ᐟ² (Im eta)⁻⁴ = (1 / √B) (Im eta)⁻⁴` scale in v3 formula (3.12).

The constant is explicit and independent of the fixed finite shift `z`. -/
theorem bvh_remark613_specialized_v3
    {Omega OmegaXi OmegaG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi] [MeasurableSpace OmegaG]
    {mu : Measure Omega} {nu : Measure OmegaXi} {muG : Measure OmegaG}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure muG]
    {n : ℕ} [NeZero n]
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (gaussian : GaussianCompanionModelV3 n Omega OmegaXi OmegaG mu nu muG model)
    {B : ℝ} (hB : IsBandwidth model.profile B)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) :
    ‖(∫ omega, stieltjesTrace (model.matrix omega) z eta ∂mu) -
        ∫ omega, stieltjesTrace (gaussian.matrix omega) z eta ∂muG‖ ≤
      (atomThirdMoment model + complexGaussianThirdMomentConstant) /
        (Real.sqrt B * eta.im ^ 4) := by
  have hraw :=
    norm_expected_stieltjesTrace_sub_gaussian_le_coordinate_cubicBudget
      model gaussian (integrable_gaussian_entry_norm_cube model gaussian) z heta
  let SA : ℝ :=
    ∑ i : Fin n, ∑ j : Fin n,
      ∫ omega, ‖model.matrix omega i j‖ ^ 3 ∂mu
  let SG : ℝ :=
    ∑ i : Fin n, ∑ j : Fin n,
      ∫ omega, ‖gaussian.matrix omega i j‖ ^ 3 ∂muG
  have hsumActual :
      (∑ k : Fin (n * n),
          ∫ w, ‖w‖ ^ 3 ∂entryCoordinateLaw mu model.matrix k) = SA := by
    simpa only [SA] using
      sum_integral_entryCoordinateLaw_norm_cube_eq model.entry_measurable
  have hsumGaussian :
      (∑ k : Fin (n * n),
          ∫ w, ‖w‖ ^ 3 ∂entryCoordinateLaw muG gaussian.matrix k) = SG := by
    simpa only [SG] using
      sum_integral_entryCoordinateLaw_norm_cube_eq gaussian.entry_measurable
  have hrawSum :
      (∑ k : Fin (n * n),
        (1 / ((n : ℝ) * eta.im ^ 4)) *
          ((∫ w, ‖w‖ ^ 3 ∂entryCoordinateLaw mu model.matrix k) +
            ∫ w, ‖w‖ ^ 3 ∂entryCoordinateLaw muG gaussian.matrix k)) =
        (SA + SG) / ((n : ℝ) * eta.im ^ 4) := by
    calc
      _ = (1 / ((n : ℝ) * eta.im ^ 4)) *
          ((∑ k : Fin (n * n),
              ∫ w, ‖w‖ ^ 3 ∂entryCoordinateLaw mu model.matrix k) +
            ∑ k : Fin (n * n),
              ∫ w, ‖w‖ ^ 3 ∂entryCoordinateLaw muG gaussian.matrix k) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (SA + SG) / ((n : ℝ) * eta.im ^ 4) := by
        rw [hsumActual, hsumGaussian]
        ring
  have hnormalized : (SA + SG) / (n : ℝ) ≤
      (atomThirdMoment model + complexGaussianThirdMomentConstant) /
        Real.sqrt B := by
    calc
      (SA + SG) / (n : ℝ) = SA / (n : ℝ) + SG / (n : ℝ) := by ring
      _ ≤ atomThirdMoment model / Real.sqrt B +
          complexGaussianThirdMomentConstant / Real.sqrt B :=
        add_le_add
          (by simpa only [SA] using
            normalized_sum_integral_entry_norm_cube_le model hB)
          (by simpa only [SG] using
            normalized_sum_integral_gaussian_entry_norm_cube_le model gaussian hB)
      _ = (atomThirdMoment model + complexGaussianThirdMomentConstant) /
          Real.sqrt B := by ring
  calc
    ‖(∫ omega, stieltjesTrace (model.matrix omega) z eta ∂mu) -
        ∫ omega, stieltjesTrace (gaussian.matrix omega) z eta ∂muG‖ ≤
        (SA + SG) / ((n : ℝ) * eta.im ^ 4) := by
      rw [← hrawSum]
      exact hraw
    _ = ((SA + SG) / (n : ℝ)) / eta.im ^ 4 := by ring
    _ ≤ ((atomThirdMoment model + complexGaussianThirdMomentConstant) /
          Real.sqrt B) / eta.im ^ 4 := by
      exact div_le_div_of_nonneg_right hnormalized (pow_nonneg (le_of_lt heta) 4)
    _ = (atomThirdMoment model + complexGaussianThirdMomentConstant) /
          (Real.sqrt B * eta.im ^ 4) := by ring

end

end Arxiv2410V3.BVH

