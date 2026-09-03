/- Source snapshot: upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/KernelCoordinateFrame.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.LivshytsProjectionFormalization.GeometricBrascampLieb
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The Parseval frame on the kernel of a projection

For a subspace `W` of a coordinate Euclidean space, project every standard
basis vector onto `W`.  The nonzero projected vectors, normalized and weighted
by their squared norms, form the geometric Brascamp--Lieb frame used in Han's
fiber proof.  This construction works uniformly over `ℝ` and `ℂ`.
-/

open scoped BigOperators ComplexConjugate

namespace LivshytsProjectionFormalization

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

abbrev CoordinateSpace (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :=
  EuclideanSpace 𝕜 (Fin n)

def kernelCoordinateVector (W : Submodule 𝕜 (CoordinateSpace 𝕜 n)) (i : Fin n) : W :=
  W.orthogonalProjectionOnto (EuclideanSpace.basisFun (Fin n) 𝕜 i)

abbrev ActiveKernelCoordinate (W : Submodule 𝕜 (CoordinateSpace 𝕜 n)) :=
  {i : Fin n // kernelCoordinateVector W i ≠ 0}

noncomputable instance (W : Submodule 𝕜 (CoordinateSpace 𝕜 n)) :
    Fintype (ActiveKernelCoordinate W) :=
  by classical infer_instance

def kernelCoordinateWeight (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (i : ActiveKernelCoordinate W) : ℝ :=
  ‖kernelCoordinateVector W i.1‖ ^ 2

def kernelCoordinateBasis (W : Submodule 𝕜 (CoordinateSpace 𝕜 n)) :
    OrthonormalBasis (Fin (Module.finrank 𝕜 W)) 𝕜 W :=
  stdOrthonormalBasis 𝕜 W

def normalizedKernelCoordinateMap (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (i : ActiveKernelCoordinate W) :
    CoordinateSpace 𝕜 (Module.finrank 𝕜 W) →L[𝕜] 𝕜 :=
  ((‖kernelCoordinateVector W i.1‖⁻¹ : ℝ) : 𝕜) •
    innerSL 𝕜 ((kernelCoordinateBasis W).repr (kernelCoordinateVector W i.1))

theorem kernelCoordinateWeight_nonnegative
    (W : Submodule 𝕜 (CoordinateSpace 𝕜 n)) (i : ActiveKernelCoordinate W) :
    0 ≤ kernelCoordinateWeight W i := by
  exact sq_nonneg _

theorem kernelCoordinateWeight_le_one
    (W : Submodule 𝕜 (CoordinateSpace 𝕜 n)) (i : ActiveKernelCoordinate W) :
    kernelCoordinateWeight W i ≤ 1 := by
  have h := W.norm_orthogonalProjectionOnto_apply_le
    (EuclideanSpace.basisFun (Fin n) 𝕜 (i : Fin n))
  have hb : ‖EuclideanSpace.basisFun (Fin n) 𝕜 (i : Fin n)‖ = 1 := by simp
  rw [hb] at h
  change ‖W.orthogonalProjectionOnto
    (EuclideanSpace.basisFun (Fin n) 𝕜 (i : Fin n))‖ ^ 2 ≤ 1
  nlinarith [norm_nonneg (W.orthogonalProjectionOnto
    (EuclideanSpace.basisFun (Fin n) 𝕜 (i : Fin n)))]

theorem normalizedKernelCoordinateMap_norm
    (W : Submodule 𝕜 (CoordinateSpace 𝕜 n)) (i : ActiveKernelCoordinate W) :
    ‖normalizedKernelCoordinateMap W i‖ = 1 := by
  have hv : ‖kernelCoordinateVector W i.1‖ ≠ 0 := norm_ne_zero_iff.mpr i.property
  rw [normalizedKernelCoordinateMap, norm_smul, innerSL_apply_norm,
    (kernelCoordinateBasis W).repr.norm_map]
  rw [RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ hv

theorem kernelCoordinate_inner_eq_coordinate
    (W : Submodule 𝕜 (CoordinateSpace 𝕜 n)) (i : Fin n) (w : W) :
    inner 𝕜 (kernelCoordinateVector W i) w = (w : CoordinateSpace 𝕜 n) i := by
  rw [kernelCoordinateVector, W.inner_orthogonalProjectionOnto_eq_of_mem_right]
  exact EuclideanSpace.basisFun_inner (𝕜 := 𝕜) (ι := Fin n)
    (w : CoordinateSpace 𝕜 n) i

theorem kernelCoordinateFrame_term
    (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (i : ActiveKernelCoordinate W)
    (x : CoordinateSpace 𝕜 (Module.finrank 𝕜 W)) :
    kernelCoordinateWeight W i * ‖normalizedKernelCoordinateMap W i x‖ ^ 2 =
      ‖inner 𝕜 ((kernelCoordinateBasis W).repr
        (kernelCoordinateVector W i.1)) x‖ ^ 2 := by
  have hv : ‖kernelCoordinateVector W i.1‖ ≠ 0 := norm_ne_zero_iff.mpr i.property
  simp only [kernelCoordinateWeight, normalizedKernelCoordinateMap,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, norm_smul]
  rw [RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  field_simp [hv]

theorem kernelCoordinate_reconstruct
    (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (i : ActiveKernelCoordinate W)
    (x : CoordinateSpace 𝕜 (Module.finrank 𝕜 W)) :
    ((‖kernelCoordinateVector W i.1‖ : ℝ) : 𝕜) *
        normalizedKernelCoordinateMap W i x =
      ((kernelCoordinateBasis W).repr.symm x : CoordinateSpace 𝕜 n) i.1 := by
  have hv : ‖kernelCoordinateVector W i.1‖ ≠ 0 := norm_ne_zero_iff.mpr i.property
  have hvK : ((‖kernelCoordinateVector W i.1‖ : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr hv
  have hinner :
      inner 𝕜 ((kernelCoordinateBasis W).repr (kernelCoordinateVector W i.1)) x =
        inner 𝕜 (kernelCoordinateVector W i.1) ((kernelCoordinateBasis W).repr.symm x) := by
    simpa using (kernelCoordinateBasis W).repr.inner_map_map
      (kernelCoordinateVector W i.1) ((kernelCoordinateBasis W).repr.symm x)
  rw [normalizedKernelCoordinateMap, smul_apply, smul_eq_mul, innerSL_apply_apply, hinner]
  rw [kernelCoordinate_inner_eq_coordinate]
  rw [RCLike.ofReal_inv]
  field_simp [hvK]

theorem kernelCoordinateFrame_identity
    (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (x : CoordinateSpace 𝕜 (Module.finrank 𝕜 W)) :
    ∑ i : ActiveKernelCoordinate W,
        kernelCoordinateWeight W i * ‖normalizedKernelCoordinateMap W i x‖ ^ 2 =
      ‖x‖ ^ 2 := by
  let b := kernelCoordinateBasis W
  let w : W := b.repr.symm x
  calc
    ∑ i : ActiveKernelCoordinate W,
        kernelCoordinateWeight W i * ‖normalizedKernelCoordinateMap W i x‖ ^ 2 =
        ∑ i : ActiveKernelCoordinate W,
          ‖inner 𝕜 (b.repr (kernelCoordinateVector W i.1)) x‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            exact kernelCoordinateFrame_term W i x
    _ = ∑ i : ActiveKernelCoordinate W,
          ‖inner 𝕜 (kernelCoordinateVector W i.1) w‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            have h := b.repr.inner_map_map (kernelCoordinateVector W i.1) (b.repr.symm x)
            rw [b.repr.apply_symm_apply] at h
            exact congrArg (fun z => ‖z‖ ^ 2) h
    _ = ∑ i : Fin n, ‖inner 𝕜 (kernelCoordinateVector W i) w‖ ^ 2 := by
            classical
            have hsplit := Fintype.sum_subtype_add_sum_subtype
              (fun i : Fin n => kernelCoordinateVector W i ≠ 0)
              (fun i : Fin n => ‖inner 𝕜 (kernelCoordinateVector W i) w‖ ^ 2)
            have hzero :
                (∑ i : {i : Fin n // ¬ kernelCoordinateVector W i ≠ 0},
                  ‖inner 𝕜 (kernelCoordinateVector W i.1) w‖ ^ 2) = 0 := by
              apply Finset.sum_eq_zero
              intro i _
              simp only [not_ne_iff.mp i.property, inner_zero_left, norm_zero, zero_pow]
              norm_num
            linarith
    _ = ∑ i : Fin n, ‖(w : CoordinateSpace 𝕜 n) i‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [kernelCoordinate_inner_eq_coordinate]
    _ = ‖(w : CoordinateSpace 𝕜 n)‖ ^ 2 := by
            exact (EuclideanSpace.norm_sq_eq (w : CoordinateSpace 𝕜 n)).symm
    _ = ‖x‖ ^ 2 := by
            calc
              ‖(w : CoordinateSpace 𝕜 n)‖ ^ 2 = ‖w‖ ^ 2 := rfl
              _ = ‖x‖ ^ 2 :=
                congrArg (fun r : ℝ => r ^ 2) (b.repr.symm.norm_map x)

theorem sum_kernelCoordinateWeight_eq_finrank
    (W : Submodule 𝕜 (CoordinateSpace 𝕜 n)) :
    ∑ i : ActiveKernelCoordinate W, kernelCoordinateWeight W i =
      Module.finrank 𝕜 W := by
  let b := kernelCoordinateBasis W
  calc
    ∑ i : ActiveKernelCoordinate W, kernelCoordinateWeight W i =
        ∑ i : ActiveKernelCoordinate W,
          ∑ j : Fin (Module.finrank 𝕜 W),
            ‖inner 𝕜 (b j) (kernelCoordinateVector W i.1)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact (b.sum_sq_norm_inner_right (kernelCoordinateVector W i.1)).symm
    _ = ∑ j : Fin (Module.finrank 𝕜 W),
          ∑ i : ActiveKernelCoordinate W,
            ‖inner 𝕜 (b j) (kernelCoordinateVector W i.1)‖ ^ 2 := by
      rw [Finset.sum_comm]
    _ = ∑ _j : Fin (Module.finrank 𝕜 W), 1 := by
      apply Finset.sum_congr rfl
      intro j _
      have hframe := kernelCoordinateFrame_identity W
        (EuclideanSpace.basisFun (Fin (Module.finrank 𝕜 W)) 𝕜 j)
      rw [show ‖EuclideanSpace.basisFun (Fin (Module.finrank 𝕜 W)) 𝕜 j‖ ^ 2 = 1 by simp]
        at hframe
      calc
        ∑ i : ActiveKernelCoordinate W,
            ‖inner 𝕜 (b j) (kernelCoordinateVector W i.1)‖ ^ 2 =
            ∑ i : ActiveKernelCoordinate W,
              kernelCoordinateWeight W i *
                ‖normalizedKernelCoordinateMap W i
                  (EuclideanSpace.basisFun (Fin (Module.finrank 𝕜 W)) 𝕜 j)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [kernelCoordinateFrame_term]
          rw [norm_inner_symm
            ((kernelCoordinateBasis W).repr (kernelCoordinateVector W i.1))
            (EuclideanSpace.basisFun (Fin (Module.finrank 𝕜 W)) 𝕜 j)]
          rw [EuclideanSpace.basisFun_inner, OrthonormalBasis.repr_apply_apply]
        _ = 1 := hframe
    _ = Module.finrank 𝕜 W := by simp

theorem sum_one_sub_kernelCoordinateWeight_le_codimension
    (W : Submodule 𝕜 (CoordinateSpace 𝕜 n)) :
    ∑ i : ActiveKernelCoordinate W, (1 - kernelCoordinateWeight W i) ≤
      (n - Module.finrank 𝕜 W : ℕ) := by
  have hrank : Module.finrank 𝕜 W ≤ n := by
    simpa using W.finrank_le
  have hcardNat : Fintype.card (ActiveKernelCoordinate W) ≤ n := by
    simpa using Fintype.card_subtype_le
      (fun i : Fin n => kernelCoordinateVector W i ≠ 0)
  have hcard : (Fintype.card (ActiveKernelCoordinate W) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hcardNat
  rw [Finset.sum_sub_distrib, sum_kernelCoordinateWeight_eq_finrank]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub hrank]
  exact sub_le_sub_right hcard _

theorem sum_projectionEntropy_kernelCoordinateWeight_le_codimension
    (W : Submodule 𝕜 (CoordinateSpace 𝕜 n)) :
    ∑ i : ActiveKernelCoordinate W,
        projectionEntropy (kernelCoordinateWeight W i) ≤
      (n - Module.finrank 𝕜 W : ℕ) := by
  calc
    ∑ i : ActiveKernelCoordinate W,
        projectionEntropy (kernelCoordinateWeight W i) ≤
        ∑ i : ActiveKernelCoordinate W, (1 - kernelCoordinateWeight W i) :=
      Finset.sum_le_sum fun i _ =>
        projectionEntropy_le_one_sub (kernelCoordinateWeight_nonnegative W i)
    _ ≤ (n - Module.finrank 𝕜 W : ℕ) :=
      sum_one_sub_kernelCoordinateWeight_le_codimension W

end

end LivshytsProjectionFormalization

