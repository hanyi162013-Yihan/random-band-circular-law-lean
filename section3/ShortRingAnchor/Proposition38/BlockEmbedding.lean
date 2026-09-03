import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The deterministic block-norm step in Proposition 3.8

Between (3.21) and (3.22), Cook is used only with a bounded number of blocks.
Consequently the crude sum of the block norms suffices. No sharp band-matrix
norm theorem is required. This module proves the coordinate embedding and
restriction bounds; these are not passed in as hypotheses.
-/

open scoped Matrix.Norms.L2Operator BigOperators
noncomputable section
namespace ShortRingAnchor.Proposition38

set_option maxHeartbeats 1000000

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I]

/-- Proposition 3.8, norm event: insert a vector at one block coordinate. -/
def blockInjection (b : B) : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ (B × I) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun p => if p.1 = b then x p.2 else 0)
      map_add' := by intros; ext p; dsimp; split_ifs <;> simp
      map_smul' := by intros; ext p; dsimp; split_ifs <;> simp }

/-- Proposition 3.8, norm event: read the vector at one block coordinate. -/
def blockProjection (b : B) : EuclideanSpace ℂ (B × I) →L[ℂ] EuclideanSpace ℂ I :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => x (b, i))
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }

/-- Proposition 3.8, norm event: insertion preserves the Euclidean norm. -/
theorem norm_blockInjection_apply (b : B) (x : EuclideanSpace ℂ I) :
    ‖blockInjection b x‖ = ‖x‖ := by
  have hs : ‖blockInjection b x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, blockInjection, Fintype.sum_prod_type, apply_ite]
  nlinarith [norm_nonneg (blockInjection b x), norm_nonneg x]

/-- Proposition 3.8, norm event: coordinate restriction is contractive. -/
theorem norm_blockProjection_apply_le (b : B) (x : EuclideanSpace ℂ (B × I)) :
    ‖blockProjection b x‖ ≤ ‖x‖ := by
  have hs : ‖blockProjection b x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    change (∑ i, ‖x (b, i)‖ ^ 2) ≤ ∑ b, ∑ i, ‖x (b, i)‖ ^ 2
    exact Finset.single_le_sum (fun b _ =>
      Finset.sum_nonneg (fun i _ => sq_nonneg ‖x (b, i)‖)) (Finset.mem_univ b)
  nlinarith [norm_nonneg (blockProjection b x), norm_nonneg x]

/-- Proposition 3.8, norm event: block insertion has norm at most one. -/
theorem norm_blockInjection_le (b : B) : ‖blockInjection (I := I) b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [norm_blockInjection_apply]

/-- Proposition 3.8, norm event: block projection has norm at most one. -/
theorem norm_blockProjection_le (b : B) : ‖blockProjection (I := I) b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using norm_blockProjection_apply_le b x

/-- Proposition 3.8, norm event: a single block placed at row `b`, column `c`. -/
def embeddedBlock (b c : B) (A : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    EuclideanSpace ℂ (B × I) →L[ℂ] EuclideanSpace ℂ (B × I) :=
  (blockInjection b).comp (A.comp (blockProjection c))

/-- Proposition 3.8, norm event: inserting a block cannot increase its norm. -/
theorem norm_embeddedBlock_le (b c : B)
    (A : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    ‖embeddedBlock b c A‖ ≤ ‖A‖ := by
  unfold embeddedBlock
  calc
    ‖(blockInjection b).comp (A.comp (blockProjection c))‖ ≤
        ‖blockInjection (I := I) b‖ * ‖A.comp (blockProjection c)‖ :=
      ContinuousLinearMap.opNorm_comp_le (blockInjection (I := I) b)
        (A.comp (blockProjection (I := I) c))
    _ ≤ 1 * ‖A.comp (blockProjection c)‖ :=
      mul_le_mul_of_nonneg_right (norm_blockInjection_le (I := I) b) (norm_nonneg _)
    _ = ‖A.comp (blockProjection c)‖ := one_mul _
    _ ≤ ‖A‖ * ‖blockProjection (I := I) c‖ :=
      ContinuousLinearMap.opNorm_comp_le A (blockProjection (I := I) c)
    _ ≤ ‖A‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_blockProjection_le (I := I) c) (norm_nonneg A)
    _ = ‖A‖ := mul_one _

/-- Proposition 3.8, norm event: the sum bound is sufficient when Cook is
used for only finitely many block counts. Independence is not needed here. -/
theorem norm_sum_embeddedBlock_le {J : Type*} [Fintype J]
    (row col : J → B) (A : J → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    ‖∑ j, embeddedBlock (row j) (col j) (A j)‖ ≤ ∑ j, ‖A j‖ := by
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum (fun j _ => norm_embeddedBlock_le (row j) (col j) (A j)))

end ShortRingAnchor.Proposition38
