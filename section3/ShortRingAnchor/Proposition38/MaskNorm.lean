import ShortRingAnchor.Proposition38.Model
import Vendor.SubgaussianNorm.OperatorNorm

/-!
# Proposition 3.8: Cook's norm guard for the literal masked matrix

For a bounded number of blocks the crude `m²` block-compression bound
suffices. The unused IID entries in the `A ∘ X` realization let us apply
the already proved square-IID norm tail once. This is an alternative to
the three-diagonal block union bound and needs no new probability input.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator BigOperators
namespace ShortRingAnchor.Proposition38

variable {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]

def coordinateProjection (label : I → B) (b : B) : Matrix I I ℂ :=
  Matrix.diagonal (fun i => if label i = b then 1 else 0)

def maskedMatrix (label : I → B) (adj : B → B → Prop)
    [DecidableRel adj] (R : Matrix I I ℂ) : Matrix I I ℂ :=
  fun i j => if adj (label i) (label j) then R i j else 0

/-- Proposition 3.8, norm guard: coordinate projections are contractions. -/
theorem norm_coordinateProjection_le (label : I → B) (b : B) :
    ‖coordinateProjection label b‖ ≤ 1 := by
  rw [coordinateProjection, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  split_ifs <;> simp

/-- Proposition 3.8, norm guard: the mask is the sum of its block compressions. -/
theorem block_mask_eq_sum (label : I → B) (adj : B → B → Prop)
    [DecidableRel adj] (R : Matrix I I ℂ) :
    maskedMatrix label adj R =
      ∑ b : B, ∑ c : B, if adj b c then
        coordinateProjection label b * R * coordinateProjection label c else 0 := by
  apply Matrix.ext
  intro i j
  simp only [maskedMatrix, Matrix.sum_apply, Matrix.ite_apply,
    coordinateProjection, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp only [← ite_and]
  rw [Finset.sum_eq_single (label i)]
  · rw [Finset.sum_eq_single (label j)]
    · simp
    · intro c _ hc
      simp [hc.symm]
    · simp
  · intro b _ hb
    simp [hb.symm]
  · simp

/-- Proposition 3.8, norm guard: no sharp norm theorem is needed for
bounded `m`; the deterministic block-mask cost is at most `m²`. -/
theorem norm_block_mask_le (label : I → B) (adj : B → B → Prop)
    [DecidableRel adj] (R : Matrix I I ℂ) :
    ‖maskedMatrix label adj R‖ ≤
      (Fintype.card B : ℝ) ^ 2 * ‖R‖ := by
  rw [block_mask_eq_sum]
  calc
    _ ≤ ∑ b : B, ∑ c : B, ‖if adj b c then
          coordinateProjection label b * R * coordinateProjection label c else 0‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ _b : B, ∑ _c : B, ‖R‖ := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro c _
      split_ifs
      · calc
          _ ≤ ‖coordinateProjection label b‖ * ‖R‖ * ‖coordinateProjection label c‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
              (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ 1 * ‖R‖ * 1 := mul_le_mul
            (mul_le_mul_of_nonneg_right (norm_coordinateProjection_le label b) (norm_nonneg _))
            (norm_coordinateProjection_le label c) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      · simpa using norm_nonneg R
    _ = _ := by simp; ring

end ShortRingAnchor.Proposition38
