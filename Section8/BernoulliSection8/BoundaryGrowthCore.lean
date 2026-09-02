import BernoulliSection8.WidthLog
import BernoulliLinearAlgebra.ConcreteConditioning

/-! # Deterministic logarithmic bookkeeping for the normalized packet

These elementary estimates keep the raw shift separate from the width
factor. All finite exterior sums and Hodge inverse estimates use the
already proved concrete matrix identities.
-/

open scoped BigOperators Matrix Matrix.Norms.Frobenius

noncomputable section

namespace BernoulliSection8

open BernoulliLinearAlgebra Matrix Set Set.powersetCard

local instance boundaryGrowthSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W => (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h => toLex.injective h)

/-- A finite sum of actual forward and inverse compounds. The inverse
bound follows internally from the Hodge--Jacobi identity. -/
theorem log_exactExteriorConditioningConstant_le_of_forward_bound
    (W : ℕ) (E : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hE : IsUnit E.det) (F D : ℝ) (hF : 1 ≤ F) (hD : 0 ≤ D)
    (hdet : ‖E.det‖⁻¹ ≤ Real.exp D)
    (hforward : ∀ q : ℕ, ‖compound q E‖ ≤ F) :
    Real.log (exactExteriorConditioningConstant E) ≤
      Real.log (4 * W + 3 : ℝ) + Real.log F + D := by
  have hFpos : 0 < F := zero_lt_one.trans_le hF
  have hDexp : 1 ≤ Real.exp D := Real.one_le_exp_iff.mpr hD
  have hcard : Fintype.card (Fin W ⊕ Fin W) = 2 * W := by simp; omega
  have hterm (q : ℕ) (hq : q ∈ Finset.range (2 * W + 1)) :
      ‖compound q E‖ + ‖compound q E⁻¹‖ ≤ 2 * (F * Real.exp D) := by
    have hq' : q ≤ Fintype.card (Fin W ⊕ Fin W) := by
      rw [hcard]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hq)
    have hinv : ‖compound q E⁻¹‖ ≤ Real.exp D * F := by
      rw [compound_inverse_norm_eq_of_isUnit E hE q hq']
      exact mul_le_mul hdet (hforward _) (norm_nonneg _) (Real.exp_pos _).le
    have hf : ‖compound q E‖ ≤ F * Real.exp D :=
      (hforward q).trans (by nlinarith [mul_le_mul_of_nonneg_left hDexp hFpos.le])
    nlinarith
  have hprod : 1 ≤ F * Real.exp D := one_le_mul_of_one_le_of_one_le hF hDexp
  have hcoarse : exactExteriorConditioningConstant E ≤
      (4 * W + 3 : ℝ) * F * Real.exp D := by
    unfold exactExteriorConditioningConstant
    rw [hcard]
    calc
      1 + ∑ q ∈ Finset.range (2 * W + 1), (‖compound q E‖ + ‖compound q E⁻¹‖) ≤
          1 + ∑ _q ∈ Finset.range (2 * W + 1), 2 * (F * Real.exp D) :=
        add_le_add le_rfl (Finset.sum_le_sum hterm)
      _ = 1 + (2 * W + 1 : ℝ) * (2 * (F * Real.exp D)) := by simp
      _ ≤ (4 * W + 3 : ℝ) * F * Real.exp D := by nlinarith
  have hpos : 0 < exactExteriorConditioningConstant E :=
    zero_lt_one.trans_le (one_le_exactExteriorConditioningConstant E)
  calc
    Real.log (exactExteriorConditioningConstant E) ≤
        Real.log ((4 * W + 3 : ℝ) * F * Real.exp D) := Real.log_le_log hpos hcoarse
    _ = Real.log (4 * W + 3 : ℝ) + Real.log F + D := by
      rw [Real.log_mul (mul_pos (by positivity) hFpos).ne' (Real.exp_ne_zero _),
        Real.log_mul (by positivity) hFpos.ne', Real.log_exp]

end BernoulliSection8
