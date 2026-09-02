import BernoulliSection9.EndpointOperatorBounds
import Mathlib.Tactic

/-!
# Paper endpoint-interface data

This file packages exactly the scalar endpoint information supplied by the
paper's interface good event: a common operator-norm bound and a positive
lower bound for the two determinant norms.  Invertibility and the determinant
bound for the block-diagonal endpoint factor are consequences, not additional
certificates.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

open BernoulliLinearAlgebra

/-- The deterministic data carried by the paper's endpoint good event.

There are no compound-matrix, Hodge, inverse, or elimination certificates in
this structure. -/
structure PaperEndpointGood {W : Nat}
    (CL BR : Matrix (Fin W) (Fin W) Complex)
    (B delta : Real) : Prop where
  norm_CL_le : ‖CL‖ <= B
  norm_BR_le : ‖BR‖ <= B
  delta_pos : 0 < delta
  delta_le_norm_det_CL : delta <= ‖CL.det‖
  delta_le_norm_det_BR : delta <= ‖BR.det‖

namespace PaperEndpointGood

variable {W : Nat} {CL BR : Matrix (Fin W) (Fin W) Complex}
  {B delta : Real}

/-- The lower determinant bound implies invertibility of the left endpoint. -/
theorem CL_det_isUnit (h : PaperEndpointGood CL BR B delta) :
    IsUnit CL.det := by
  apply isUnit_iff_ne_zero.mpr
  exact norm_pos_iff.mp (h.delta_pos.trans_le h.delta_le_norm_det_CL)

/-- The lower determinant bound implies invertibility of the right endpoint. -/
theorem BR_det_isUnit (h : PaperEndpointGood CL BR B delta) :
    IsUnit BR.det := by
  apply isUnit_iff_ne_zero.mpr
  exact norm_pos_iff.mp (h.delta_pos.trans_le h.delta_le_norm_det_BR)

/-- Forgetting the determinant part gives precisely the operator-norm good
event used by the quantitative exterior estimates. -/
theorem endpointOperatorGood (h : PaperEndpointGood CL BR B delta) :
    EndpointOperatorGood CL BR B :=
  ⟨h.norm_CL_le, h.norm_BR_le⟩

/-- The paper determinant-loss scalar is nonnegative. -/
theorem deltaInvSq_nonneg (_h : PaperEndpointGood CL BR B delta) :
    0 <= delta⁻¹ ^ 2 := by
  positivity

/-- The two endpoint determinant lower bounds imply the required inverse
determinant bound for `diag(C_L,B_R)`. -/
theorem endpointFactor_det_inv_norm_le
    (h : PaperEndpointGood CL BR B delta) :
    ‖(endpointFactor CL BR).det‖⁻¹ <= delta⁻¹ ^ 2 := by
  have hdelta_sq : 0 < delta ^ 2 := pow_pos h.delta_pos 2
  have hproduct : delta ^ 2 <= ‖CL.det‖ * ‖BR.det‖ := by
    rw [pow_two]
    exact mul_le_mul h.delta_le_norm_det_CL h.delta_le_norm_det_BR
      h.delta_pos.le (norm_nonneg _)
  rw [endpointFactor_det, norm_mul]
  simpa [inv_pow] using inv_anti₀ hdelta_sq hproduct

end PaperEndpointGood

end BernoulliSection9
