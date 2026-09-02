import BernoulliSection8.CappedReset
import BernoulliSection10.RemainderControl

/-!
# Unclipping a matrix reset using only local Hodge bounds

The cap for a reset must be independent of the length of the past. These
lemmas bound the true increment by twice the core Hodge loss plus the
reset Hodge loss. This justifies removing the cap on the interface-good
event without incorrectly bounding the entire past by a cell-sized cap.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection8

open BernoulliSection10

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem matrix_sandwich_ne_zero
    (A R B : Matrix ι ι ℂ) (hA : IsUnit A.det) (hR : IsUnit R.det) (hB : B ≠ 0) :
    A * R * B ≠ 0 := by
  have hu : IsUnit (A * R) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [Matrix.det_mul]; exact hA.mul hR)
  intro h
  apply hB
  exact hu.mul_left_cancel (by simpa using h)

theorem matrix_splice_defect_le_hodge
    (A R B : Matrix ι ι ℂ) (hA : IsUnit A.det) (hR : IsUnit R.det) (hB : B ≠ 0) :
    Real.log ‖A‖ + Real.log ‖B‖ - Real.log ‖A * R * B‖ ≤
      2 * matrixHodgeLoss A + matrixHodgeLoss R := by
  have hAR : IsUnit (A * R).det := by rw [Matrix.det_mul]; exact hA.mul hR
  have hprod := abs_matrix_logNorm_mul_sub_le_hodgeLoss (A * R) B hAR hB
  have hcore := abs_matrix_logNorm_mul_sub_le_hodgeLoss A 1 hA one_ne_zero
  simp only [Matrix.mul_one, norm_one, Real.log_one, sub_zero] at hcore
  have hsum := matrixHodgeLoss_mul_le A R hA hR
  have hlo := (abs_le.mp hprod).1
  have hhi := (abs_le.mp hcore).2
  linarith

/-- A cap at this local Hodge cost is inactive regardless of the length of
the nonzero past matrix `B`. -/
theorem matrix_log_product_ge_sub_cappedSpliceLoss
    (A R B : Matrix ι ι ℂ) (hA : IsUnit A.det) (hR : IsUnit R.det) (hB : B ≠ 0)
    {T : ℝ} (hcap : 2 * matrixHodgeLoss A + matrixHodgeLoss R ≤ T) :
    Real.log ‖A‖ + Real.log ‖B‖ -
        cappedSpliceLoss T ‖A‖ ‖B‖ ‖A * R * B‖ ≤ Real.log ‖A * R * B‖ := by
  apply log_product_ge_sub_cappedSpliceLoss
    (norm_ne_zero_iff.mpr (matrix_sandwich_ne_zero A R B hA hR hB))
  exact (matrix_splice_defect_le_hodge A R B hA hR hB).trans hcap

end BernoulliSection8
