/- Source snapshot: upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/EntropyJacobian.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.LivshytsProjectionFormalization.GeometricBrascampLieb

open scoped ENNReal

namespace LivshytsProjectionFormalization

/-- The one-real-dimensional Jacobian contribution is half the projection entropy. -/
theorem real_jacobian_rpow_eq_entropy_half {r : ℝ} (hr : 0 < r) :
    (ENNReal.ofReal r⁻¹).rpow (r ^ 2) =
      ENNReal.ofReal (Real.exp (1 / 2 * projectionEntropy (r ^ 2))) := by
  change ENNReal.ofReal r⁻¹ ^ (r ^ 2 : ℝ) = _
  rw [ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hr)]
  congr 1
  rw [Real.rpow_def_of_pos (inv_pos.mpr hr), Real.log_inv]
  unfold projectionEntropy
  rw [show Real.log (r ^ 2) = 2 * Real.log r by simpa using Real.log_pow r 2]
  congr 1
  ring

/-- The two-real-dimensional Jacobian contribution is the full projection entropy. -/
theorem complex_jacobian_rpow_eq_entropy {r : ℝ} (hr : 0 < r) :
    (ENNReal.ofReal (r⁻¹ ^ 2)).rpow (r ^ 2) =
      ENNReal.ofReal (Real.exp (projectionEntropy (r ^ 2))) := by
  change ENNReal.ofReal (r⁻¹ ^ 2) ^ (r ^ 2 : ℝ) = _
  rw [ENNReal.ofReal_rpow_of_pos (pow_pos (inv_pos.mpr hr) 2)]
  congr 1
  rw [Real.rpow_def_of_pos (pow_pos (inv_pos.mpr hr) 2),
    show Real.log (r⁻¹ ^ 2) = 2 * Real.log r⁻¹ by simpa using Real.log_pow r⁻¹ 2,
    Real.log_inv]
  unfold projectionEntropy
  rw [show Real.log (r ^ 2) = 2 * Real.log r by simpa using Real.log_pow r 2]
  congr 1
  ring

end LivshytsProjectionFormalization

