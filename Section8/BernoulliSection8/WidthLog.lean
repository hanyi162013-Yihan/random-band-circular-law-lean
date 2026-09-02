import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Width logarithms for the physically normalized packet -/

noncomputable section

namespace BernoulliSection8

theorem log_nat_polynomial_le_log_e_scale
    (W : ℕ) (hW : 0 < W) (A : ℝ) (hA : 1 ≤ A) (k : ℕ) :
    Real.log (A * (W : ℝ) ^ k) ≤
      (Real.log A + k) * Real.log (Real.exp 1 * W) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (Nat.succ_le_of_lt hW)
  have hWpos : (0 : ℝ) < W := by positivity
  have hApos : 0 < A := zero_lt_one.trans_le hA
  rw [Real.log_mul hApos.ne' (pow_ne_zero _ hWpos.ne'), Real.log_pow,
    Real.log_mul (Real.exp_ne_zero _) hWpos.ne', Real.log_exp]
  have ha := Real.log_nonneg hA
  have hw := Real.log_nonneg hW1
  have hk : (0 : ℝ) ≤ k := by positivity
  nlinarith [mul_nonneg ha hw]

theorem log_rowScale_le_log_e_scale
    (W : ℕ) (hW : 0 < W) (S : ℝ) (hS : 0 < S) (hupper : S ≤ 3 * W) :
    Real.log S ≤ (Real.log 3 + 1) * Real.log (Real.exp 1 * W) := by
  exact (Real.log_le_log hS hupper).trans
    (by simpa only [pow_one, Nat.cast_one] using
      log_nat_polynomial_le_log_e_scale W hW 3 (by norm_num) 1)

theorem log_scaled_shift_le_log_e_scale
    (W : ℕ) (hW : 0 < W) (S : ℝ) (hS : 0 ≤ S) (hupper : S ≤ 3 * W)
    (z : ℂ) :
    Real.log (1 + S * ‖z‖) ≤
      (Real.log (1 + 3 * ‖z‖) + 1) * Real.log (Real.exp 1 * W) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (Nat.succ_le_of_lt hW)
  have hz := norm_nonneg z
  have hle : 1 + S * ‖z‖ ≤ (1 + 3 * ‖z‖) * W := by
    nlinarith [mul_le_mul_of_nonneg_right hupper hz]
  have hA : 1 ≤ 1 + 3 * ‖z‖ := le_add_of_nonneg_right (by positivity)
  exact (Real.log_le_log (by positivity) hle).trans
    (by simpa only [pow_one, Nat.cast_one] using
      log_nat_polynomial_le_log_e_scale W hW (1 + 3 * ‖z‖) hA 1)

theorem log_endpoint_count_le_log_e_scale
    (W : ℕ) (hW : 0 < W) :
    Real.log (4 * W + 3 : ℝ) ≤
      (Real.log 7 + 1) * Real.log (Real.exp 1 * W) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (Nat.succ_le_of_lt hW)
  exact (Real.log_le_log (by positivity) (by linarith : (4 * W + 3 : ℝ) ≤ 7 * W)).trans
    (by simpa only [pow_one, Nat.cast_one] using
      log_nat_polynomial_le_log_e_scale W hW 7 (by norm_num) 1)

/-- A polynomial operator bound gives one W log(eW) loss after taking
all exterior degrees. -/
theorem log_endpoint_forward_crude_le
    (W : ℕ) (hW : 0 < W) (B : ℝ) (hB : 1 ≤ B) :
    Real.log ((24 * B * (W : ℝ) ^ 3) ^ (2 * W)) ≤
      (2 * Real.log (24 * B) + 6) * W * Real.log (Real.exp 1 * W) := by
  have hlog := log_nat_polynomial_le_log_e_scale W hW (24 * B) (by linarith) 3
  rw [Real.log_pow]
  calc
    ((2 * W : ℕ) : ℝ) * Real.log (24 * B * (W : ℝ) ^ 3) ≤
        ((2 * W : ℕ) : ℝ) *
          ((Real.log (24 * B) + (3 : ℝ)) * Real.log (Real.exp 1 * W)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by push_cast; ring

end BernoulliSection8
