import Vendor.GinibreLSV.Deterministic
import ShortRingAnchor.LeastSingularValueAdapter
import Mathlib.Data.Real.Pointwise

/-! # Proposition 3.8: deterministic scaling of the actual least singular value -/

noncomputable section
namespace ShortRingAnchor.Proposition38

/-- Proposition 3.8, Cook rescaling: the bottom singular value scales by
the absolute value of the scalar. Proved through the Rayleigh quotient. -/
theorem leastSingularValue_smul {n : ℕ} (hn : 0 < n)
    (X : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    GinibreLSV.leastSingularValue (c • X) = ‖c‖ * GinibreLSV.leastSingularValue X := by
  rw [GinibreLSV.leastSingularValue_eq_iInf_singularQuotient hn,
    GinibreLSV.leastSingularValue_eq_iInf_singularQuotient hn,
    Real.mul_iInf_of_nonneg (norm_nonneg c)]
  congr 1
  funext x
  simp only [LinearMap.singularQuotient, map_smul, LinearMap.smul_apply,
    norm_smul, mul_div_assoc]

/-- Proposition 3.8, (3.22): the bottom singular value in Cook's statement
is the last member of the same family used by the logarithmic proof. -/
theorem leastSingularValue_shift_eq {n : ℕ} (hn : 0 < n)
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    GinibreLSV.leastSingularValue (X - z • 1) =
      shiftedSingularValueFamily X z (lastSingularValueIndex n hn) := rfl

/-- Proposition 3.8, Cook choice `t=N^(-1/4)`: after division by
`sqrt(3W)`, the resulting floor is at least `N^(-2)` for `N ≥ 3`. -/
theorem cook_threshold_dominates_polynomial {N W : ℕ}
    (hN : 3 ≤ N) (hWN : W ≤ N) :
    Real.sqrt (3 * (W : ℝ)) * (N : ℝ) ^ (-(2 : ℝ)) ≤
      (N : ℝ) ^ (-(1 / 4 : ℝ)) / Real.sqrt N := by
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hroot : Real.sqrt (3 * (W : ℝ)) ≤ (N : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    have hw : (W : ℝ) ≤ N := by exact_mod_cast hWN
    exact ⟨hn0.le, by nlinarith⟩
  have hfirst : Real.sqrt (3 * (W : ℝ)) * (N : ℝ) ^ (-(2 : ℝ)) ≤
      (N : ℝ) ^ (-(1 : ℝ)) := by
    calc
      _ ≤ (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hn0.le _)
      _ = _ := by
        conv_lhs => lhs; rw [← Real.rpow_one (N : ℝ)]
        rw [← Real.rpow_add hn0]
        norm_num
  apply hfirst.trans
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hn0]
  apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ N)
  norm_num

end ShortRingAnchor.Proposition38
