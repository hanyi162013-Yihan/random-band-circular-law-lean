import ShortRingAnchor.LocalStieltjesNet
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Lemma 3.5: a polynomial horizontal net, with the radius in the constant only

Use spacing `N^(-2)`. There are at most `(2R+2)N²` points, so a pointwise
failure bound `N^(-10)` loses only two powers. Interpolation preserves any
comparison exponent `0 < d ≤ 1` if the Lipschitz constant is at most `N`.
For the Stieltjes transforms in Lemma 3.5, `v ≥ N^(-1/8)` suffices for that
last condition. The radius here is arbitrary and fixed, not restricted to 5.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace ShortRingAnchor

/-- Lemma 3.5, net cardinality: replacing radius 5 by fixed `R` costs only a constant. -/
theorem horizontalGridSize_polynomial_le {N R : ℝ} (hN : 1 ≤ N) (hR : 0 ≤ R) :
    (horizontalGridSize R (N ^ (-(2 : ℝ))) : ℝ) ≤ (2 * R + 2) * N ^ (2 : ℝ) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hpow : 1 ≤ N ^ (2 : ℝ) := Real.one_le_rpow hN (by norm_num)
  calc
    _ ≤ 2 * R / N ^ (-(2 : ℝ)) + 2 :=
      horizontalGridSize_le hR (Real.rpow_pos_of_pos hN0 (-(2 : ℝ)))
    _ = 2 * R * N ^ (2 : ℝ) + 2 := by
      rw [Real.rpow_neg hN0.le, div_inv_eq_mul]
    _ ≤ _ := by nlinarith

/-- Lemma 3.5, interpolation budget for the simple `N^(-2)` mesh. -/
theorem horizontalPolynomial_interpolation_error_le {N L d : ℝ}
    (hN : 1 ≤ N) (hL : L ≤ N) (hd : d ≤ 1) :
    2 * L * N ^ (-(2 : ℝ)) ≤ 2 * N ^ (-d) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hpow : N ^ (-(1 : ℝ)) ≤ N ^ (-d) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  calc
    2 * L * N ^ (-(2 : ℝ)) ≤ 2 * N * N ^ (-(2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by norm_num))
        (Real.rpow_nonneg hN0.le _)
    _ = 2 * N ^ (-(1 : ℝ)) := by
      calc
        2 * N * N ^ (-(2 : ℝ)) = 2 * (N ^ (1 : ℝ) * N ^ (-(2 : ℝ))) := by
          rw [Real.rpow_one, mul_assoc]
        _ = _ := by rw [← Real.rpow_add hN0]; norm_num
    _ ≤ 2 * N ^ (-d) := mul_le_mul_of_nonneg_left hpow (by norm_num)

/-- Lemma 3.5: the Stieltjes Lipschitz constant is small enough at the manuscript scale. -/
theorem inverse_height_sq_le_dimension {N v : ℝ}
    (hN : 1 ≤ N) (hv : N ^ (-(1 / 8 : ℝ)) ≤ v) : v⁻¹ ^ 2 ≤ N := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hlower : 0 < N ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hv0 : 0 < v := hlower.trans_le hv
  have hinv : v⁻¹ ≤ N ^ (1 / 8 : ℝ) := by
    calc
      v⁻¹ ≤ (N ^ (-(1 / 8 : ℝ)))⁻¹ := inv_anti₀ hlower hv
      _ = N ^ (1 / 8 : ℝ) := by rw [Real.rpow_neg hN0.le, inv_inv]
  calc
    v⁻¹ ^ 2 ≤ (N ^ (1 / 8 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hv0.le) hinv 2
    _ = N ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_mul_natCast hN0.le]
      norm_num
    _ ≤ N := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (1 / 4 : ℝ) ≤ 1)

/-- Lemma 3.5: a common grid comparison exponent survives interpolation on any fixed interval. -/
theorem horizontalGrid_comparison_polynomial {N R L d : ℝ}
    (hN : 1 ≤ N) (hL0 : 0 ≤ L) (hL : L ≤ N) (hd : d ≤ 1)
    (f g : ℝ → ℂ)
    (hf : ∀ u w, ‖f u - f w‖ ≤ L * |u - w|)
    (hg : ∀ u w, ‖g u - g w‖ ≤ L * |u - w|)
    (hgrid : ∀ i : Fin (horizontalGridSize R (N ^ (-(2 : ℝ)))),
      ‖f (horizontalGridCenter R (N ^ (-(2 : ℝ))) i) -
        g (horizontalGridCenter R (N ^ (-(2 : ℝ))) i)‖ ≤ 2 * N ^ (-d))
    {u : ℝ} (hu : u ∈ Icc (-R) R) : ‖f u - g u‖ ≤ 4 * N ^ (-d) := by
  have h := horizontalGrid_comparison
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hN) (-(2 : ℝ))) hL0 f g hf hg hgrid hu
  have herror := horizontalPolynomial_interpolation_error_le hN hL hd
  linarith

/-- Lemma 3.5, union-bound arithmetic: a point tail `N^(-10)` becomes `O_R(N^(-8))`. -/
theorem horizontalPolynomial_failure_budget {N R : ℝ} (hN : 1 ≤ N) (hR : 0 ≤ R) :
    (horizontalGridSize R (N ^ (-(2 : ℝ))) : ℝ≥0∞) * ENNReal.ofReal (N ^ (-(10 : ℝ))) ≤
      ENNReal.ofReal ((2 * R + 2) * N ^ (-(8 : ℝ))) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hgrid := horizontalGridSize_polynomial_le hN hR
  calc
    _ ≤ ENNReal.ofReal ((2 * R + 2) * N ^ (2 : ℝ)) *
        ENNReal.ofReal (N ^ (-(10 : ℝ))) := by
      apply mul_le_mul'
      · simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hgrid
      · exact le_rfl
    _ = ENNReal.ofReal (((2 * R + 2) * N ^ (2 : ℝ)) * N ^ (-(10 : ℝ))) := by
      rw [ENNReal.ofReal_mul (show 0 ≤ (2 * R + 2) * N ^ (2 : ℝ) by positivity)]
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hN0]
      norm_num

end ShortRingAnchor
