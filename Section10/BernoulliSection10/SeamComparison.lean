import BernoulliSection10.PacketBoundary
import BernoulliLinearAlgebra.ExteriorOperatorVolume
import Mathlib.Tactic

/-!
# Deterministic seam comparison

This module contains the deterministic logarithmic triangle used in
Proposition 10.7 and the exact comparison between Gram volume and the maximal
exterior operator growth.  Conditional expectation is applied only after
these pointwise inequalities have been assembled.
-/

open scoped Matrix

noncomputable section

namespace BernoulliSection10

open Matrix
open BernoulliLinearAlgebra

variable {W : Type*} [Fintype W] [LinearOrder W]

local instance seamComparisonSumLinearOrder : LinearOrder (W ⊕ W) :=
  BernoulliLinearAlgebra.twoBlockSpecializationSumLinearOrder

/-- The outside pressure in the scalar-cleared form used after the packet
cut. -/
def outsideExteriorPressure (c : ℂ)
    (R : Matrix (W ⊕ W) (W ⊕ W) ℂ) : ℝ :=
  Real.log ‖c‖ + Real.log (maxExteriorOperatorGrowth R)

/-- The degree maximum is strictly positive.  This follows without choosing
a maximizing degree: the positive Gram volume is bounded above by a positive
multiple of that maximum. -/
theorem maxExteriorOperatorGrowth_pos_twoBlock
    (R : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    0 < maxExteriorOperatorGrowth R := by
  have hvol : 0 < gramVolume R := gramVolume_pos R
  have hupper :=
    gramVolume_le_two_pow_card_mul_maxExteriorOperatorGrowth_twoBlock R
  have hpow : 0 < (2 : ℝ) ^ Fintype.card W := pow_pos (by norm_num) _
  by_contra h
  have hnonpos : maxExteriorOperatorGrowth R ≤ 0 := le_of_not_gt h
  have : (2 : ℝ) ^ Fintype.card W * maxExteriorOperatorGrowth R ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hpow.le hnonpos
  exact (not_le_of_gt hvol) (hupper.trans this)

/-- Logarithmic form of the deterministic Gram-volume versus maximal
exterior-growth comparison.  The loss is exactly `W log 2`. -/
theorem abs_log_gramVolume_sub_log_maxExteriorOperatorGrowth_le
    (R : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    |Real.log (gramVolume R) - Real.log (maxExteriorOperatorGrowth R)| ≤
      (Fintype.card W : ℝ) * Real.log 2 := by
  let K : ℝ := (2 : ℝ) ^ Fintype.card W
  have hK : 1 ≤ K := by
    exact one_le_pow₀ (by norm_num)
  have hmax : 0 < maxExteriorOperatorGrowth R :=
    maxExteriorOperatorGrowth_pos_twoBlock R
  have hlower : K⁻¹ * maxExteriorOperatorGrowth R ≤ gramVolume R := by
    calc
      K⁻¹ * maxExteriorOperatorGrowth R ≤
          1 * maxExteriorOperatorGrowth R := by
        exact mul_le_mul_of_nonneg_right
          ((inv_le_one₀ (zero_lt_one.trans_le hK)).2 hK)
          hmax.le
      _ = maxExteriorOperatorGrowth R := one_mul _
      _ ≤ gramVolume R := maxExteriorOperatorGrowth_le_gramVolume R
  have hupper : gramVolume R ≤ K * maxExteriorOperatorGrowth R := by
    simpa [K] using
      gramVolume_le_two_pow_card_mul_maxExteriorOperatorGrowth_twoBlock R
  have h := abs_log_sub_log_le_log_of_inv_mul_le_of_le_mul hK
    (gramVolume_pos R) hmax hlower hupper
  simpa [K, Real.log_pow] using h

/-- Pure pointwise triangle behind Proposition 10.7.  The four positive
quantities are respectively the packet evaluation, its coefficient norm,
the boundary Gram volume, and the outside exterior maximum. -/
theorem seam_log_triangle
    {c eval coeff gram growth A B C : ℝ}
    (hc : 0 < c) (heval : 0 < eval) (_hcoeff : 0 < coeff)
    (_hgram : 0 < gram) (_hgrowth : 0 < growth)
    (hEvalCoeff : |Real.log eval - Real.log coeff| ≤ A)
    (hCoeffGram : |Real.log coeff - Real.log gram| ≤ B)
    (hGramGrowth : |Real.log gram - Real.log growth| ≤ C) :
    |Real.log (c * eval) - (Real.log c + Real.log growth)| ≤
      A + B + C := by
  rw [Real.log_mul hc.ne' heval.ne']
  have h₁ :
      |Real.log eval - Real.log gram| ≤ A + B := by
    calc
      |Real.log eval - Real.log gram| =
          |(Real.log eval - Real.log coeff) +
            (Real.log coeff - Real.log gram)| := by ring_nf
      _ ≤ |Real.log eval - Real.log coeff| +
          |Real.log coeff - Real.log gram| := abs_add_le _ _
      _ ≤ A + B := add_le_add hEvalCoeff hCoeffGram
  calc
    |Real.log c + Real.log eval -
        (Real.log c + Real.log growth)| =
        |Real.log eval - Real.log growth| := by ring_nf
    _ = |(Real.log eval - Real.log gram) +
          (Real.log gram - Real.log growth)| := by ring_nf
    _ ≤ |Real.log eval - Real.log gram| +
          |Real.log gram - Real.log growth| := abs_add_le _ _
    _ ≤ (A + B) + C := add_le_add h₁ hGramGrowth
    _ = A + B + C := by ring

end BernoulliSection10
