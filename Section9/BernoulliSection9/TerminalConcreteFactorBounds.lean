import BernoulliSection9.TerminalConcreteConclusion
import Mathlib.Tactic

/-!
# Uniform scalar comparison for the terminal determinant factor

This module records the scalar monotonicity argument which replaces the
actual RRQR rank and the two actual square sizes by their uniform packet-width
bounds.  The inner Cook powers are real powers; their outer powers are natural
powers.
-/

noncomputable section

namespace BernoulliSection9

open BernoulliLinearAlgebra
open TerminalAssembly

private theorem uniformCookPower_le_actualCookPower
    {W n : Nat} {beta : Real}
    (hW : 9 <= W) (hWdivn : W / 3 <= n) (hnW : n <= 3 * W)
    (hbeta : 0 < beta) :
    ((((3 * W : Nat) : Real) ^ (-beta)) ^ (3 * W)) <=
      ((((n : Nat) : Real) ^ (-beta)) ^ n) := by
  have hn : 0 < n := by omega
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have h3WReal : 0 < ((3 * W : Nat) : Real) := by positivity
  have hn_le : (n : Real) <= ((3 * W : Nat) : Real) := by
    exact_mod_cast hnW
  have hneg : -beta <= 0 := by linarith
  have hbase :
      ((3 * W : Nat) : Real) ^ (-beta) <=
        (n : Real) ^ (-beta) :=
    Real.rpow_le_rpow_of_nonpos hnReal hn_le hneg
  have huniform_nonneg :
      0 <= ((3 * W : Nat) : Real) ^ (-beta) :=
    Real.rpow_nonneg h3WReal.le _
  have hactual_nonneg : 0 <= (n : Real) ^ (-beta) :=
    Real.rpow_nonneg hnReal.le _
  have hn_one : (1 : Real) <= n := by exact_mod_cast hn
  have hactual_le_one : (n : Real) ^ (-beta) <= 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn_one hneg
  calc
    (((3 * W : Nat) : Real) ^ (-beta)) ^ (3 * W) <=
        ((n : Real) ^ (-beta)) ^ (3 * W) :=
      pow_le_pow_left₀ huniform_nonneg hbase _
    _ <= ((n : Real) ^ (-beta)) ^ n :=
      pow_le_pow_of_le_one hactual_nonneg hactual_le_one hnW

/-- The fixed determinant factor used by the uniform terminal theorem is no
larger than the determinant factor with the actual RRQR rank and actual Cook
square sizes.  Its hypotheses are entirely scalar and independent of the
outer matrix or of any RRQR/CUR certificate. -/
theorem terminalUniformDeterminantFactor_le_actualFactors
    (cook : CookDeformedSquareInput) {W Kz r n₁ n₂ : Nat}
    (hW : 9 <= W) (hr : r <= 2 * W)
    (hWdivn₁ : W / 3 <= n₁) (hn₁W : n₁ <= 3 * W)
    (hWdivn₂ : W / 3 <= n₂) (hn₂W : n₂ <= 3 * W) :
    terminalUniformDeterminantFactor cook W Kz <=
      (2 : Real)⁻¹ ^ r *
        ((((2 * W : Nat) : Real) ^ strongRRQRExponent)⁻¹ ^ r) *
        ((((n₁ : Nat) : Real) ^
          (-cook.beta (terminalCanonicalFirstCookExponent Kz))) ^ n₁) *
        ((((n₂ : Nat) : Real) ^
          (-cook.beta
            (terminalCanonicalSecondCookExponent cook Kz))) ^ n₂) := by
  have hhalf :
      (2 : Real)⁻¹ ^ (2 * W) <= (2 : Real)⁻¹ ^ r := by
    exact pow_le_pow_of_le_one (by positivity) (by norm_num) hr
  have h2WReal : 0 < ((2 * W : Nat) : Real) := by positivity
  have h2W_one : (1 : Real) <= ((2 * W : Nat) : Real) := by
    have : 1 <= 2 * W := by omega
    exact_mod_cast this
  have hrrqrBase_pos :
      0 < (((2 * W : Nat) : Real) ^ strongRRQRExponent)⁻¹ := by
    positivity
  have hrrqrBase_le_one :
      (((2 * W : Nat) : Real) ^ strongRRQRExponent)⁻¹ <= 1 := by
    apply (inv_le_one₀ (pow_pos h2WReal _)).2
    exact one_le_pow₀ h2W_one
  have hrrqr :
      ((((2 * W : Nat) : Real) ^ strongRRQRExponent)⁻¹ ^ (2 * W)) <=
        ((((2 * W : Nat) : Real) ^ strongRRQRExponent)⁻¹ ^ r) :=
    pow_le_pow_of_le_one hrrqrBase_pos.le hrrqrBase_le_one hr
  have hcook₁ := uniformCookPower_le_actualCookPower
    hW hWdivn₁ hn₁W
      (cook.beta_pos (terminalCanonicalFirstCookExponent Kz))
  have hcook₂ := uniformCookPower_le_actualCookPower
    hW hWdivn₂ hn₂W
      (cook.beta_pos (terminalCanonicalSecondCookExponent cook Kz))
  unfold terminalUniformDeterminantFactor
  gcongr

end BernoulliSection9
