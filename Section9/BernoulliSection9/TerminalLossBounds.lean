import BernoulliSection9.TerminalConclusion

/-!
# From determinant bounds to terminal logarithmic loss

This module contains the elementary numerical passage used after the
pivot/residual determinant estimate.  A common positive reference product
is eliminated from the coefficient upper bound and the value lower bound;
the resulting coefficient-to-value ratio controls the capped loss.  The
reverse estimate is the analogous one-line consequence of a value upper
bound.
-/

noncomputable section

namespace BernoulliSection9

open MeasureTheory

/-- A direct exponential ratio bound controls the capped logarithmic loss. -/
theorem cappedLogLoss_le_of_ratio_le_exp
    {T c A : Real} {w : Complex}
    (hA : 0 <= A) (hc : 0 <= c) (hw : w ≠ 0)
    (hratio : c / ‖w‖ <= Real.exp A) :
    cappedLogLoss T c w <= A := by
  rw [cappedLogLoss_of_ne_zero hw]
  refine (min_le_right _ _).trans ?_
  have hnonneg : 0 <= c / ‖w‖ := div_nonneg hc (norm_nonneg _)
  exact (Real.posLog_le_posLog hnonneg hratio).trans_eq (by
    simp [Real.posLog_apply, hA])

/-- Eliminate a positive reference product from a coefficient upper bound
and a determinant lower bound.  This is the numerical content of combining
(9.36) and (9.41). -/
theorem cappedLogLoss_le_of_common_product_bounds
    {T c productScale coefficientLoss valueLoss : Real} {w : Complex}
    (hcoefficientLoss : 0 <= coefficientLoss)
    (hvalueLoss : 0 <= valueLoss)
    (hc : 0 <= c) (hproduct : 0 < productScale)
    (hcoeff : c <= Real.exp coefficientLoss * productScale)
    (hvalue : Real.exp (-valueLoss) * productScale <= ‖w‖) :
    cappedLogLoss T c w <= coefficientLoss + valueLoss := by
  have hlowerPos : 0 < Real.exp (-valueLoss) * productScale :=
    mul_pos (Real.exp_pos _) hproduct
  have hnormPos : 0 < ‖w‖ := hlowerPos.trans_le hvalue
  have hw : w ≠ 0 := norm_pos_iff.mp hnormPos
  apply cappedLogLoss_le_of_ratio_le_exp
    (add_nonneg hcoefficientLoss hvalueLoss) hc hw
  apply (div_le_iff₀ hnormPos).2
  have hexp :
      Real.exp (coefficientLoss + valueLoss) * Real.exp (-valueLoss) =
        Real.exp coefficientLoss := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    c <= Real.exp coefficientLoss * productScale := hcoeff
    _ = Real.exp (coefficientLoss + valueLoss) *
          (Real.exp (-valueLoss) * productScale) := by rw [← hexp]; ring
    _ <= Real.exp (coefficientLoss + valueLoss) * ‖w‖ :=
      mul_le_mul_of_nonneg_left hvalue (Real.exp_nonneg _)

/-- Pointwise determinant lower bounds off a measurable bad event yield the
paper's capped estimate after charging that event at height `T`. -/
theorem integral_cappedLogLoss_le_of_common_product_bounds
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (T c productScale coefficientLoss valueLoss badProbability : Real)
    (value : Omega -> Complex) (bad : Set Omega)
    (hT : 0 <= T) (hcoefficientLoss : 0 <= coefficientLoss)
    (hvalueLoss : 0 <= valueLoss) (hc : 0 <= c)
    (hproduct : 0 < productScale)
    (hcoeff : c <= Real.exp coefficientLoss * productScale)
    (hbad : MeasurableSet bad)
    (hint : Integrable (fun omega => cappedLogLoss T c (value omega)) mu)
    (hprob : mu.real bad <= badProbability)
    (hvalue : forall omega, omega ∉ bad ->
      Real.exp (-valueLoss) * productScale <= ‖value omega‖) :
    ∫ omega, cappedLogLoss T c (value omega) ∂mu <=
      coefficientLoss + valueLoss + badProbability * T := by
  apply integral_cappedLogLoss_le_good_add_bad mu T c
    (coefficientLoss + valueLoss) badProbability value bad hT
    (add_nonneg hcoefficientLoss hvalueLoss) hbad hint hprob
  intro omega homega
  exact cappedLogLoss_le_of_common_product_bounds
    hcoefficientLoss hvalueLoss hc hproduct hcoeff (hvalue omega homega)

/-- A value upper bound by an exponential multiple of the coefficient norm
gives the reverse logarithmic estimate. -/
theorem posLog_value_div_coefficient_le
    {c A : Real} {w : Complex}
    (hA : 0 <= A) (hc : 0 < c)
    (hvalue : ‖w‖ <= Real.exp A * c) :
    Real.posLog (‖w‖ / c) <= A := by
  have hratio : ‖w‖ / c <= Real.exp A := by
    exact (div_le_iff₀ hc).2 (by simpa [mul_comm] using hvalue)
  exact (Real.posLog_le_posLog (div_nonneg (norm_nonneg _) hc.le) hratio).trans_eq
    (by simp [Real.posLog_apply, hA])

end BernoulliSection9
