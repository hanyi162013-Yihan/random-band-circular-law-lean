import CircularLawSection6.DeterminantRowFibers
import CircularLawSections56.Section5.UniformPaperConstants

/-! # Reusing the Section 5 uniform logarithmic constant

The row-affine bound has exactly the same numerical expression as the
Section 4 pressure fiber bound. Its Section 5 constant estimate therefore
gives the required `N log²(eN)` determinant variance bound directly.
-/

open MeasureTheory ProbabilityTheory CircularLawSection4
open CircularLawSection4.PaperIndicatorWeights CircularLawSections56.Section5

noncomputable section

namespace CircularLawSection6

attribute [local instance] iidMeasure_isProbability

theorem affineRowLogBound_le_uniform (d : ℕ) {c L : ℝ} (hc : 0 < c) (z : ℂ) :
    affineRowLogBound (d + 1) (Real.sqrt (c / (d + 2 : ℝ))) L z ≤
      uniformFiberSquareConstant c L z * dimensionLogScale d ^ 2 := by
  simpa only [affineRowLogBound, complexPaperPressureFiberL2Bound,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using
    complexPaperPressureFiberL2Bound_le_uniform d c L z hc

theorem dimensionLogScale_eq_logEN (d : ℕ) :
    dimensionLogScale d = Real.log (Real.exp 1 * (d + 2 : ℝ)) := by
  rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity : (d + 2 : ℝ) ≠ 0), Real.log_exp]
  rfl

/-- A finite-size determinant bound for actual IID matrices. Only the
diagonal amplitude lower bound is required, not comparable off-diagonal
weights or any extra determinant integrability hypothesis. -/
theorem weightedRowsLogDet_variance_le_uniform
    (ν : Measure ℂ) [IsProbabilityMeasure ν] {L c : ℝ}
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (hc : 0 < c) (hc1 : c ≤ 1) (d : ℕ)
    (b : Matrix (Fin (d + 2)) (Fin (d + 2)) ℂ) (z : ℂ)
    (hb : ∀ i, Real.sqrt (c / (d + 2 : ℝ)) ≤ ‖b i i‖)
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    variance (weightedRowsLogDet b z) (iidMeasure (iidMeasure ν (d + 2)) (d + 2)) ≤
      (2 * uniformFiberSquareConstant c L z) * (d + 2 : ℝ) *
        (Real.log (Real.exp 1 * (d + 2 : ℝ))) ^ 2 := by
  have hq : 0 < Real.sqrt (c / (d + 2 : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hq1 : Real.sqrt (c / (d + 2 : ℝ)) ≤ 1 := by
    apply Real.sqrt_le_one.2
    apply (div_le_one (by positivity : (0 : ℝ) < d + 2)).2
    exact hc1.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  have hv := (weightedRowsLogDet_memLp_and_variance ν hν hL b z hq hq1 hb hInt hSecond).2
  have hu := mul_le_mul_of_nonneg_left (affineRowLogBound_le_uniform (L := L) d hc z)
    (show 0 ≤ 2 * (d + 2 : ℝ) by positivity)
  have hv' : variance (weightedRowsLogDet b z)
      (iidMeasure (iidMeasure ν (d + 2)) (d + 2)) ≤
      2 * (d + 2 : ℝ) * affineRowLogBound (d + 1) (Real.sqrt (c / (d + 2 : ℝ))) L z := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hv
  calc
    _ ≤ 2 * (d + 2 : ℝ) * (uniformFiberSquareConstant c L z * dimensionLogScale d ^ 2) :=
      hv'.trans hu
    _ = _ := by rw [dimensionLogScale_eq_logEN]; ring

end CircularLawSection6
