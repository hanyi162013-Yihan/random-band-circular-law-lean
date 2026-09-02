import BernoulliSection8.ResetAveraging
import BernoulliSection8.RademacherBoundaryGrowth

/-!
# The reset loss on one literal chronological interval

The observation has chronological order past, reset, core. Independent
product coordinates appear only in the proof of its expectation bound.
-/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def intervalLastCore (W p q : ℕ) (x : IntervalRows W (q + 3 + p)) : IntervalRows W p :=
  intervalRestriction (Fin.natAddEmb (q + 3)) x

def intervalPastBeforeReset (W p q : ℕ) (x : IntervalRows W (q + 3 + p)) :
    IntervalRows W q :=
  intervalRestriction (Fin.castAddEmb 3)
    (intervalRestriction (Fin.castAddEmb p) x)

def intervalResetLoss (W p q : ℕ) (z : ℂ) (r : Fin (2 * W + 1)) (T : ℝ)
    (x : IntervalRows W (q + 3 + p)) : ℝ :=
  cappedSpliceLoss T
    ‖intervalClearedProduct W p z (intervalLastCore W p q x) r‖
    ‖intervalClearedProduct W q z (intervalPastBeforeReset W p q x) r‖
    ‖intervalClearedProduct W (q + 3 + p) z x r‖

theorem measurable_intervalResetLoss (W p q : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) (T : ℝ) : Measurable (intervalResetLoss W p q z r T) := by
  have hcore : Continuous (intervalLastCore W p q) := by
    unfold intervalLastCore intervalRestriction
    fun_prop
  have hpast : Continuous (intervalPastBeforeReset W p q) := by
    unfold intervalPastBeforeReset intervalRestriction
    fun_prop
  exact measurable_cappedSpliceLoss T
    ((continuous_intervalClearedProduct W p z r).comp hcore).norm.measurable
    ((continuous_intervalClearedProduct W q z r).comp hpast).norm.measurable
    (continuous_intervalClearedProduct W (q + 3 + p) z r).norm.measurable

theorem intervalResetLoss_resetSandwichRowsFlat (W p q : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) (T : ℝ)
    (v : (IntervalRows W p × IntervalRows W q) × IntervalRows W 3) :
    intervalResetLoss W p q z r T (resetSandwichRowsFlat W p q v) =
      resetLossFlat W p q z r T v := by
  have hc : intervalLastCore W p q (resetSandwichRowsFlat W p q v) = v.1.1 := by
    simp [intervalLastCore, resetSandwichRowsFlat, resetSandwichRows]
  have hp : intervalPastBeforeReset W p q (resetSandwichRowsFlat W p q v) = v.1.2 := by
    simp [intervalPastBeforeReset, resetSandwichRowsFlat, resetSandwichRows]
  simp only [intervalResetLoss, hc, hp, resetSandwichRowsFlat,
    intervalClearedProduct_resetSandwichRows, resetLossFlat, physicalCappedResetLoss]

/-- The coefficient-norm estimate is discharged here by the explicit
Nguyen endpoint constant. Only Cook and Nguyen remain as input objects. -/
theorem intervalResetLoss_integral_le
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput.{0, 0})
    (hI : 1 ≤ I.subgaussianBound) (W p q : ℕ) (z : ℂ)
    (hW : rademacherBoundaryWidthThreshold cook z ≤ W)
    (hWI : interfaceCanonicalLargeWThreshold I ≤ W)
    (r : Fin (2 * W + 1)) {T : ℝ} (hT : 0 < T) :
    (∫ x, intervalResetLoss W p q z r T x
      ∂intervalRowsLaw W (q + 3 + p) rademacherLaw) ≤
      rademacherBoundaryLogConstant I z * W * densityLogScale W +
        rademacherBoundaryBaseLoss cook W z + T *
          (rademacherBoundaryBadProbability cook W + (9 + 3 * ((p : ℝ) + q)) *
            Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ))) := by
  have hW0 : 0 < W := (rademacherBoundaryWidthThreshold_pos cook z).trans_le hW
  rw [← real_integral_comp_measurePreserving
    (resetSandwichRowsFlat_measurePreserving (μ := rademacherLaw) W p q)
    (measurable_intervalResetLoss W p q z r T)]
  simp only [Function.comp_def, intervalResetLoss_resetSandwichRowsFlat]
  apply resetLossFlat_integral_le cook I hI W p q z hW hWI r hT
  · exact mul_nonneg (mul_nonneg (rademacherBoundaryLogConstant_nonneg I z)
      (Nat.cast_nonneg W)) (densityLogScale_nonneg hW0)
  · exact fun ep hep => neg_log_rademacherBoundaryInverseGamma_le_on_endpoint_good
      I W hW0 z ep hep

end BernoulliSection8
