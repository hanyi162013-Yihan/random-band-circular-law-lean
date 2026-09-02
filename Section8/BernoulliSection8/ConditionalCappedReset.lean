import BernoulliSection8.CappedReset
import BernoulliSection8.RademacherFrameSmallBall
import BernoulliSection10.ClearedSingularTest

/-!
# A fresh physical Bernoulli reset, with core and past frozen

The scalar test is selected inside this fixed-fiber proof. The final
integrand is the norm of the actual physical product. The coefficient
lower bound is deterministic endpoint data, not a new small-ball input.
-/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra

set_option maxHeartbeats 1000000

def physicalCappedResetLoss (W p q : ℕ) (z : ℂ) (r : Fin (2 * W + 1)) (T : ℝ)
    (core : IntervalRows W p) (past : IntervalRows W q) (reset : IntervalRows W 3) : ℝ :=
  cappedSpliceLoss T ‖intervalClearedProduct W p z core r‖
    ‖intervalClearedProduct W q z past r‖
    ‖intervalClearedProduct W p z core r *
      intervalClearedProduct W 3 z reset r * intervalClearedProduct W q z past r‖

theorem measurable_physicalCappedResetLoss (W p q : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) (T : ℝ)
    (core : IntervalRows W p) (past : IntervalRows W q) :
    Measurable (physicalCappedResetLoss W p q z r T core past) := by
  apply measurable_cappedSpliceLoss T measurable_const measurable_const
  exact ((continuous_const.matrix_mul
    (continuous_intervalClearedProduct W 3 z r)).matrix_mul continuous_const).norm.measurable

theorem physicalCappedResetLoss_nonneg (W p q : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) {T : ℝ} (hT : 0 ≤ T)
    (core : IntervalRows W p) (past : IntervalRows W q) (reset : IntervalRows W 3) :
    0 ≤ physicalCappedResetLoss W p q z r T core past reset :=
  cappedSpliceLoss_nonneg hT _ _ _

theorem physicalCappedResetLoss_le_cap (W p q : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) (T : ℝ)
    (core : IntervalRows W p) (past : IntervalRows W q) (reset : IntervalRows W 3) :
    physicalCappedResetLoss W p q z r T core past reset ≤ T :=
  cappedSpliceLoss_le_cap _ _ _ _

/-- An internal fixed-fiber form of (8.37). All random variables here are
the seven fresh blocks in the literal normalized three-site packet. -/
theorem physicalCappedResetLoss_fresh_integral_le
    (cook : CookDeformedSquareInput.{0, 0}) (W p q : ℕ) (z : ℂ)
    (hW : rademacherBoundaryWidthThreshold cook z ≤ W)
    (core : IntervalRows W p) (past : IntervalRows W q)
    (hcoreB : ∀ j, IsUnit (intervalSiteBlocks z core j).B.det)
    (hcoreC : ∀ j, IsUnit (intervalSiteBlocks z core j).C.det)
    (hpastB : ∀ j, IsUnit (intervalSiteBlocks z past j).B.det)
    (hpastC : ∀ j, IsUnit (intervalSiteBlocks z past j).C.det)
    (ep : EndpointBlockPair W)
    (hCL : IsUnit (normalizedBlockMatrix W ep.1).det)
    (hBR : IsUnit (normalizedBlockMatrix W ep.2).det)
    (r : Fin (2 * W + 1)) {T D : ℝ} (hT : 0 < T) (hD : 0 ≤ D)
    (hGamma : -Real.log (rademacherBoundaryInverseGamma W z
      (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)) ≤ D) :
    (∫ x, physicalCappedResetLoss W p q z r T core past
      (packetPhysicalRows W (ep, x)) ∂packetAtomRowsLaw W rademacherLaw) ≤
        D + rademacherBoundaryBaseLoss cook W z +
          rademacherBoundaryBadProbability cook W * T := by
  have hW0 : 0 < W := by
    have h1 : 1 ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
    omega
  letI : Nonempty (Set.powersetCard (Fin W ⊕ Fin W) r.1) := by
    rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
    apply Nat.choose_pos
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  let A := intervalClearedProduct W p z core r
  let B := intervalClearedProduct W q z past r
  have hA : IsUnit A.det := intervalClearedProduct_det_isUnit W p z core hcoreB hcoreC r
  have hB : IsUnit B.det := intervalClearedProduct_det_isUnit W q z past hpastB hpastC r
  have hA0 : 0 < ‖A‖ := norm_pos_iff.mpr ((Matrix.isUnit_iff_isUnit_det A).mpr hA).ne_zero
  have hB0 : 0 < ‖B‖ := norm_pos_iff.mpr ((Matrix.isUnit_iff_isUnit_det B).mpr hB).ne_zero
  obtain ⟨U, V, s, htest⟩ := exists_cleared_exterior_product_scalar_test
    (intervalTransferProduct W p z core) (intervalTransferProduct W q z past)
    (intervalTransferProduct_det_isUnit W p z core hcoreB hcoreC)
    (intervalTransferProduct_det_isUnit W q z past hpastB hpastC)
    (intervalClearingFactor W p z core) (intervalClearingFactor W q z past) r.1
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  rw [← intervalClearedProduct_eq_clearing_smul_compound W p z core hcoreB r,
    ← intervalClearedProduct_eq_clearing_smul_compound W q z past hpastB r] at htest
  let c := rademacherPacketFrameCoefficient W r.1 z
    (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2) U V s
  have hc := rademacherPacketFrameCoefficient_lower_and_pos W r.1 hW0 z
    (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2) hCL hBR U V s
  have hGamma0 := rademacherBoundaryInverseGamma_pos W hW0 z
    (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
  have hcLower : -Real.log c ≤ D := by
    have hlog := Real.log_le_log hGamma0 hc.1
    dsimp [c]
    linarith
  have hpacket : Measurable (fun x : PacketAtomRows W => packetPhysicalRows W (ep, x)) :=
    (packetPhysicalRows_measurePreserving (μ := rademacherLaw) W).measurable.comp
      (measurable_const.prodMk measurable_id)
  apply integral_cappedSpliceLoss_le (packetAtomRowsLaw W rademacherLaw)
    hT.le hA0 hB0 hc.2 hD hcLower
  · have hproduct : Continuous (fun reset : IntervalRows W 3 =>
        A * intervalClearedProduct W 3 z reset r * B) :=
      (continuous_const.matrix_mul
        (continuous_intervalClearedProduct W 3 z r)).matrix_mul continuous_const
    exact hproduct.norm.measurable.comp hpacket
  · exact (continuous_physicalPacketCoefficient W z r U V s).measurable.comp hpacket
  · intro x
    exact htest (intervalClearedProduct W 3 z (packetPhysicalRows W (ep, x)) r)
  · exact rademacherPhysicalPacketCoefficient_capped cook W z hW ep hCL hBR r U V s T hT

end BernoulliSection8
