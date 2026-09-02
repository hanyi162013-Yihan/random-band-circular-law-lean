import SubgaussianSection8.BoundedBlockGrowth
import SubgaussianSection8.BlockEntryControl
import BernoulliSection8.ClippedLog

/-! Deterministic one-site growth from the measurable general subgaussian interface event. -/
open Filter MeasureTheory Set Topology
open scoped BigOperators Matrix Matrix.Norms.Frobenius
noncomputable section
namespace SubgaussianSection8
open BernoulliSection8 BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra Set.powersetCard

local instance transferSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W => (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h => toLex.injective h)

theorem oneSiteForwardMaxLoss_le_of_bounded_blocks
    (W : ℕ) (hW : 0 < W) (z : ℂ) (x : IntervalRows W 1)
    (q : ℂ)
    (hL : ∀ i j, ‖stepL (intervalSiteBlocks z x 0).B i j‖ ≤ 1 + ‖q‖)
    (hK : ∀ i j, ‖stepK (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C i j‖ ≤ 1 + ‖q‖) :
    oneSiteForwardMaxLoss W z x ≤
      oneSiteTensorLogConstant q * W * (1 + Real.posLog (W : ℝ)) := by
  have hfamily : ‖oneSiteClearedFamily W z x‖ ≤ oneSiteCommonDegreeBound W q := by
    apply (pi_norm_le_iff_of_nonneg (oneSiteCommonDegreeBound_nonneg W q)).mpr
    intro r
    have heq : oneSiteClearedFamily W z x r = intervalClearedProduct W 1 z x r := by
      unfold oneSiteClearedFamily oneSiteClearedFamilyRecursiveFunction
      rw [multiAffineRowsToFinRows_leftInverse]
    rw [heq, intervalClearedProduct_one]
    exact (norm_clearedStepCompound_le_degreeBound
      (intervalSiteBlocks z x 0).B (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C q hL hK r.1
      (Nat.le_of_lt_succ r.2)).trans
        (oneSiteDegreeFrobeniusBound_le_common W r.1 (Nat.le_of_lt_succ r.2) q)
  have hlog : Real.posLog (oneSiteCommonDegreeBound W q) ≤
      oneSiteTensorLogBound W q := by
    have hcommon := posLog_oneSiteCommonDegreeBound_le W q
    have hb : 0 ≤ (W : ℝ) * Real.posLog (1 + 2 * (3 * W : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg
    have hc : 0 ≤ Real.log (2 * W + 1 : ℝ) :=
      Real.log_nonneg (le_add_of_nonneg_left (by positivity))
    unfold oneSiteTensorLogBound
    linarith
  exact ((Real.posLog_le_posLog (norm_nonneg _) hfamily).trans hlog).trans
    (oneSiteTensorLogBound_le_scale W hW q)

/-- A positive exponential lower bound controls the positive inverse log,
including the exact normalization used by the interface determinant. -/
theorem posLog_inv_le_of_exp_neg_le {a D : ℝ} (hD : 0 ≤ D)
    (ha : Real.exp (-D) ≤ a) : Real.posLog a⁻¹ ≤ D := by
  have hlog : -D ≤ Real.log a := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (-D)) ha
  rw [Real.posLog_apply, Real.log_inv]
  exact max_le hD (by linarith)

/-- The one-site Hodge envelope has the required W log(eW) size under
literal atom bounds and endpoint determinant lower bounds. -/
theorem oneSiteMaxHodgeEnvelope_le_of_bounded_blocks
    (W : ℕ) (hW : 0 < W) (z : ℂ) (x : IntervalRows W 1)
    (q : ℂ)
    (hL : ∀ i j, ‖stepL (intervalSiteBlocks z x 0).B i j‖ ≤ 1 + ‖q‖)
    (hK : ∀ i j, ‖stepK (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C i j‖ ≤ 1 + ‖q‖) (D : ℝ) (hD : 0 ≤ D)
    (hB : Real.exp (-D * (W : ℝ)) ≤ ‖oneSiteBDet W z x‖)
    (hC : Real.exp (-D * (W : ℝ)) ≤ ‖oneSiteCDet W z x‖) :
    oneSiteMaxHodgeEnvelope W z x ≤
      (2 * (oneSiteTensorLogConstant q + D)) * W *
        (1 + Real.posLog (W : ℝ)) := by
  have hf := oneSiteForwardMaxLoss_le_of_bounded_blocks W hW z x q hL hK
  have hDW : 0 ≤ D * (W : ℝ) := mul_nonneg hD (Nat.cast_nonneg _)
  have hb := posLog_inv_le_of_exp_neg_le hDW (by simpa only [neg_mul] using hB)
  have hc := posLog_inv_le_of_exp_neg_le hDW (by simpa only [neg_mul] using hC)
  have hlift : D * (W : ℝ) ≤ D * (W : ℝ) * (1 + Real.posLog (W : ℝ)) := by
    nlinarith [mul_nonneg hDW (Real.posLog_nonneg (x := (W : ℝ)))]
  unfold oneSiteMaxHodgeEnvelope
  nlinarith


end SubgaussianSection8
