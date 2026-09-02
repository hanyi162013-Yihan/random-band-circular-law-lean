import BernoulliSection8.RademacherInterface
import BernoulliSection8.ClippedLog
import BernoulliSection10.HodgeFamilyGrowth

/-!
# Cleared-transfer bounds on the Rademacher interface event

Bounded Rademacher atoms give an explicit uniform bound for every forward
exterior degree. Determinant lower bounds on the Nguyen good event and the
proved complementary-degree Hodge identity give the inverse bound. Their
sum controls every chronological interval product at the source's
`O(L log W)` scale. No density or new probability estimate is used.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators Matrix Matrix.Norms.Frobenius

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra
open Set.powersetCard

local instance transferBoundsSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W => (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h => toLex.injective h)

/-- The deterministic forward family estimate applies to all atom values
in [-1,1], and in particular to every Rademacher configuration. -/
theorem oneSiteForwardMaxLoss_le_of_bounded_atoms
    (W : ℕ) (hW : 0 < W) (z : ℂ) (x : IntervalRows W 1)
    (hx : OneSiteAtomsBound W x) :
    oneSiteForwardMaxLoss W z x ≤
      oneSiteTensorLogConstant z * W * (1 + Real.posLog (W : ℝ)) := by
  have hfamily : ‖oneSiteClearedFamily W z x‖ ≤ oneSiteCommonDegreeBound W z := by
    apply (pi_norm_le_iff_of_nonneg (oneSiteCommonDegreeBound_nonneg W z)).mpr
    intro r
    have heq : oneSiteClearedFamily W z x r = intervalClearedProduct W 1 z x r := by
      unfold oneSiteClearedFamily oneSiteClearedFamilyRecursiveFunction
      rw [multiAffineRowsToFinRows_leftInverse]
    rw [heq, intervalClearedProduct_one]
    exact (norm_clearedStepCompound_le_degreeBound hW z x hx r.1
      (Nat.le_of_lt_succ r.2)).trans
        (oneSiteDegreeFrobeniusBound_le_common W r.1 (Nat.le_of_lt_succ r.2) z)
  have hlog : Real.posLog (oneSiteCommonDegreeBound W z) ≤
      oneSiteTensorLogBound W z := by
    have hcommon := posLog_oneSiteCommonDegreeBound_le W z
    have hb : 0 ≤ (W : ℝ) * Real.posLog (1 + 2 * (3 * W : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg
    have hc : 0 ≤ Real.log (2 * W + 1 : ℝ) := Real.log_nonneg (by positivity)
    unfold oneSiteTensorLogBound
    linarith
  exact ((Real.posLog_le_posLog (norm_nonneg _) hfamily).trans hlog).trans
    (oneSiteTensorLogBound_le_scale W hW z)

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
theorem oneSiteMaxHodgeEnvelope_le_of_bounded_atoms
    (W : ℕ) (hW : 0 < W) (z : ℂ) (x : IntervalRows W 1)
    (hx : OneSiteAtomsBound W x) (D : ℝ) (hD : 0 ≤ D)
    (hB : Real.exp (-D * (W : ℝ)) ≤ ‖oneSiteBDet W z x‖)
    (hC : Real.exp (-D * (W : ℝ)) ≤ ‖oneSiteCDet W z x‖) :
    oneSiteMaxHodgeEnvelope W z x ≤
      (2 * (oneSiteTensorLogConstant z + D)) * W *
        (1 + Real.posLog (W : ℝ)) := by
  have hf := oneSiteForwardMaxLoss_le_of_bounded_atoms W hW z x hx
  have hDW : 0 ≤ D * (W : ℝ) := mul_nonneg hD (Nat.cast_nonneg _)
  have hb := posLog_inv_le_of_exp_neg_le hDW (by simpa only [neg_mul] using hB)
  have hc := posLog_inv_le_of_exp_neg_le hDW (by simpa only [neg_mul] using hC)
  have hlift : D * (W : ℝ) ≤ D * (W : ℝ) * (1 + Real.posLog (W : ℝ)) := by
    nlinarith [mul_nonneg hDW (Real.posLog_nonneg (x := (W : ℝ)))]
  unfold oneSiteMaxHodgeEnvelope
  nlinarith

/-- All constants are fixed by the named Nguyen input and the spectral
parameter; none depends on the ring length. -/
def rademacherTransferLogConstant (I : NguyenBottomSingularInput) (z : ℂ) : ℝ :=
  2 * (oneSiteTensorLogConstant z +
    max 0 (nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I)))

theorem rademacherTransferLogConstant_nonneg (I : NguyenBottomSingularInput) (z : ℂ) :
    0 ≤ rademacherTransferLogConstant I z := by
  exact mul_nonneg (by norm_num)
    (add_nonneg (oneSiteTensorLogConstant_nonneg z) (le_max_left _ _))

/-- Summing site envelopes gives the source's bound with scalar interval
length L=sW. -/
theorem rademacherIntervalMaxHodgeEnvelope_le_of_good
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W s)
    (hx : x ∉ rademacherInterfaceBadEvent I W s)
    (hbound : ∀ i a, |x i a| ≤ 1) :
    intervalMaxHodgeEnvelope W s z x ≤
      rademacherTransferLogConstant I z * ((s * W : ℕ) : ℝ) *
        (1 + Real.posLog (W : ℝ)) := by
  have hWpos := (interfaceCanonicalLargeWConditions I hW).1
  let D := max 0 (nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I))
  have hD : 0 ≤ D := le_max_left _ _
  have hsite (j : Fin s) :
      oneSiteMaxHodgeEnvelope W z (intervalSiteRestriction W s x j) ≤
        rademacherTransferLogConstant I z * W * (1 + Real.posLog (W : ℝ)) := by
    have hb := (rademacherInterface_controls I hI W s hW x hx j 0).2.1
    have hc := (rademacherInterface_controls I hI W s hW x hx j 2).2.1
    rw [normalized_rademacherIntervalSquare_B W s j x z] at hb
    rw [normalized_rademacherIntervalSquare_C W s j x z] at hc
    have hexp : Real.exp (-D * (W : ℝ)) ≤
        Real.exp (-nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I) * (W : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hle : nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I) ≤ D :=
        le_max_right _ _
      nlinarith [mul_nonneg (sub_nonneg.mpr hle) (Nat.cast_nonneg W : 0 ≤ (W : ℝ))]
    apply oneSiteMaxHodgeEnvelope_le_of_bounded_atoms W hWpos z
      (intervalSiteRestriction W s x j) (fun i a => hbound _ _) D hD
    · simpa only [oneSiteBDet, intervalSiteBlocks_restriction] using hexp.trans hb
    · simpa only [oneSiteCDet, intervalSiteBlocks_restriction] using hexp.trans hc
  unfold intervalMaxHodgeEnvelope
  calc
    ∑ j : Fin s, oneSiteMaxHodgeEnvelope W z (intervalSiteRestriction W s x j) ≤
        ∑ _j : Fin s, rademacherTransferLogConstant I z * W *
          (1 + Real.posLog (W : ℝ)) := Finset.sum_le_sum fun j _ => hsite j
    _ = rademacherTransferLogConstant I z * ((s * W : ℕ) : ℝ) *
        (1 + Real.posLog (W : ℝ)) := by simp; ring

/-- Deterministic Hodge bound for every nonempty chronological product,
including its inverse, on the actual good event. -/
theorem rademacherInterval_hodgeLoss_le_of_good
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W) (hs : 0 < s)
    (z : ℂ) (x : IntervalRows W s)
    (hx : x ∉ rademacherInterfaceBadEvent I W s)
    (hbound : ∀ i a, |x i a| ≤ 1) (r : Fin (2 * W + 1)) :
    matrixHodgeLoss (intervalClearedProduct W s z x r) ≤
      rademacherTransferLogConstant I z * ((s * W : ℕ) : ℝ) *
        (1 + Real.posLog (W : ℝ)) := by
  have hdet := rademacherInterface_dets_isUnit_of_good I hI W s hW x hx z
  exact (intervalClearedProduct_hodgeLoss_le_maxEnvelope W s hs z x
    (fun j => (hdet j).1) (fun j => (hdet j).2) r).trans
      (rademacherIntervalMaxHodgeEnvelope_le_of_good I hI W s hW z x hx hbound)

open scoped Matrix.Norms.L2Operator in
/-- Source formula `eq:gb-product-control`, with the harmless log(eW)
convention, for the actual
operator norm used by pressure. -/
theorem rademacherInterval_abs_logNorm_le_of_good
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W) (hs : 0 < s)
    (z : ℂ) (x : IntervalRows W s)
    (hx : x ∉ rademacherInterfaceBadEvent I W s)
    (hbound : ∀ i a, |x i a| ≤ 1) (r : Fin (2 * W + 1)) :
    |Real.log ‖intervalClearedProduct W s z x r‖| ≤
      rademacherTransferLogConstant I z * ((s * W : ℕ) : ℝ) *
        (1 + Real.posLog (W : ℝ)) := by
  letI : Nonempty (powersetCard (Fin W ⊕ Fin W) r.1) := by
    rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
    apply Nat.choose_pos
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hdet := rademacherInterface_dets_isUnit_of_good I hI W s hW x hx z
  have hu := intervalClearedProduct_det_isUnit W s z x
    (fun j => (hdet j).1) (fun j => (hdet j).2) r
  have h := abs_matrix_logNorm_mul_sub_le_hodgeLoss
    (intervalClearedProduct W s z x r) 1 hu one_ne_zero
  simp only [Matrix.mul_one, norm_one, Real.log_one, sub_zero] at h
  exact h.trans (rademacherInterval_hodgeLoss_le_of_good I hI W s hW hs z x hx hbound r)

open scoped Matrix.Norms.L2Operator in
/-- Atom boundedness is discharged from the Rademacher law in this
probabilistic caller, leaving only the explicitly constructed good event. -/
theorem rademacherInterval_abs_logNorm_le_ae_on_good
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W) (hs : 0 < s)
    (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W s rademacherLaw,
      x ∉ rademacherInterfaceBadEvent I W s →
      ∀ r : Fin (2 * W + 1), |Real.log ‖intervalClearedProduct W s z x r‖| ≤
        rademacherTransferLogConstant I z * ((s * W : ℕ) : ℝ) *
          (1 + Real.posLog (W : ℝ)) := by
  filter_upwards [rademacherRows_ae_sign W s] with x hx hgood r
  apply rademacherInterval_abs_logNorm_le_of_good I hI W s hW hs z x hgood
  intro i a
  rcases hx i a with h | h <;> rw [h] <;> norm_num

open scoped Matrix.Norms.L2Operator in
/-- Every exterior degree is nonzero on the concrete interface good event.
The degree-zero and top-degree cases are included. -/
theorem rademacherInterval_norm_pos_of_good
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W s)
    (hx : x ∈ rademacherInterfaceGoodEvent I W s) (r : Fin (2 * W + 1)) :
    0 < ‖intervalClearedProduct W s z x r‖ := by
  letI : Nonempty (powersetCard (Fin W ⊕ Fin W) r.1) := by
    rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
    apply Nat.choose_pos
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hdet := rademacherInterface_dets_isUnit_of_good I hI W s hW x hx.2 z
  have hu := intervalClearedProduct_det_isUnit W s z x
    (fun j => (hdet j).1) (fun j => (hdet j).2) r
  apply norm_pos_iff.mpr
  intro hzero
  exact hu.ne_zero (by rw [hzero, Matrix.det_zero])

/-- The three-site packet cap is a fixed constant times W log(eW).
All boundedness and determinant premises come from the measurable physical
good event. -/
theorem rademacherPacket_hodgeLoss_le_of_good
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W 3)
    (hx : x ∈ rademacherInterfaceGoodEvent I W 3) (r : Fin (2 * W + 1)) :
    matrixHodgeLoss (intervalClearedProduct W 3 z x r) ≤
      (3 * rademacherTransferLogConstant I z) * W * Real.log (Real.exp 1 * W) := by
  have hbound : ∀ i a, |x i a| ≤ 1 := by
    intro i a
    rcases hx.1 i a with h | h <;> rw [h] <;> norm_num
  have h := rademacherInterval_hodgeLoss_le_of_good I hI W 3 hW (by omega)
    z x hx.2 hbound r
  rw [one_add_posLog_nat_eq_log_e_mul W (interfaceCanonicalLargeWConditions I hW).1] at h
  convert h using 1 <;> push_cast <;> ring

open scoped Matrix.Norms.L2Operator in
/-- The ordinary operator logarithm bound includes an empty interval,
whose product is exactly the identity. -/
theorem rademacherInterval_abs_logNorm_le_on_measurable_good
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W s)
    (hx : x ∈ rademacherInterfaceGoodEvent I W s) (r : Fin (2 * W + 1)) :
    |Real.log ‖intervalClearedProduct W s z x r‖| ≤
      rademacherTransferLogConstant I z * ((s * W : ℕ) : ℝ) *
        (1 + Real.posLog (W : ℝ)) := by
  by_cases hs : s = 0
  · subst s
    letI : Nonempty (powersetCard (Fin W ⊕ Fin W) r.1) := by
      rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
      apply Nat.choose_pos
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    simp [intervalClearedProduct, reverseMatrixProduct]
  · have hbound : ∀ i a, |x i a| ≤ 1 := by
      intro i a
      rcases hx.1 i a with h | h <;> rw [h] <;> norm_num
    exact rademacherInterval_abs_logNorm_le_of_good I hI W s hW
      (Nat.pos_of_ne_zero hs) z x hx.2 hbound r

open scoped Matrix.Norms.L2Operator in
/-- The support-restricted good event discharges atom boundedness pointwise,
so its actual transfer logarithm agrees with the bounded observable. -/
theorem rademacherInterval_clippedLog_eq_log_of_good
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W s)
    (hx : x ∈ rademacherInterfaceGoodEvent I W s) (r : Fin (2 * W + 1)) :
    clippedLog
      (rademacherTransferLogConstant I z * ((s * W : ℕ) : ℝ) *
        (1 + Real.posLog (W : ℝ)))
      ‖intervalClearedProduct W s z x r‖ =
        Real.log ‖intervalClearedProduct W s z x r‖ := by
  have hlog := abs_le.mp
    (rademacherInterval_abs_logNorm_le_on_measurable_good I hI W s hW z x hx r)
  exact clippedLog_eq_log_of_log_bounds
    (rademacherInterval_norm_pos_of_good I hI W s hW z x hx r) hlog.1 hlog.2

end BernoulliSection8
