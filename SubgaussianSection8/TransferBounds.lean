import SubgaussianSection8.TransferGrowth
import BernoulliSection8.WidthLog

/-! General subgaussian transfer logarithm bounds on the actual measurable interface event. -/
open Filter MeasureTheory Set Topology
open scoped BigOperators Matrix Matrix.Norms.Frobenius
noncomputable section
namespace SubgaussianSection8
open BernoulliSection8 BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra Set.powersetCard

local instance transferBoundsSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W => (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h => toLex.injective h)

/-- All constants are fixed by the named Nguyen input and the spectral
parameter; none depends on the ring length. -/
def subgaussianTransferLogConstant (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) (z : ℂ) : ℝ :=
  2 * (oneSiteTensorLogConstant (growthParameter Ξ z) +
    max 0 (nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I)))

theorem subgaussianTransferLogConstant_nonneg (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) (z : ℂ) :
    0 ≤ (subgaussianTransferLogConstant Ξ) I z := by
  exact mul_nonneg (by norm_num)
    (add_nonneg (oneSiteTensorLogConstant_nonneg (growthParameter Ξ z)) (le_max_left _ _))

/-- Summing site envelopes gives the source's bound with scalar interval
length L=sW. -/
theorem subgaussianIntervalMaxHodgeEnvelope_le_of_good (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : Ξ.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W s)
    (hx : x ∉ (subgaussianInterfaceBadEvent Ξ) I W s) :
    intervalMaxHodgeEnvelope W s z x ≤
      (subgaussianTransferLogConstant Ξ) I z * ((s * W : ℕ) : ℝ) *
        (1 + Real.posLog (W : ℝ)) := by
  have hWpos := (interfaceCanonicalLargeWConditions I hW).1
  let D := max 0 (nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I))
  have hD : 0 ≤ D := le_max_left _ _
  have hsite (j : Fin s) :
      oneSiteMaxHodgeEnvelope W z (intervalSiteRestriction W s x j) ≤
        (subgaussianTransferLogConstant Ξ) I z * W * (1 + Real.posLog (W : ℝ)) := by
    have hb := ((subgaussianInterface_controls Ξ) I hI W s hW x hx j 0).2.1
    have hc := ((subgaussianInterface_controls Ξ) I hI W s hW x hx j 2).2.1
    rw [(normalized_subgaussianIntervalSquare_B Ξ) W s j x z] at hb
    rw [(normalized_subgaussianIntervalSquare_C Ξ) W s j x z] at hc
    have hexp : Real.exp (-D * (W : ℝ)) ≤
        Real.exp (-nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I) * (W : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hle : nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I) ≤ D :=
        le_max_right _ _
      nlinarith [mul_nonneg (sub_nonneg.mpr hle) (Nat.cast_nonneg W : 0 ≤ (W : ℝ))]
    have hh := site_step_entry_bounds_of_good Ξ I hI W s hW z x hx j
    apply oneSiteMaxHodgeEnvelope_le_of_bounded_blocks W hWpos z
      (intervalSiteRestriction W s x j) (growthParameter Ξ z)
      (by simpa only [intervalSiteBlocks_restriction] using hh.1)
      (by simpa only [intervalSiteBlocks_restriction] using hh.2) D hD
    · simpa only [oneSiteBDet, intervalSiteBlocks_restriction] using hexp.trans hb
    · simpa only [oneSiteCDet, intervalSiteBlocks_restriction] using hexp.trans hc
  unfold intervalMaxHodgeEnvelope
  calc
    ∑ j : Fin s, oneSiteMaxHodgeEnvelope W z (intervalSiteRestriction W s x j) ≤
        ∑ _j : Fin s, (subgaussianTransferLogConstant Ξ) I z * W *
          (1 + Real.posLog (W : ℝ)) := Finset.sum_le_sum fun j _ => hsite j
    _ = (subgaussianTransferLogConstant Ξ) I z * ((s * W : ℕ) : ℝ) *
        (1 + Real.posLog (W : ℝ)) := by simp; ring

/-- Deterministic Hodge bound for every nonempty chronological product,
including its inverse, on the actual good event. -/
theorem subgaussianInterval_hodgeLoss_le_of_good (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : Ξ.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W) (hs : 0 < s)
    (z : ℂ) (x : IntervalRows W s)
    (hx : x ∉ (subgaussianInterfaceBadEvent Ξ) I W s)
    (r : Fin (2 * W + 1)) :
    matrixHodgeLoss (intervalClearedProduct W s z x r) ≤
      (subgaussianTransferLogConstant Ξ) I z * ((s * W : ℕ) : ℝ) *
        (1 + Real.posLog (W : ℝ)) := by
  have hdet := (subgaussianInterface_dets_isUnit_of_good Ξ) I hI W s hW x hx z
  exact (intervalClearedProduct_hodgeLoss_le_maxEnvelope W s hs z x
    (fun j => (hdet j).1) (fun j => (hdet j).2) r).trans
      ((subgaussianIntervalMaxHodgeEnvelope_le_of_good Ξ) I hI W s hW z x hx)

open scoped Matrix.Norms.L2Operator in
/-- Source formula `eq:gb-product-control`, with the harmless log(eW)
convention, for the actual
operator norm used by pressure. -/
theorem subgaussianInterval_abs_logNorm_le_of_good (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : Ξ.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W) (hs : 0 < s)
    (z : ℂ) (x : IntervalRows W s)
    (hx : x ∉ (subgaussianInterfaceBadEvent Ξ) I W s)
    (r : Fin (2 * W + 1)) :
    |Real.log ‖intervalClearedProduct W s z x r‖| ≤
      (subgaussianTransferLogConstant Ξ) I z * ((s * W : ℕ) : ℝ) *
        (1 + Real.posLog (W : ℝ)) := by
  letI : Nonempty (powersetCard (Fin W ⊕ Fin W) r.1) := by
    rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
    apply Nat.choose_pos
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hdet := (subgaussianInterface_dets_isUnit_of_good Ξ) I hI W s hW x hx z
  have hu := intervalClearedProduct_det_isUnit W s z x
    (fun j => (hdet j).1) (fun j => (hdet j).2) r
  have h := abs_matrix_logNorm_mul_sub_le_hodgeLoss
    (intervalClearedProduct W s z x r) 1 hu one_ne_zero
  simp only [Matrix.mul_one, norm_one, Real.log_one, sub_zero] at h
  exact h.trans ((subgaussianInterval_hodgeLoss_le_of_good Ξ) I hI W s hW hs z x hx r)

open scoped Matrix.Norms.L2Operator in
/-- Atom boundedness is discharged from the subgaussian law in this
probabilistic caller, leaving only the explicitly constructed good event. -/
theorem subgaussianInterval_abs_logNorm_le_ae_on_good (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : Ξ.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W) (hs : 0 < s)
    (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W s Ξ.law,
      x ∉ (subgaussianInterfaceBadEvent Ξ) I W s →
      ∀ r : Fin (2 * W + 1), |Real.log ‖intervalClearedProduct W s z x r‖| ≤
        (subgaussianTransferLogConstant Ξ) I z * ((s * W : ℕ) : ℝ) *
          (1 + Real.posLog (W : ℝ)) := by
  exact ae_of_all _ fun x hx r =>
    subgaussianInterval_abs_logNorm_le_of_good Ξ I hI W s hW hs z x hx r

open scoped Matrix.Norms.L2Operator in
/-- Every exterior degree is nonzero on the concrete interface good event.
The degree-zero and top-degree cases are included. -/
theorem subgaussianInterval_norm_pos_of_good (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : Ξ.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W s)
    (hx : x ∈ (subgaussianInterfaceGoodEvent Ξ) I W s) (r : Fin (2 * W + 1)) :
    0 < ‖intervalClearedProduct W s z x r‖ := by
  letI : Nonempty (powersetCard (Fin W ⊕ Fin W) r.1) := by
    rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
    apply Nat.choose_pos
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hdet := (subgaussianInterface_dets_isUnit_of_good Ξ) I hI W s hW x hx z
  have hu := intervalClearedProduct_det_isUnit W s z x
    (fun j => (hdet j).1) (fun j => (hdet j).2) r
  apply norm_pos_iff.mpr
  intro hzero
  exact hu.ne_zero (by rw [hzero, Matrix.det_zero])

/-- The three-site packet cap is a fixed constant times W log(eW).
All boundedness and determinant premises come from the measurable physical
good event. -/
theorem subgaussianPacket_hodgeLoss_le_of_good (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : Ξ.parameter ≤ I.subgaussianBound)
    (W : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W 3)
    (hx : x ∈ (subgaussianInterfaceGoodEvent Ξ) I W 3) (r : Fin (2 * W + 1)) :
    matrixHodgeLoss (intervalClearedProduct W 3 z x r) ≤
      (3 * (subgaussianTransferLogConstant Ξ) I z) * W * Real.log (Real.exp 1 * W) := by
  have h := (subgaussianInterval_hodgeLoss_le_of_good Ξ) I hI W 3 hW (by omega)
    z x hx r
  rw [one_add_posLog_nat_eq_log_e_mul W (interfaceCanonicalLargeWConditions I hW).1] at h
  convert h using 1 <;> push_cast <;> ring

open scoped Matrix.Norms.L2Operator in
/-- The ordinary operator logarithm bound includes an empty interval,
whose product is exactly the identity. -/
theorem subgaussianInterval_abs_logNorm_le_on_measurable_good (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : Ξ.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W s)
    (hx : x ∈ (subgaussianInterfaceGoodEvent Ξ) I W s) (r : Fin (2 * W + 1)) :
    |Real.log ‖intervalClearedProduct W s z x r‖| ≤
      (subgaussianTransferLogConstant Ξ) I z * ((s * W : ℕ) : ℝ) *
        (1 + Real.posLog (W : ℝ)) := by
  by_cases hs : s = 0
  · subst s
    letI : Nonempty (powersetCard (Fin W ⊕ Fin W) r.1) := by
      rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
      apply Nat.choose_pos
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    simp [intervalClearedProduct, reverseMatrixProduct]
  · exact (subgaussianInterval_abs_logNorm_le_of_good Ξ) I hI W s hW
      (Nat.pos_of_ne_zero hs) z x hx r

open scoped Matrix.Norms.L2Operator in
/-- The measurable interface event discharges atom boundedness pointwise,
so its actual transfer logarithm agrees with the bounded observable. -/
theorem subgaussianInterval_clippedLog_eq_log_of_good (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : Ξ.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W s)
    (hx : x ∈ (subgaussianInterfaceGoodEvent Ξ) I W s) (r : Fin (2 * W + 1)) :
    clippedLog
      ((subgaussianTransferLogConstant Ξ) I z * ((s * W : ℕ) : ℝ) *
        (1 + Real.posLog (W : ℝ)))
      ‖intervalClearedProduct W s z x r‖ =
        Real.log ‖intervalClearedProduct W s z x r‖ := by
  have hlog := abs_le.mp
    ((subgaussianInterval_abs_logNorm_le_on_measurable_good Ξ) I hI W s hW z x hx r)
  exact clippedLog_eq_log_of_log_bounds
    ((subgaussianInterval_norm_pos_of_good Ξ) I hI W s hW z x hx r) hlog.1 hlog.2


end SubgaussianSection8
