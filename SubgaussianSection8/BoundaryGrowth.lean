import SubgaussianSection8.BlockEntryControl
import SubgaussianSection8.Inputs
import BernoulliSection8.BoundaryGrowthCore
import BernoulliSection10.PacketComparisonGrowth
import SubgaussianSection8.BoundarySmallBall
import SubgaussianSection8.EndpointInterface
import BernoulliSection9.ArbitraryFrameQuantitative

/-! # W log(eW) boundary comparison on the Nguyen endpoint event

The raw shift is `sqrt(3W) z`. Its exact translation logarithm and the
common row scale are estimated before applying the width bound, so the
result contains only one logarithm of the width.
-/

open scoped BigOperators Matrix

noncomputable section

namespace SubgaussianSection8
open BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra Matrix Set

local instance rademacherBoundaryGrowthSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W => (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h => toLex.injective h)

theorem subgaussianOpNormBound_one_le (Ξ : Atom) : (1 : ℝ) ≤ opNormConstant Ξ :=
  opNormConstant_one_le Ξ

theorem packetRowScale_norm_bounds (Ξ : Atom) (W : ℕ) (hW : 0 < W) :
    1 ≤ ‖packetRowScale W‖ ∧ ‖packetRowScale W‖ ≤ 3 * W := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (Nat.succ_le_of_lt hW)
  have hp := Real.sqrt_nonneg (3 * (W : ℝ))
  simp only [packetRowScale, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hp]
  exact ⟨Real.one_le_sqrt.mpr (by linarith), Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))⟩

open scoped Matrix.Norms.L2Operator in
theorem subgaussianScaledEndpointGood (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) (hW : 0 < W)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hgood : PaperEndpointGood CL BR (opNormConstant Ξ)
      (interfaceDeterminantLowerBound I W)) :
    PaperEndpointGood ((packetRowScale W) • CL) ((packetRowScale W) • BR)
      (3 * W * (opNormConstant Ξ)) (interfaceDeterminantLowerBound I W) := by
  have hK := opNormConstant_nonneg Ξ
  have hs := (packetRowScale_norm_bounds Ξ) W hW
  have hscale : 1 ≤ ‖packetRowScale W‖ ^ W := one_le_pow₀ hs.1
  refine ⟨?_, ?_, hgood.delta_pos, ?_, ?_⟩
  · rw [norm_smul]
    exact mul_le_mul hs.2 hgood.norm_CL_le (norm_nonneg CL) (by positivity)
  · rw [norm_smul]
    exact mul_le_mul hs.2 hgood.norm_BR_le (norm_nonneg BR) (by positivity)
  · rw [Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow]
    exact hgood.delta_le_norm_det_CL.trans
      (by nlinarith [mul_le_mul_of_nonneg_right hscale (norm_nonneg CL.det)])
  · rw [Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow]
    exact hgood.delta_le_norm_det_BR.trans
      (by nlinarith [mul_le_mul_of_nonneg_right hscale (norm_nonneg BR.det)])

open scoped Matrix.Norms.Frobenius

def subgaussianEndpointLogConstant (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) : ℝ :=
  Real.log 7 + 1 + (2 * Real.log (24 * (opNormConstant Ξ)) + 6) +
    2 * max 0 (nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I))

theorem subgaussianEndpointLogConstant_nonneg (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) :
    0 ≤ (subgaussianEndpointLogConstant Ξ) I := by
  have hlog : 0 ≤ Real.log (24 * (opNormConstant Ξ)) :=
    Real.log_nonneg (by nlinarith [(subgaussianOpNormBound_one_le Ξ)])
  unfold subgaussianEndpointLogConstant
  positivity

theorem log_scaled_endpointExteriorConstant_le (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) (hW : 0 < W)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hgood : PaperEndpointGood CL BR (opNormConstant Ξ)
      (interfaceDeterminantLowerBound I W)) :
    Real.log (endpointExteriorConstant ((packetRowScale W) • CL)
        ((packetRowScale W) • BR)) ≤
      (subgaussianEndpointLogConstant Ξ) I * W * Real.log (Real.exp 1 * W) := by
  let D := max 0 (nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I))
  let B := opNormConstant Ξ
  let F := (24 * B * (W : ℝ) ^ 3) ^ (2 * W)
  have hD : 0 ≤ D := le_max_left _ _
  have hB : 1 ≤ B := (subgaussianOpNormBound_one_le Ξ)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (Nat.succ_le_of_lt hW)
  have hcube : 1 ≤ (W : ℝ) ^ 3 := one_le_pow₀ hW1
  have hbase : 1 ≤ 24 * B * (W : ℝ) ^ 3 := by
    nlinarith [mul_le_mul hB hcube (by norm_num) (by linarith : 0 ≤ B)]
  have hF : 1 ≤ F := one_le_pow₀ hbase
  have hs := (subgaussianScaledEndpointGood Ξ) I W hW CL BR hgood
  have hcrude : endpointCompoundCrudeBound W (3 * W * B) = F := by
    have heq : endpointOperatorCrudeBound W (3 * W * B) =
        12 * B * (W : ℝ) ^ 3 := by
      unfold endpointOperatorCrudeBound
      push_cast
      ring
    have hlarge : 1 ≤ endpointOperatorCrudeBound W (3 * W * B) := by
      rw [heq]
      nlinarith [mul_le_mul hB hcube (by norm_num) (by linarith : 0 ≤ B)]
    unfold endpointCompoundCrudeBound
    rw [max_eq_right hlarge, heq]
    dsimp [F]
    congr 1
    ring
  have hforward (q : ℕ) :
      ‖compound q (endpointFactor ((packetRowScale W) • CL)
        ((packetRowScale W) • BR))‖ ≤ F := by
    rw [← hcrude]
    exact endpointFactor_compound_norm_le_endpointCompoundCrudeBound _ _ _
      hs.endpointOperatorGood q
  have hdet : ‖(endpointFactor ((packetRowScale W) • CL)
      ((packetRowScale W) • BR)).det‖⁻¹ ≤ Real.exp (2 * D * W) := by
    refine hs.endpointFactor_det_inv_norm_le.trans ?_
    unfold interfaceDeterminantLowerBound
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hle : nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I) ≤ D :=
      le_max_right _ _
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (Nat.cast_nonneg W : 0 ≤ (W : ℝ))]
  have hE : IsUnit (endpointFactor ((packetRowScale W) • CL)
      ((packetRowScale W) • BR)).det := by
    rw [endpointFactor_det]
    exact hs.CL_det_isUnit.mul hs.BR_det_isUnit
  have hlog := log_exactExteriorConditioningConstant_le_of_forward_bound W _ hE
    F (2 * D * W) hF (by positivity) hdet hforward
  have hcount := log_endpoint_count_le_log_e_scale W hW
  have hflog := log_endpoint_forward_crude_le W hW B hB
  have hscale : 1 ≤ Real.log (Real.exp 1 * W) := by
    rw [← one_add_posLog_nat_eq_log_e_mul W hW]
    exact le_add_of_nonneg_right Real.posLog_nonneg
  have hcountW : (Real.log 7 + 1) * Real.log (Real.exp 1 * W) ≤
      (Real.log 7 + 1) * W * Real.log (Real.exp 1 * W) := by
    have hnonneg : 0 ≤ (Real.log 7 + 1) * Real.log (Real.exp 1 * W) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hW1 hnonneg]
  have hDW : 2 * D * (W : ℝ) ≤
      2 * D * W * Real.log (Real.exp 1 * W) := by
    nlinarith [mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ 2 * D * (W : ℝ) by positivity)]
  change Real.log (exactExteriorConditioningConstant _) ≤ _
  dsimp only [subgaussianEndpointLogConstant, F, B, D] at *
  nlinarith

def subgaussianBoundaryLogConstant (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) (z : ℂ) : ℝ :=
  3 * (Real.log 3 + 1) + packetZeroLogConstant +
    3 * (Real.log (1 + 3 * ‖z‖) + 1) + (subgaussianEndpointLogConstant Ξ) I

theorem subgaussianBoundaryLogConstant_nonneg (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) (z : ℂ) :
    0 ≤ (subgaussianBoundaryLogConstant Ξ) I z := by
  have hz : 0 ≤ Real.log (1 + 3 * ‖z‖) :=
    Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have he := (subgaussianEndpointLogConstant_nonneg Ξ) I
  have hp := packetZeroLogConstant_nonneg
  unfold subgaussianBoundaryLogConstant
  positivity

/-- Exact common-scale identity; this is the logarithmic row-normalization
cost and does not use an asymptotic estimate. -/
theorem neg_log_subgaussianBoundaryInverseGamma_eq (Ξ : Atom)
    (W : ℕ) (hW : 0 < W) (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ) :
    -Real.log ((subgaussianBoundaryInverseGamma Ξ) W z CL BR) =
      (3 * W : ℝ) * Real.log ‖packetRowScale W‖ +
        Real.log (packetEndpointComparisonConstant (packetRowScale W * z)
          ((packetRowScale W) • CL) ((packetRowScale W) • BR)) := by
  have hs := packetRowScale_ne_zero W hW
  have hk := packetEndpointComparisonConstant_pos (packetRowScale W * z)
    ((packetRowScale W) • CL) ((packetRowScale W) • BR)
  unfold subgaussianBoundaryInverseGamma
  rw [Real.log_mul (norm_ne_zero_iff.mpr (pow_ne_zero _ (inv_ne_zero hs)))
    (inv_ne_zero hk.ne'), Real.log_inv, norm_pow, norm_inv, Real.log_pow, Real.log_inv]
  push_cast <;> ring

theorem neg_log_subgaussianBoundaryInverseGamma_le (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hgood : PaperEndpointGood CL BR (opNormConstant Ξ)
      (interfaceDeterminantLowerBound I W)) :
    -Real.log ((subgaussianBoundaryInverseGamma Ξ) W z CL BR) ≤
      (subgaussianBoundaryLogConstant Ξ) I z * W * Real.log (Real.exp 1 * W) := by
  have hs := (packetRowScale_norm_bounds Ξ) W hW
  have hrow := log_rowScale_le_log_e_scale W hW ‖packetRowScale W‖
    (zero_lt_one.trans_le hs.1) hs.2
  have hshift := log_scaled_shift_le_log_e_scale W hW ‖packetRowScale W‖
    (norm_nonneg _) hs.2 z
  have hzero := log_threeBlockZeroComparisonConstant_fin_le_W_log_eW W hW
  have he := (log_scaled_endpointExteriorConstant_le Ξ) I W hW CL BR hgood
  have hzpos := zero_lt_one.trans_le (threeBlockZeroComparisonConstant_one_le (w := Fin W))
  have htpos := zero_lt_one.trans_le
    (threeBlockTranslationFactor_one_le (w := Fin W) (packetRowScale W * z))
  have hepos : 0 < endpointExteriorConstant ((packetRowScale W) • CL)
      ((packetRowScale W) • BR) :=
    zero_lt_one.trans_le (one_le_exactExteriorConditioningConstant _)
  have hcard : Fintype.card (ThreeBlockIndex (Fin W)) = 3 * W := by
    simp [ThreeBlockIndex, ThreeBlockOuter]
    omega
  rw [(neg_log_subgaussianBoundaryInverseGamma_eq Ξ) W hW]
  unfold packetEndpointComparisonConstant threeBlockConcreteComparisonConstant
  rw [Real.log_mul (mul_pos hzpos htpos).ne' hepos.ne',
    Real.log_mul hzpos.ne' htpos.ne', log_threeBlockTranslationFactor_eq, hcard, norm_mul]
  have hrowW := mul_le_mul_of_nonneg_left hrow (show 0 ≤ (3 * W : ℝ) by positivity)
  have hshiftW := mul_le_mul_of_nonneg_left hshift (show 0 ≤ (3 * W : ℝ) by positivity)
  unfold subgaussianBoundaryLogConstant
  push_cast
  nlinarith

theorem neg_log_subgaussianBoundaryInverseGamma_le_on_endpoint_good (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) (hW : 0 < W) (z : ℂ)
    (ep : EndpointBlockPair W) (hep : ep ∈ (subgaussianEndpointGoodEvent Ξ) I W) :
    -Real.log ((subgaussianBoundaryInverseGamma Ξ) W z
      (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)) ≤
      (subgaussianBoundaryLogConstant Ξ) I z * W * Real.log (Real.exp 1 * W) :=
  (neg_log_subgaussianBoundaryInverseGamma_le Ξ) I W hW z _ _
    ((subgaussianEndpointGoodEvent_spec Ξ) I W ep hep)

/-- Both sides of the actual normalized coefficient-to-Gram comparison.
The raw comparison is transported through the same exact common scale
as the terminal polynomial; its logarithm has nonpositive sign. -/
theorem subgaussianPacketBoundaryCoefficient_log_gramVolume_le (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hgood : PaperEndpointGood CL BR (opNormConstant Ξ)
      (interfaceDeterminantLowerBound I W))
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hTheta : IsUnit Theta.det) :
    |Real.log (rademacherPacketBoundaryCoefficient W z CL BR Theta) -
      Real.log (gramVolume Theta)| ≤
      (subgaussianBoundaryLogConstant Ξ) I z * W * Real.log (Real.exp 1 * W) := by
  have hsigma := packetRowScale_ne_zero W hW
  have hs := (subgaussianScaledEndpointGood Ξ) I W hW CL BR hgood
  have hraw := packetCoefficient_log_gramVolume_pathwise (packetRowScale W * z)
    ((packetRowScale W) • CL) ((packetRowScale W) • BR)
    hs.CL_det_isUnit hs.BR_det_isUnit Theta hTheta
  have hrawpos := globalBoundaryCoefficientNorm_pos_fullyInstantiated (packetRowScale W * z)
    ((packetRowScale W) • CL) ((packetRowScale W) • BR)
    hs.CL_det_isUnit hs.BR_det_isUnit Theta hTheta
  have hscalepos : 0 < ‖(packetRowScale W)⁻¹ ^ (3 * W)‖ :=
    norm_pos_iff.mpr (pow_ne_zero _ (inv_ne_zero hsigma))
  have habsScale : |Real.log ‖(packetRowScale W)⁻¹ ^ (3 * W)‖| =
      (3 * W : ℝ) * Real.log ‖packetRowScale W‖ := by
    have hlogsigma := Real.log_nonneg ((packetRowScale_norm_bounds Ξ) W hW).1
    rw [norm_pow, norm_inv, Real.log_pow, Real.log_inv, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg _), abs_neg, abs_of_nonneg hlogsigma]
    push_cast <;> rfl
  rw [rademacherPacketBoundaryCoefficient,
    normalizedPacketBoundaryCoefficient_eq_scaled _ hsigma,
    Fintype.card_fin, Real.log_mul hscalepos.ne' hrawpos.ne']
  calc
    |Real.log ‖(packetRowScale W)⁻¹ ^ (3 * W)‖ +
        Real.log (packetBoundaryCoefficientNorm (packetRowScale W * z)
          ((packetRowScale W) • CL) ((packetRowScale W) • BR) Theta) -
        Real.log (gramVolume Theta)| ≤
      |Real.log ‖(packetRowScale W)⁻¹ ^ (3 * W)‖| +
        |Real.log (packetBoundaryCoefficientNorm (packetRowScale W * z)
          ((packetRowScale W) • CL) ((packetRowScale W) • BR) Theta) -
          Real.log (gramVolume Theta)| := by
      simpa only [add_sub_assoc] using abs_add_le
        (Real.log ‖(packetRowScale W)⁻¹ ^ (3 * W)‖)
        (Real.log (packetBoundaryCoefficientNorm (packetRowScale W * z)
          ((packetRowScale W) • CL) ((packetRowScale W) • BR) Theta) -
          Real.log (gramVolume Theta))
    _ ≤ (3 * W : ℝ) * Real.log ‖packetRowScale W‖ +
        Real.log (packetEndpointComparisonConstant (packetRowScale W * z)
          ((packetRowScale W) • CL) ((packetRowScale W) • BR)) :=
      add_le_add (le_of_eq habsScale) hraw
    _ = -Real.log ((subgaussianBoundaryInverseGamma Ξ) W z CL BR) :=
      ((neg_log_subgaussianBoundaryInverseGamma_eq Ξ) W hW z CL BR).symm
    _ ≤ _ := (neg_log_subgaussianBoundaryInverseGamma_le Ξ) I W hW z CL BR hgood

theorem subgaussianPacketBoundaryCoefficient_log_gramVolume_le_on_endpoint_good (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) (hW : 0 < W) (z : ℂ)
    (ep : EndpointBlockPair W) (hep : ep ∈ (subgaussianEndpointGoodEvent Ξ) I W)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) (hTheta : IsUnit Theta.det) :
    |Real.log (rademacherPacketBoundaryCoefficient W z
      (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2) Theta) -
      Real.log (gramVolume Theta)| ≤
      (subgaussianBoundaryLogConstant Ξ) I z * W * Real.log (Real.exp 1 * W) :=
  (subgaussianPacketBoundaryCoefficient_log_gramVolume_le Ξ) I W hW z _ _
    ((subgaussianEndpointGoodEvent_spec Ξ) I W ep hep) Theta hTheta

end SubgaussianSection8
