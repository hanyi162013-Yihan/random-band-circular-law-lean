import BernoulliSection10.SquarefreeRademacher
import BernoulliSection10Complex.EndpointDeterminant
import BernoulliSection10Complex.PacketComparisonGrowth

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open Matrix MvPolynomial BernoulliLinearAlgebra

set_option maxHeartbeats 800000

/-- Deterministic cost for passing from raw scalar squarefree coefficients
to the canonical tensor grouped into normalized physical packet rows. -/
def packetTensorEvaluationFactor (W : ℕ) : ℝ :=
  (1 + (PacketAtomRowCount W : ℝ) * (blockNormalization W)⁻¹) ^
    PacketAtomRowCount W

theorem packetAtomRowsOfRealAssignment_abs_le
    (W : ℕ) (hW : 0 < W)
    (a : ThreeBlockVariable (Fin W) → ℝ)
    (ha : ∀ e, a e = 1 ∨ a e = -1) :
    ∀ i j, ‖packetAtomRowsOfRealAssignment W a i j‖ ≤
      (blockNormalization W)⁻¹ := by
  intro i j
  unfold packetAtomRowsOfRealAssignment
  split_ifs with h
  · have habs : |a ⟨((packetIndexEquiv W).symm i,
        (packetIndexEquiv W).symm j), h⟩| = 1 := by
      rcases ha ⟨((packetIndexEquiv W).symm i,
        (packetIndexEquiv W).symm j), h⟩ with he | he <;> simp [he]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs]
    rw [habs, abs_of_pos (blockNormalization_pos W hW)]
    simp
  · simp only [norm_zero]
    exact inv_nonneg.mpr (blockNormalization_pos W hW).le

/-- Raw scalar frame coefficients are bounded by the normalized physical-row
canonical tensor with only the explicit `3W`-row evaluation loss. -/
theorem packetScalarMatrixCoefficientNorm_le_evaluationFactor_mul_tensor
    (W : ℕ) (hW : 0 < W) (r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    packetScalarMatrixCoefficientNorm r z CL BR U V s ≤
      packetTensorEvaluationFactor W *
        ‖packetScalarCoefficientTensor W r z CL BR U V s‖ := by
  letI : DecidableEq (ThreeBlockVariable (Fin W)) := Classical.decEq _
  let P := packetScalarMatrixCoefficientPolynomial r z CL BR U V s
  have hP : HasSquarefreeSupport P :=
    hasSquarefreeSupport_classical_to_infer (by
      simpa only [P] using
        (hasSquarefreeSupport_packetScalarMatrixCoefficientPolynomial
          r z CL BR U V s))
  obtain ⟨a, ha, hraw⟩ := exists_squarefree_rademacher_norm_le_eval P hP
  let rows := packetAtomRowsOfRealAssignment W a
  have hrows : ∀ i j, ‖rows i j‖ ≤ (blockNormalization W)⁻¹ :=
    packetAtomRowsOfRealAssignment_abs_le W hW a ha
  have htensor := norm_multiAffineEval_finRows_le
    (E := ℂ) (PacketAtomRowCount W) (blockNormalization W)⁻¹
    (inv_nonneg.mpr (blockNormalization_pos W hW).le)
    (PacketAtomRowCount W)
    (packetScalarCoefficientTensor W r z CL BR U V s) rows hrows
  have hrepresentation :
      multiAffineEval (packetScalarCoefficientTensor W r z CL BR U V s)
          (finRowsToMultiAffineRows (PacketAtomRowCount W)
            (PacketAtomRowCount W) rows) =
        packetScalarCoefficientEval W r z CL BR U V s rows := by
    have h := congrFun
      (packetScalarCoefficientEval_recursive_isMultiAffine
        W r z CL BR U V s).eval_tensorOfFunction
      (finRowsToMultiAffineRows (PacketAtomRowCount W)
        (PacketAtomRowCount W) rows)
    simpa only [packetScalarCoefficientTensor,
      packetScalarCoefficientEvalRecursive,
      multiAffineRowsToFinRows_leftInverse] using h
  have heval : eval (fun e ↦ (a e : ℂ)) P =
      packetScalarCoefficientEval W r z CL BR U V s rows := by
    unfold packetScalarCoefficientEval
    rw [packetAtomAssignment_rowsOfRealAssignment W hW a]
  calc
    packetScalarMatrixCoefficientNorm r z CL BR U V s ≤
        ‖eval (fun e ↦ (a e : ℂ)) P‖ := by
      simpa only [packetScalarMatrixCoefficientNorm,
        packetScalarMatrixCoefficientCoeffVector, P] using hraw
    _ = ‖packetScalarCoefficientEval W r z CL BR U V s rows‖ := by rw [heval]
    _ = ‖multiAffineEval
          (packetScalarCoefficientTensor W r z CL BR U V s)
          (finRowsToMultiAffineRows (PacketAtomRowCount W)
            (PacketAtomRowCount W) rows)‖ := by rw [hrepresentation]
    _ ≤ packetTensorEvaluationFactor W *
        ‖packetScalarCoefficientTensor W r z CL BR U V s‖ := by
      simpa only [packetTensorEvaluationFactor] using htensor

/-- The same raw-to-normalized tensor comparison for the literal boundary
determinant polynomial used in Propositions 10.7 and 10.9. -/
theorem packetBoundaryCoefficientNorm_le_evaluationFactor_mul_tensor
    (W : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    packetBoundaryCoefficientNorm z CL BR Theta ≤
      packetTensorEvaluationFactor W *
        ‖packetBoundaryCoefficientTensor W z CL BR Theta‖ := by
  let P := packetBoundaryPolynomial z CL BR Theta
  have hP : HasSquarefreeSupport P := by
    simpa only [P] using
      (hasSquarefreeSupport_globalBoundaryDetPolynomial z CL BR Theta)
  obtain ⟨a, ha, hraw⟩ := exists_squarefree_rademacher_norm_le_eval P hP
  let rows := packetAtomRowsOfRealAssignment W a
  have hrows : ∀ i j, ‖rows i j‖ ≤ (blockNormalization W)⁻¹ :=
    packetAtomRowsOfRealAssignment_abs_le W hW a ha
  have htensor := norm_multiAffineEval_finRows_le
    (E := ℂ) (PacketAtomRowCount W) (blockNormalization W)⁻¹
    (inv_nonneg.mpr (blockNormalization_pos W hW).le)
    (PacketAtomRowCount W)
    (packetBoundaryCoefficientTensor W z CL BR Theta) rows hrows
  have hrepresentation :
      multiAffineEval (packetBoundaryCoefficientTensor W z CL BR Theta)
          (finRowsToMultiAffineRows (PacketAtomRowCount W)
            (PacketAtomRowCount W) rows) =
        packetBoundaryEval W z CL BR Theta rows := by
    have h := congrFun
      (packetBoundaryEval_recursive_isMultiAffine
        W z CL BR Theta).eval_tensorOfFunction
      (finRowsToMultiAffineRows (PacketAtomRowCount W)
        (PacketAtomRowCount W) rows)
    simpa only [packetBoundaryCoefficientTensor,
      packetBoundaryEvalRecursive,
      multiAffineRowsToFinRows_leftInverse] using h
  have heval : eval (fun e ↦ (a e : ℂ)) P =
      packetBoundaryEval W z CL BR Theta rows := by
    unfold packetBoundaryEval
    rw [packetAtomAssignment_rowsOfRealAssignment W hW a]
  calc
    packetBoundaryCoefficientNorm z CL BR Theta ≤
        ‖eval (fun e ↦ (a e : ℂ)) P‖ := by
      simpa only [packetBoundaryCoefficientNorm,
        globalBoundaryCoefficientNorm, globalBoundaryCoeffVector, P] using hraw
    _ = ‖packetBoundaryEval W z CL BR Theta rows‖ := by rw [heval]
    _ = ‖multiAffineEval (packetBoundaryCoefficientTensor W z CL BR Theta)
          (finRowsToMultiAffineRows (PacketAtomRowCount W)
            (PacketAtomRowCount W) rows)‖ := by rw [hrepresentation]
    _ ≤ packetTensorEvaluationFactor W *
        ‖packetBoundaryCoefficientTensor W z CL BR Theta‖ := by
      simpa only [packetTensorEvaluationFactor] using htensor

theorem packetTensorEvaluationFactor_eq_oneSiteGrowth_pow
    (W : ℕ) (hW : 0 < W) :
    packetTensorEvaluationFactor W = oneSiteDetTensorGrowth W ^ 3 := by
  have hcard : PacketAtomRowCount W = 3 * W := by
    simpa only [Fintype.card_fin] using
      (card_threeBlockIndex (W := Fin W))
  have habs : |(blockNormalization W)⁻¹| =
      (blockNormalization W)⁻¹ := by
    rw [abs_of_pos]
    exact inv_pos.mpr (blockNormalization_pos W hW)
  unfold packetTensorEvaluationFactor oneSiteDetTensorGrowth
  rw [hcard, habs]
  push_cast
  rw [← pow_mul]
  congr 1 <;> ring

def packetTensorLogConstant : ℝ := 3 * oneSiteDetLogConstant

theorem packetTensorLogConstant_nonneg : 0 ≤ packetTensorLogConstant :=
  mul_nonneg (by norm_num) oneSiteDetLogConstant_nonneg

theorem posLog_packetTensorEvaluationFactor_le_W_log_eW
    (W : ℕ) (hW : 0 < W) :
    Real.posLog (packetTensorEvaluationFactor W) ≤
      packetTensorLogConstant * W * Real.log (Real.exp 1 * W) := by
  rw [packetTensorEvaluationFactor_eq_oneSiteGrowth_pow W hW,
    Real.posLog_pow]
  have h := posLog_oneSiteDetTensorGrowth_le_W_log_eW W hW
  unfold packetTensorLogConstant
  norm_num
  nlinarith

/-- Deterministic normalized-tensor inverse bound used by Proposition 10.10.
The only variable loss is the literal endpoint comparison constant. -/
theorem posLog_inv_packetScalarCoefficientTensor_le
    (W : ℕ) (hW : 0 < W) (r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    Real.posLog ‖packetScalarCoefficientTensor W r z CL BR U V s‖⁻¹ ≤
      Real.posLog (packetTensorEvaluationFactor W) +
        Real.posLog (packetEndpointComparisonConstant z CL BR) := by
  let Γ := ‖packetScalarCoefficientTensor W r z CL BR U V s‖
  let F := packetTensorEvaluationFactor W
  let K := packetEndpointComparisonConstant z CL BR
  have hK : 0 < K := packetEndpointComparisonConstant_pos z CL BR
  have hF : 0 < F := by
    unfold F packetTensorEvaluationFactor
    apply pow_pos
    have hinv : 0 ≤ (blockNormalization W)⁻¹ :=
      (inv_pos.mpr (blockNormalization_pos W hW)).le
    have hmul : 0 ≤ (PacketAtomRowCount W : ℝ) *
        (blockNormalization W)⁻¹ := mul_nonneg (by positivity) hinv
    linarith
  have hraw :=
    (packetScalarMatrixCoefficientNorm_bounds_and_pos
      r z CL BR hCL hBR U V s).1
  have hscale :=
    packetScalarMatrixCoefficientNorm_le_evaluationFactor_mul_tensor
      W hW r z CL BR U V s
  have hlower : K⁻¹ ≤ F * Γ := hraw.trans hscale
  have hΓ : 0 < Γ := by
    by_contra h
    have hz : Γ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hz, mul_zero] at hlower
    exact (not_le_of_gt (inv_pos.mpr hK)) hlower
  have hone : 1 ≤ (F * K) * Γ := by
    calc
      1 = K * K⁻¹ := (mul_inv_cancel₀ hK.ne').symm
      _ ≤ K * (F * Γ) :=
        mul_le_mul_of_nonneg_left hlower hK.le
      _ = (F * K) * Γ := by ring
  have hinv : Γ⁻¹ ≤ F * K := by
    rw [← one_mul Γ⁻¹, mul_inv_le_iff₀ hΓ]
    simpa only [one_mul] using hone
  calc
    Real.posLog Γ⁻¹ ≤ Real.posLog (F * K) :=
      Real.posLog_le_posLog (inv_nonneg.mpr hΓ.le) hinv
    _ ≤ Real.posLog F + Real.posLog K := Real.posLog_mul

theorem packetThreeRowCost_le_W_log_eW
    (L : ℝ) (W : ℕ) (hW : 0 < W) :
    multiAffineLogCost L
        (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) ≤
      3 * ENNReal.ofReal (oneSiteRowLogConstant L) *
        oneSiteWLogScale W := by
  have hcard : PacketAtomRowCount W = 3 * W := by
    simpa only [Fintype.card_fin] using
      (card_threeBlockIndex (W := Fin W))
  rw [hcard]
  calc
    multiAffineLogCost L (List.replicate (3 * W) (3 * W)) =
        3 * multiAffineLogCost L (List.replicate (1 * W) (3 * W)) := by
      rw [multiAffineLogCost_replicate, multiAffineLogCost_replicate]
      push_cast
      ring
    _ ≤ 3 * ENNReal.ofReal (oneSiteRowLogConstant L * W *
          Real.log (Real.exp 1 * W)) :=
      mul_le_mul' le_rfl (oneSiteRepeatedRowCost_le_W_log_eW L W hW)
    _ = 3 * ENNReal.ofReal (oneSiteRowLogConstant L) *
        oneSiteWLogScale W := by
      unfold oneSiteWLogScale
      rw [show oneSiteRowLogConstant L * (W : ℝ) *
          Real.log (Real.exp 1 * W) = oneSiteRowLogConstant L *
            ((W : ℝ) * Real.log (Real.exp 1 * W)) by ring,
        ENNReal.ofReal_mul (oneSiteRowLogConstant_nonneg L)]
      ring

end BernoulliSection10Complex
