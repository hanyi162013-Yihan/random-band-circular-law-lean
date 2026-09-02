import BernoulliSection10.HodgeFamilyGrowth
import BernoulliSection10.FinitePressure
import BernoulliLinearAlgebra.ExteriorOperatorVolume

/-!
# Concrete remainder control in Section 10.5.1

The estimates apply to the actual cleared interval product, simultaneously
in every degree. The empty remainder is handled by its identity matrix,
without a spurious Frobenius norm of the identity. The operator norm in
the observable is the Euclidean operator norm throughout.
-/

open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal

noncomputable section

namespace BernoulliSection10

open BernoulliLinearAlgebra Matrix Set Set.powersetCard

section Deterministic

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Frobenius in
theorem matrixL2OperatorNorm_le_frobenius (A : Matrix n n ℂ) :
    matrixL2OperatorNorm A ≤ ‖A‖ := by
  rw [Matrix.frobenius_norm_def]
  simpa only [← Complex.sq_norm, Real.sqrt_eq_rpow, Real.rpow_two] using
    matrixL2OperatorNorm_le_sqrt_sum_normSq A

/-- The pathwise two-sided estimate (10.45). Nonvanishing of the product
is proved from the inverse identity, not assumed separately. -/
theorem matrix_logNorm_mul_bounds [Nonempty n]
    (R A : Matrix n n ℂ) (hR : IsUnit R.det) (hA : A ≠ 0) :
    -Real.log ‖R⁻¹‖ ≤ Real.log ‖R * A‖ - Real.log ‖A‖ ∧
      Real.log ‖R * A‖ - Real.log ‖A‖ ≤ Real.log ‖R‖ := by
  have hR0 : R ≠ 0 := ((Matrix.isUnit_iff_isUnit_det R).mpr hR).ne_zero
  have hcancel : R⁻¹ * (R * A) = A := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul R hR, Matrix.one_mul]
  have hRA0 : R * A ≠ 0 := by
    intro h
    apply hA
    simpa only [h, Matrix.mul_zero] using hcancel.symm
  have hRi0 : R⁻¹ ≠ 0 := by
    intro h
    apply hA
    simpa only [h, Matrix.zero_mul] using hcancel.symm
  have hu := Real.log_le_log (norm_pos_iff.mpr hRA0) (norm_mul_le R A)
  rw [Real.log_mul (norm_ne_zero_iff.mpr hR0) (norm_ne_zero_iff.mpr hA)] at hu
  have hl := Real.log_le_log (norm_pos_iff.mpr hA)
    (show ‖A‖ ≤ ‖R⁻¹‖ * ‖R * A‖ by
      calc
        ‖A‖ = ‖R⁻¹ * (R * A)‖ := congrArg norm hcancel.symm
        _ ≤ ‖R⁻¹‖ * ‖R * A‖ := norm_mul_le R⁻¹ (R * A))
  rw [Real.log_mul (norm_ne_zero_iff.mpr hRi0) (norm_ne_zero_iff.mpr hRA0)] at hl
  constructor <;> linarith

/-- The concrete Frobenius Hodge envelope already proved in Lemma 10.6
also controls the change of the Euclidean-operator logarithm. -/
theorem abs_matrix_logNorm_mul_sub_le_hodgeLoss [Nonempty n]
    (R A : Matrix n n ℂ) (hR : IsUnit R.det) (hA : A ≠ 0) :
    |Real.log ‖R * A‖ - Real.log ‖A‖| ≤ matrixHodgeLoss R := by
  have h := matrix_logNorm_mul_bounds R A hR hA
  have hf : Real.log ‖R‖ ≤ Real.posLog (matrixL2OperatorNorm R) :=
    le_max_right _ _
  have hi : Real.log ‖R⁻¹‖ ≤ Real.posLog (matrixL2OperatorNorm R⁻¹) :=
    le_max_right _ _
  have hf' := Real.posLog_le_posLog (norm_nonneg
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) R))
    (matrixL2OperatorNorm_le_frobenius R)
  have hi' := Real.posLog_le_posLog (norm_nonneg
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) R⁻¹))
    (matrixL2OperatorNorm_le_frobenius R⁻¹)
  change Real.posLog (matrixL2OperatorNorm R) ≤ _ at hf'
  change Real.posLog (matrixL2OperatorNorm R⁻¹) ≤ _ at hi'
  have hp1 := Real.posLog_nonneg (x := matrixL2OperatorNorm R)
  have hp2 := Real.posLog_nonneg (x := matrixL2OperatorNorm R⁻¹)
  unfold matrixHodgeLoss
  apply abs_le.mpr
  constructor
  · linarith only [h.1, hi, hi', hp1, hf']
  · linarith only [h.2, hf, hf', hp2, hi']

end Deterministic

/-- A cleared product is invertible whenever its actual interface blocks
are invertible. This includes the empty interval. -/
theorem intervalClearedProduct_det_isUnit
    (W s : ℕ) (z : ℂ) (x : IntervalRows W s)
    (hB : ∀ j : Fin s, IsUnit (intervalSiteBlocks z x j).B.det)
    (hC : ∀ j : Fin s, IsUnit (intervalSiteBlocks z x j).C.det)
    (r : Fin (2 * W + 1)) :
    IsUnit (intervalClearedProduct W s z x r).det := by
  apply list_prod_det_isUnit
  intro A hA
  simp only [List.mem_ofFn] at hA
  obtain ⟨j, rfl⟩ := hA
  apply clearedStepCompound_det_isUnit r.1
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · exact hB j.rev
  · exact hC j.rev

theorem intervalClearedProduct_det_isUnit_ae
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W s μ, ∀ r : Fin (2 * W + 1),
      IsUnit (intervalClearedProduct W s z x r).det := by
  filter_upwards [intervalInterfaceDets_isUnit_ae hμ W s hW z] with x hx
  intro r
  exact intervalClearedProduct_det_isUnit W s z x
    (fun j => (hx j).1) (fun j => (hx j).2) r

/-- A normalized incoming product can be any nonzero matrix in its degree.
The interval, its envelope and all of its probabilistic hypotheses are
concrete. The bound is uniform over the incoming matrix. -/
theorem interval_remainder_log_change_le_ae
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W s μ, ∀ r : Fin (2 * W + 1),
      ∀ A : Matrix (powersetCard (Fin W ⊕ Fin W) r.1)
        (powersetCard (Fin W ⊕ Fin W) r.1) ℂ, A ≠ 0 →
      |Real.log ‖intervalClearedProduct W s z x r * A‖ - Real.log ‖A‖| ≤
        intervalMaxHodgeEnvelope W s z x := by
  by_cases hs : s = 0
  · subst s
    exact Filter.Eventually.of_forall fun x r A hA => by
      simp [intervalClearedProduct, reverseMatrixProduct, intervalMaxHodgeEnvelope]
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs
    filter_upwards [intervalClearedProduct_det_isUnit_ae hμ W s hW z,
      intervalClearedProduct_hodgeLoss_le_maxEnvelope_ae hμ W s hW hspos z] with x hu hh
    intro r A hA
    letI : Nonempty (powersetCard (Fin W ⊕ Fin W) r.1) := by
      rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
      apply Nat.choose_pos
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    exact (abs_matrix_logNorm_mul_sub_le_hodgeLoss _ A (hu r) hA).trans (hh r)

/-- Equation (10.46) for the actual remainder product, with a common
almost-sure event for every degree and every nonzero incoming family. -/
theorem interval_remainder_max_change_le_ae
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W s μ,
      ∀ A : (r : Fin (2 * W + 1)) →
        Matrix (powersetCard (Fin W ⊕ Fin W) r.1)
          (powersetCard (Fin W ⊕ Fin W) r.1) ℂ,
      (∀ r, A r ≠ 0) →
      |finitePressureMax (fun r => Real.log ‖intervalClearedProduct W s z x r * A r‖) -
        finitePressureMax (fun r => Real.log ‖A r‖)| ≤
          intervalMaxHodgeEnvelope W s z x := by
  filter_upwards [interval_remainder_log_change_le_ae hμ W s hW z] with x hx
  intro A hA
  exact abs_finitePressureMax_sub_le (fun r => hx r (A r) (hA r))

end BernoulliSection10
