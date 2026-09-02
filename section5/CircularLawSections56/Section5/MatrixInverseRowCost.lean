import CircularLawSections56.Section5.InverseAndRemainder
import CircularLawSections56.Section5.LiteralIidMatrixCellAEAdapter

/-!
# Matrix inverse-row costs and integrated terminal remainders

The two submultiplicative hypotheses of the old scalar interface are now proved
for actual Euclidean matrix norms.  The complementary exterior inverse estimate
is isolated as one explicitly named premise; its logarithmic decomposition,
integrability, expectation cost, and finite-row telescope are proved here.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def matrixInverseRowCost (R : Matrix ι ι ℂ) : ℝ :=
  positiveLog ‖R‖ + positiveLog ‖R⁻¹‖

/-- Neither multiplicative comparison is an input anymore. -/
theorem matrix_pathwise_remainder (R P : Matrix ι ι ℂ)
    (hR : IsUnit R) (hP : P ≠ 0) :
    |Real.log ‖R * P‖ - Real.log ‖P‖| ≤ matrixInverseRowCost R := by
  have hdet := (Matrix.isUnit_iff_isUnit_det R).1 hR
  have hcancel : R⁻¹ * (R * P) = P := Matrix.nonsing_inv_mul_cancel_left R P hdet
  have hRP : R * P ≠ 0 := by
    intro h
    apply hP
    rw [← hcancel, h, mul_zero]
  apply pathwise_remainder_log_inequality
    (norm_pos_iff.2 hP) (norm_pos_iff.2 hRP) (norm_pos_iff.2 hR.ne_zero)
    (norm_pos_iff.2 ((Matrix.isUnit_nonsing_inv_iff).2 hR).ne_zero)
    (norm_mul_le _ _)
  calc
    ‖P‖ = ‖R⁻¹ * (R * P)‖ := congrArg norm hcancel.symm
    _ ≤ ‖R⁻¹‖ * ‖R * P‖ := norm_mul_le _ _

def negativeLog (x : ℝ) : ℝ := max 0 (-Real.log x)

theorem positiveLog_div_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    positiveLog (a / b) ≤ positiveLog a + negativeLog b := by
  rw [positiveLog, Real.log_div ha.ne' hb.ne', max_le_iff]
  constructor
  · exact add_nonneg (positiveLog_nonneg _) (le_max_left _ _)
  · have h₁ : Real.log a ≤ positiveLog a := le_max_right _ _
    have h₂ : -Real.log b ≤ negativeLog b := le_max_right _ _
    linarith

theorem negativeLog_mul_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    negativeLog (a * b) ≤ negativeLog a + negativeLog b := by
  rw [negativeLog, Real.log_mul ha.ne' hb.ne', max_le_iff]
  constructor
  · exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · have h₁ : -Real.log a ≤ negativeLog a := le_max_right _ _
    have h₂ : -Real.log b ≤ negativeLog b := le_max_right _ _
    linarith

/-- The complementary inverse formula is needed only as an upper bound. -/
theorem matrixInverseRowCost_le_complementary
    (R : Matrix ι ι ℂ) (complementary α β : ℝ)
    (hR : IsUnit R) (hα : 0 < α) (hβ : 0 < β)
    (hComplementary : ‖R⁻¹‖ ≤ complementary / (α * β)) :
    matrixInverseRowCost R ≤ positiveLog ‖R‖ + positiveLog complementary +
      negativeLog α + negativeLog β := by
  have hinv : 0 < ‖R⁻¹‖ :=
    norm_pos_iff.2 ((Matrix.isUnit_nonsing_inv_iff).2 hR).ne_zero
  have hc : 0 < complementary := by
    have h := (le_div_iff₀ (mul_pos hα hβ)).1 hComplementary
    exact (mul_pos hinv (mul_pos hα hβ)).trans_le h
  have hmono : positiveLog ‖R⁻¹‖ ≤ positiveLog (complementary / (α * β)) :=
    max_le_max le_rfl (Real.log_le_log hinv hComplementary)
  have hdiv := positiveLog_div_le complementary (α * β) hc (mul_pos hα hβ)
  have hmul := negativeLog_mul_le α β hα hβ
  dsimp only [matrixInverseRowCost]
  linarith

/-- An integrated one-row comparison on the actual sample space.  Only the
norm-inverse majorant and its four elementary log moments are supplied. -/
theorem expected_matrix_row_increment_le_complementary
    [MeasurableSpace Ω] (μ : Measure Ω)
    (R P : Ω → Matrix ι ι ℂ) (complementary α β : Ω → ℝ)
    (hUnit : ∀ᵐ ω ∂μ, IsUnit (R ω)) (hBase : ∀ᵐ ω ∂μ, P ω ≠ 0)
    (hα : ∀ᵐ ω ∂μ, 0 < α ω) (hβ : ∀ᵐ ω ∂μ, 0 < β ω)
    (hComplementary : ∀ᵐ ω ∂μ,
      ‖(R ω)⁻¹‖ ≤ complementary ω / (α ω * β ω))
    (hExtendedInt : Integrable (fun ω => Real.log ‖R ω * P ω‖) μ)
    (hBaseInt : Integrable (fun ω => Real.log ‖P ω‖) μ)
    (hForwardInt : Integrable (fun ω => positiveLog ‖R ω‖) μ)
    (hCompInt : Integrable (fun ω => positiveLog (complementary ω)) μ)
    (hAlphaInt : Integrable (fun ω => negativeLog (α ω)) μ)
    (hBetaInt : Integrable (fun ω => negativeLog (β ω)) μ)
    (forwardBound complementaryBound alphaBound betaBound : ℝ)
    (hForward : ∫ ω, positiveLog ‖R ω‖ ∂μ ≤ forwardBound)
    (hComp : ∫ ω, positiveLog (complementary ω) ∂μ ≤ complementaryBound)
    (hAlpha : ∫ ω, negativeLog (α ω) ∂μ ≤ alphaBound)
    (hBeta : ∫ ω, negativeLog (β ω) ∂μ ≤ betaBound) :
    (∫ ω, |Real.log ‖R ω * P ω‖ - Real.log ‖P ω‖| ∂μ ≤
      forwardBound + complementaryBound + alphaBound + betaBound) ∧
    |(∫ ω, Real.log ‖R ω * P ω‖ ∂μ) - (∫ ω, Real.log ‖P ω‖ ∂μ)| ≤
      forwardBound + complementaryBound + alphaBound + betaBound := by
  have hdom : ∀ᵐ ω ∂μ, |Real.log ‖R ω * P ω‖ - Real.log ‖P ω‖| ≤
      positiveLog ‖R ω‖ + positiveLog (complementary ω) +
        negativeLog (α ω) + negativeLog (β ω) := by
    filter_upwards [hUnit, hBase, hα, hβ, hComplementary] with ω hR hP ha hb hc
    exact (matrix_pathwise_remainder (R ω) (P ω) hR hP).trans
      (matrixInverseRowCost_le_complementary (R ω) _ _ _ hR ha hb hc)
  have hbound := integral_mono_ae (hExtendedInt.sub hBaseInt).abs
    (((hForwardInt.add hCompInt).add hAlphaInt).add hBetaInt) hdom
  simp only [Pi.add_apply, Pi.sub_apply] at hbound
  have hsum₃ := integral_add ((hForwardInt.add hCompInt).add hAlphaInt) hBetaInt
  have hsum₂ := integral_add (hForwardInt.add hCompInt) hAlphaInt
  have hsum₁ := integral_add hForwardInt hCompInt
  simp only [Pi.add_apply] at hsum₃ hsum₂ hsum₁
  rw [hsum₃, hsum₂, hsum₁] at hbound
  have htotal : ∫ ω, |Real.log ‖R ω * P ω‖ - Real.log ‖P ω‖| ∂μ ≤
      forwardBound + complementaryBound + alphaBound + betaBound := by linarith
  refine ⟨htotal, ?_⟩
  rw [← integral_sub hExtendedInt hBaseInt]
  exact abs_integral_le_integral_abs.trans htotal

/-- Automatic mean-pressure telescope from actual random matrix products. -/
theorem expected_matrix_terminal_remainder
    [MeasurableSpace Ω] (μ : Measure Ω)
    (product row : ℕ → Ω → Matrix ι ι ℂ) (steps : ℕ) (rowCost : ℝ)
    (hUnit : ∀ j < steps, ∀ᵐ ω ∂μ, IsUnit (row j ω))
    (hBase : ∀ j < steps, ∀ᵐ ω ∂μ, product j ω ≠ 0)
    (hStep : ∀ j < steps, ∀ᵐ ω ∂μ, product (j + 1) ω = row j ω * product j ω)
    (hPressureInt : ∀ j ≤ steps, Integrable (fun ω => Real.log ‖product j ω‖) μ)
    (hCostInt : ∀ j < steps, Integrable (fun ω => matrixInverseRowCost (row j ω)) μ)
    (hCost : ∀ j < steps, ∫ ω, matrixInverseRowCost (row j ω) ∂μ ≤ rowCost) :
    |(∫ ω, Real.log ‖product steps ω‖ ∂μ) - (∫ ω, Real.log ‖product 0 ω‖ ∂μ)| ≤
      (steps : ℝ) * rowCost := by
  apply uniform_step_cost_telescope (fun j => ∫ ω, Real.log ‖product j ω‖ ∂μ) steps rowCost
  intro j hj
  rw [← integral_sub (hPressureInt (j + 1) (by omega)) (hPressureInt j (by omega))]
  apply abs_integral_le_integral_abs.trans
  apply le_trans (integral_mono_ae
    ((hPressureInt (j + 1) (by omega)).sub (hPressureInt j (by omega))).abs (hCostInt j hj) ?_)
    (hCost j hj)
  filter_upwards [hUnit j hj, hBase j hj, hStep j hj] with ω hu hb hs
  simp only [Pi.sub_apply]
  rw [hs]
  exact matrix_pathwise_remainder _ _ hu hb

end CircularLawSections56.Section5
