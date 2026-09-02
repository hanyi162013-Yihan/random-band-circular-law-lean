import BernoulliSection10.RemainderControl
import BernoulliSection10.ConcretePressure

/-!
# Integrability before choosing singular frames

The reset sandwich is an actual matrix-product observable. Its
integrability follows from the existing Hodge envelope, independent of
any choice of frames used subsequently to bound its expectation.
-/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection10

open BernoulliLinearAlgebra Matrix Set Set.powersetCard

theorem log_product_lower_of_scalar_test {a b t v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (h : a * b * t ≤ v) :
    Real.log a + Real.log b - Real.posLog t⁻¹ ≤ Real.log v := by
  have hh := Real.log_le_log (mul_pos (mul_pos ha hb) ht) h
  rw [Real.log_mul (mul_ne_zero ha.ne' hb.ne') ht.ne',
    Real.log_mul ha.ne' hb.ne'] at hh
  have hl : -Real.log t ≤ Real.posLog t⁻¹ := by
    rw [← Real.log_inv]
    exact le_max_right _ _
  linarith only [hh, hl]

theorem log_norm_sandwich_upper
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A Q B : Matrix n n ℂ) (hA : IsUnit A.det)
    (hQ : IsUnit Q.det) (hB : IsUnit B.det) :
    Real.log ‖A * Q * B‖ ≤ Real.log ‖A‖ + Real.log ‖Q‖ + Real.log ‖B‖ := by
  have hB0 : B ≠ 0 := ((Matrix.isUnit_iff_isUnit_det B).mpr hB).ne_zero
  have hQB : IsUnit (Q * B).det := by rw [Matrix.det_mul]; exact hQ.mul hB
  have hQB0 : Q * B ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mpr hQB).ne_zero
  have h1 := (matrix_logNorm_mul_bounds Q B hQ hB0).2
  have h2 := (matrix_logNorm_mul_bounds A (Q * B) hA hQB0).2
  rw [← Matrix.mul_assoc] at h2
  linarith only [h1, h2]

theorem fixed_interval_sandwich_log_integrable
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1))
    (A B : Matrix (powersetCard (Fin W ⊕ Fin W) r.1)
      (powersetCard (Fin W ⊕ Fin W) r.1) ℂ)
    (hA : IsUnit A.det) (hB : IsUnit B.det) :
    Integrable (fun x => Real.log ‖A * intervalClearedProduct W s z x r * B‖)
      (intervalRowsLaw W s μ) := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W s μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  letI : Nonempty (powersetCard (Fin W ⊕ Fin W) r.1) := by
    rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
    apply Nat.choose_pos
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hB0 : B ≠ 0 := ((Matrix.isUnit_iff_isUnit_det B).mpr hB).ne_zero
  have hc : Continuous (fun x : IntervalRows W s =>
      A * intervalClearedProduct W s z x r * B) :=
    (continuous_const.matrix_mul (continuous_intervalClearedProduct W s z r)).matrix_mul
      continuous_const
  have hm := Real.measurable_log.comp hc.norm.measurable
  have hi : Integrable (fun x => matrixHodgeLoss A +
      intervalMaxHodgeEnvelope W s z x + |Real.log ‖B‖|) (intervalRowsLaw W s μ) :=
    ((integrable_const _).add (intervalMaxHodgeEnvelope_integrable hμ W s hW z)).add
      (integrable_const _)
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [intervalClearedProduct_det_isUnit_ae hμ W s hW z,
    interval_remainder_log_change_le_ae hμ W s hW z] with x hx hb
  have hQB : IsUnit (intervalClearedProduct W s z x r * B).det := by
    rw [Matrix.det_mul]
    exact (hx r).mul hB
  have hQB0 : intervalClearedProduct W s z x r * B ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mpr hQB).ne_zero
  have h1 := abs_le.mp (hb r B hB0)
  have h2 := abs_le.mp (abs_matrix_logNorm_mul_sub_le_hodgeLoss A
    (intervalClearedProduct W s z x r * B) hA hQB0)
  rw [← Matrix.mul_assoc] at h2
  rw [Real.norm_eq_abs]
  dsimp only [Function.comp_apply]
  apply abs_le.mpr
  constructor
  · linarith only [h1.1, h2.1, neg_abs_le (Real.log ‖B‖)]
  · linarith only [h1.2, h2.2, le_abs_self (Real.log ‖B‖)]

end BernoulliSection10
