import BernoulliSection10Complex.RemainderProbability
import BernoulliSection10Complex.ConcretePressure

/-! # Mean Hodge control for the literal interval law -/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator ENNReal

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open BernoulliLinearAlgebra Matrix Set Set.powersetCard

theorem intervalMaxHodgeEnvelope_integral_le
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫ x, intervalMaxHodgeEnvelope W s z x ∂intervalRowsLaw W s μ) ≤
      (s : ℝ) * remainderHodgeConstant L z * W * densityLogScale W := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun _ => intervalMaxHodgeEnvelope_nonneg W s z _)
    (measurable_intervalMaxHodgeEnvelope hμ W s z).aestronglyMeasurable]
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness)
      (oneSiteMaxHodgeWLogConstant_ne_top L z)) ENNReal.ofReal_ne_top)
    (intervalMaxHodgeEnvelope_lintegral_le_W_log_eW hμ W s hW z)
  have hn : 0 ≤ (W : ℝ) * densityLogScale W :=
    mul_nonneg (Nat.cast_nonneg _) (densityLogScale_nonneg hW)
  dsimp only [densityLogScale] at hn
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, oneSiteWLogScale,
    densityLogScale, ENNReal.toReal_ofReal hn, remainderHodgeConstant,
    mul_assoc] using h

theorem abs_intervalDegreeLog_le_maxEnvelope_ae
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W s μ, ∀ r : Fin (2 * W + 1),
      |intervalDegreeLog W s z r x| ≤ intervalMaxHodgeEnvelope W s z x := by
  filter_upwards [interval_remainder_log_change_le_ae hμ W s hW z] with x hx
  intro r
  letI : Nonempty (powersetCard (Fin W ⊕ Fin W) r.1) := by
    rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
    apply Nat.choose_pos
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  simpa only [intervalDegreeLog, Matrix.mul_one, norm_one, Real.log_one, sub_zero]
    using hx r 1 one_ne_zero

theorem abs_intervalDegreeLog_integral_le
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1)) :
    (∫ x, |intervalDegreeLog W s z r x| ∂intervalRowsLaw W s μ) ≤
      (s : ℝ) * remainderHodgeConstant L z * W * densityLogScale W := by
  apply (integral_mono_ae (intervalDegreeLog_integrable hμ W s hW z r).abs
    (intervalMaxHodgeEnvelope_integrable hμ W s hW z)
    ((abs_intervalDegreeLog_le_maxEnvelope_ae hμ W s hW z).mono fun _ hx => hx r)).trans
  exact intervalMaxHodgeEnvelope_integral_le hμ W s hW z

theorem abs_intervalPressure_le
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1)) :
    |intervalPressure μ W s z r| ≤
      (s : ℝ) * remainderHodgeConstant L z * W * densityLogScale W :=
  abs_integral_le_integral_abs.trans
    (abs_intervalDegreeLog_integral_le hμ W s hW z r)

end BernoulliSection10Complex

