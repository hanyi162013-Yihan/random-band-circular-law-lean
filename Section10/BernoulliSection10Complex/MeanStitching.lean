import BernoulliSection10Complex.ConditionalReset
import BernoulliSection10Complex.ResetSandwichLaw

/-!
# Mean stitching for actual independent physical cells

The single-reset estimate is integrated against the core and past laws.
The joint law is identified with a literal longer interval, so induction
produces (10.40)--(10.41) without any stochastic-process certificate.
-/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem intervalPressure_reset_increment
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W p q : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1)) :
    |intervalPressure μ W (q + 3 + p) z r -
      (intervalPressure μ W p z r + intervalPressure μ W q z r)| ≤
        densityCellMeanErrorConstant L z * W * densityLogScale W := by
  letI := hμ.toIsProbabilityMeasure
  letI (s : ℕ) : IsProbabilityMeasure (intervalRowsLaw W s μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  let ν := (intervalRowsLaw W p μ).prod (intervalRowsLaw W q μ)
  let F : (IntervalRows W p × IntervalRows W q) × IntervalRows W 3 → ℝ :=
    fun v => resetSandwichDegreeLog W p q z r v.1.1 v.1.2 v.2
  let G : IntervalRows W p × IntervalRows W q → ℝ :=
    fun v => ∫ reset, F (v, reset) ∂intervalRowsLaw W 3 μ
  let H : IntervalRows W p × IntervalRows W q → ℝ :=
    fun v => intervalDegreeLog W p z r v.1 + intervalDegreeLog W q z r v.2
  let E := densityCellMeanErrorConstant L z * W * densityLogScale W
  have hmp := resetSandwichRowsFlat_measurePreserving (μ := μ) W p q
  have hident : F = intervalDegreeLog W (q + 3 + p) z r ∘ resetSandwichRowsFlat W p q := by
    funext v
    simp only [F, resetSandwichDegreeLog, Function.comp_apply, intervalDegreeLog,
      resetSandwichRowsFlat, intervalClearedProduct_resetSandwichRows]
  have hFm : Measurable F := by
    rw [hident]
    exact (measurable_intervalDegreeLog W (q + 3 + p) z r).comp hmp.measurable
  have hFi : Integrable F (ν.prod (intervalRowsLaw W 3 μ)) := by
    rw [hident]
    exact hmp.integrable_comp_of_integrable
      (intervalDegreeLog_integrable hμ W (q + 3 + p) hW z r)
  have hGi : Integrable G ν := hFi.integral_prod_left
  have hGm : Measurable G := hFm.stronglyMeasurable.integral_prod_right'.measurable
  have hHi : Integrable H ν :=
    ((measurePreserving_fst (μ := intervalRowsLaw W p μ)
      (ν := intervalRowsLaw W q μ)).integrable_comp_of_integrable
        (intervalDegreeLog_integrable hμ W p hW z r)).add
    ((measurePreserving_snd (μ := intervalRowsLaw W p μ)
      (ν := intervalRowsLaw W q μ)).integrable_comp_of_integrable
        (intervalDegreeLog_integrable hμ W q hW z r))
  have hHm : Measurable H :=
    ((measurable_intervalDegreeLog W p z r).comp measurable_fst).add
      ((measurable_intervalDegreeLog W q z r).comp measurable_snd)
  have hb : ∀ᵐ v ∂ν, H v - E ≤ G v ∧ G v ≤ H v + E := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_le (hHm.sub_const E) hGm).inter
        (measurableSet_le hGm (hHm.add_const E)))).2
    filter_upwards [resetSandwichDegreeLog_integral_bounds_ae hμ W p q hW z] with core hc
    filter_upwards [hc] with past hp
    exact hp r
  have hlower := integral_mono_ae (hHi.sub (integrable_const E)) hGi
    (hb.mono fun _ hv => hv.1)
  have hupper := integral_mono_ae hGi (hHi.add (integrable_const E))
    (hb.mono fun _ hv => hv.2)
  have hG : (∫ v, G v ∂ν) = intervalPressure μ W (q + 3 + p) z r := by
    rw [← integral_prod F hFi]
    rw [hident]
    exact real_integral_comp_measurePreserving hmp
      (measurable_intervalDegreeLog W (q + 3 + p) z r)
  have hH : (∫ v, H v ∂ν) =
      intervalPressure μ W p z r + intervalPressure μ W q z r := by
    have hp : Integrable (fun v : IntervalRows W p × IntervalRows W q =>
        intervalDegreeLog W p z r v.1) ν :=
      (measurePreserving_fst (μ := intervalRowsLaw W p μ)
        (ν := intervalRowsLaw W q μ)).integrable_comp_of_integrable
          (intervalDegreeLog_integrable hμ W p hW z r)
    have hq : Integrable (fun v : IntervalRows W p × IntervalRows W q =>
        intervalDegreeLog W q z r v.2) ν :=
      (measurePreserving_snd (μ := intervalRowsLaw W p μ)
        (ν := intervalRowsLaw W q μ)).integrable_comp_of_integrable
          (intervalDegreeLog_integrable hμ W q hW z r)
    dsimp only [H]
    rw [integral_add hp hq]
    dsimp only [ν]
    rw [integral_fun_fst, integral_fun_snd]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, intervalPressure]
  simp only [Pi.sub_apply] at hlower
  simp only [Pi.add_apply] at hupper
  rw [integral_sub hHi (integrable_const E), integral_const, hH, hG] at hlower
  rw [integral_add hHi (integrable_const E), integral_const, hH, hG] at hupper
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hlower hupper
  exact abs_le.mpr ⟨by linarith only [hlower], by linarith only [hupper]⟩

theorem intervalPressure_zero_sites (μ : Measure ℂ) (W : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) : intervalPressure μ W 0 z r = 0 := by
  letI : Nonempty (Set.powersetCard (Fin W ⊕ Fin W) r.1) := by
    rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
    apply Nat.choose_pos
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  simp [intervalPressure, intervalDegreeLog, intervalClearedProduct, reverseMatrixProduct]

/-- Both bounds in (10.40)--(10.41), simultaneously for all degrees.
The only inputs are the atom law and the literal dimensions. -/
theorem intervalPressure_complete_cells
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W p K : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1)) :
    |intervalPressure μ W (K * (3 + p)) z r -
      (K : ℝ) * intervalPressure μ W p z r| ≤
        (K : ℝ) * (densityCellMeanErrorConstant L z * W * densityLogScale W) := by
  induction K with
  | zero => simp [intervalPressure_zero_sites]
  | succ K ih =>
    have h := intervalPressure_reset_increment hμ W p (K * (3 + p)) hW z r
    have heq : (K + 1) * (3 + p) = K * (3 + p) + 3 + p := by ring
    rw [heq, Nat.cast_add, Nat.cast_one]
    have heq' : intervalPressure μ W (K * (3 + p) + 3 + p) z r -
        ((K : ℝ) + 1) * intervalPressure μ W p z r =
      (intervalPressure μ W (K * (3 + p) + 3 + p) z r -
        (intervalPressure μ W p z r + intervalPressure μ W (K * (3 + p)) z r)) +
      (intervalPressure μ W (K * (3 + p)) z r - (K : ℝ) * intervalPressure μ W p z r) := by ring
    rw [heq']
    exact (abs_add_le _ _).trans ((add_le_add h ih).trans_eq (by ring))

theorem densityCorePressure_mean_stitching
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W K : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1)) :
    |intervalPressure μ W (K * densityCellSites W) z r -
      (K : ℝ) * densityCorePressure μ W z r| ≤
        (K : ℝ) * (densityCellMeanErrorConstant L z * W * densityLogScale W) := by
  simpa only [densityCorePressure, densityCellSites, Nat.add_comm] using
    intervalPressure_complete_cells hμ W (densityCoreSites W) K hW z r

end BernoulliSection10Complex

