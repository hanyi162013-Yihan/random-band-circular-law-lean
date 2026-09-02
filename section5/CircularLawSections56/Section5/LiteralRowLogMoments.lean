import CircularLawSections56.Section5.UniformPaperConstants
import CircularLawSections56.Section5.MatrixInverseRowCost

/-!
# The elementary logarithmic moments in inverse-row costs

Bounded complex density gives the negative atom-log moment.  The normalized
profile and atom second moments give a degree-uniform positive row-log moment.
These are the elementary costs used by the complementary inverse estimate.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

theorem negativeLog_norm_integrable_and_bound
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (L : ℝ) (hL : 0 ≤ L)
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) :
    Integrable (fun u : ℂ => negativeLog ‖u‖) ν ∧
      ∫ u : ℂ, negativeLog ‖u‖ ∂ν ≤ (Real.log (max 1 (Real.pi * L)) + 1) / 2 := by
  have hsmall : ∀ ρ : ℝ, 0 < ρ →
      ν {u : ℂ | ‖u‖ ≤ (1 : ℝ) * ρ ^ 1} ≤ ENNReal.ofReal ((Real.pi * L) * ρ ^ 2) := by
    intro ρ hρ
    have h := hν 0 ρ hρ.le
    simpa only [Metric.closedBall, dist_zero_right, pow_one, one_mul,
      ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_mul (mul_nonneg Real.pi_pos.le hL),
      ENNReal.ofReal_pow hρ.le] using h
  obtain ⟨_, _, hi, hb⟩ := zeroSet_aeLog_and_integrable_positiveLogLoss_of_power_smallBall
    ν (fun u : ℂ => ‖u‖) continuous_norm.measurable norm_nonneg 1 (Real.pi * L)
      zero_lt_one 1 2 (by decide) (by decide) hsmall
  simpa only [positiveLogLoss, Real.log_one, zero_sub, negativeLog,
    Nat.cast_ofNat, Nat.cast_one, div_one] using And.intro hi hb

/-- The left/right edge amplitudes have a uniform logarithmic cost after the
deterministic variance-profile weights have been included. -/
theorem negativeLog_weighted_atom_integrable_and_bound
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (L : ℝ) (hL : 0 ≤ L)
    (hν : ComplexBallBound ν (ENNReal.ofReal L))
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (s : Fin (d + 2)) :
    Integrable (fun u : ℂ => negativeLog ‖profile.b s * u‖) ν ∧
      ∫ u : ℂ, negativeLog ‖profile.b s * u‖ ∂ν ≤
        uniformFiberNegativeConstant c₀ L * dimensionLogScale d := by
  obtain ⟨hInt, hBound⟩ := negativeLog_norm_integrable_and_bound ν L hL hν
  have hu : ∀ᵐ u : ℂ ∂ν, u ≠ 0 := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using
      measure_singleton_zero_eq_zero_of_complexBallBound hν
  have hb : 0 < ‖profile.b s‖ := norm_pos_iff.2 (profile.b_ne_zero hc₀ s)
  have hdom : ∀ᵐ u : ℂ ∂ν, negativeLog ‖profile.b s * u‖ ≤
      negativeLog ‖profile.b s‖ + negativeLog ‖u‖ := by
    filter_upwards [hu] with u hu
    rw [norm_mul]
    exact negativeLog_mul_le _ _ hb (norm_pos_iff.2 hu)
  have hmeas : Measurable (fun u : ℂ => negativeLog ‖profile.b s * u‖) :=
    measurable_const.max (Real.measurable_log.comp (measurable_const.mul measurable_id).norm).neg
  have hi : Integrable (fun u : ℂ => negativeLog ‖profile.b s * u‖) ν :=
    ((integrable_const (negativeLog ‖profile.b s‖)).add hInt).mono' hmeas.aestronglyMeasurable (by
      filter_upwards [hdom] with u hu
      have hn : 0 ≤ negativeLog ‖profile.b s * u‖ := le_max_left _ _
      simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg hn] using hu)
  have hineq := integral_mono_ae hi ((integrable_const (negativeLog ‖profile.b s‖)).add hInt) hdom
  simp only [Pi.add_apply] at hineq
  rw [integral_add (integrable_const _) hInt, integral_const, probReal_univ, one_smul] at hineq
  have ht : 0 ≤ Real.log (d + 2 : ℝ) :=
    Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  have ha := abs_nonneg (Real.log c₀)
  have hB : 0 ≤ Real.log (max 1 (Real.pi * L)) := Real.log_nonneg (le_max_left _ _)
  have hweight : negativeLog ‖profile.b s‖ ≤
      (|Real.log c₀| + Real.log (d + 2 : ℝ)) / 2 := by
    have hs : 0 < Real.sqrt (c₀ / (d + 2 : ℝ)) := Real.sqrt_pos.2 (by positivity)
    have hw : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ ‖profile.b s‖ := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
        profile.sqrt_lower_le_norm_b s
    have hl := Real.log_le_log hs hw
    have hhalf := negative_log_profile_sqrt_le d c₀ hc₀
    rw [negativeLog, max_le_iff]
    constructor <;> linarith
  refine ⟨hi, ?_⟩
  dsimp only [uniformFiberNegativeConstant, dimensionLogScale]
  nlinarith [mul_nonneg ha ht, mul_nonneg hB ht]

theorem positiveLog_freshRowMajorant_integrable_and_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (z : ℂ) (atoms : Ω → ResetLabel (d + 1) → ℂ)
    (hmeas : ∀ ell, Measurable (fun ω => atoms ω ell))
    (hcoord : ∀ ell, Integrable (fun ω => ‖atoms ω ell‖ ^ 2) μ ∧
      ∫ ω, ‖atoms ω ell‖ ^ 2 ∂μ ≤ 1) :
    Integrable (fun ω => positiveLog (profile.freshRowNormMajorant z (atoms ω))) μ ∧
      ∫ ω, positiveLog (profile.freshRowNormMajorant z (atoms ω)) ∂μ ≤
        (3 * ‖z‖ + 3) * dimensionLogScale d := by
  have hscaled := profile.integrable_freshRowAtomSum_div_sq_and_integral_le_one
    μ hc₀ atoms hmeas hcoord
  have hSmeas : Measurable (fun ω => profile.freshRowAtomSum (atoms ω)) := by
    unfold freshRowAtomSum
    fun_prop
  have hSnonneg : ∀ ω, 0 ≤ profile.freshRowAtomSum (atoms ω) := by
    intro ω
    exact Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hrowScale : (1 : ℝ) ≤ d + 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hsq := integrable_and_integral_positiveLogSquare_le_of_scaledSecondMoment
    μ (fun ω => profile.freshRowAtomSum (atoms ω)) hSmeas hSnonneg
    ‖z‖ (d + 2 : ℝ) 1 (norm_nonneg _) hrowScale hscaled.1 hscaled.2
  have hmeasG : Measurable (fun ω => positiveLog (profile.freshRowNormMajorant z (atoms ω))) := by
    exact measurable_const.max (Real.measurable_log.comp (hSmeas.add measurable_const))
  obtain ⟨hInt, hBound⟩ := integrable_and_integral_le_sqrt_integral_sq_of_nonneg
    μ _ hmeasG (fun _ => positiveLog_nonneg _)
    (by simpa only [positiveLog, freshRowNormMajorant_eq] using hsq.1)
  refine ⟨hInt, hBound.trans ?_⟩
  apply le_trans (Real.sqrt_le_sqrt ?_) (freshRow_sqrt_moment_le_uniform d z)
  simpa only [positiveLog, freshRowNormMajorant_eq, mul_one] using hsq.2

/-- Uniform expected positive-log cost for every actual exterior degree of one row. -/
theorem positiveLog_paperIndicatorOpenExteriorRow_integrable_and_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (rows : Ω → PaperIndicatorAtomRow d)
    (hRows : Measurable rows)
    (hcoord : ∀ ell,
      Integrable (fun ω => ‖paperIndicatorOpenRowAtoms (rows ω) ell‖ ^ 2) μ ∧
      ∫ ω, ‖paperIndicatorOpenRowAtoms (rows ω) ell‖ ^ 2 ∂μ ≤ 1) :
    Integrable (fun ω => positiveLog ‖profile.paperIndicatorOpenExteriorRow center z q (rows ω)‖) μ ∧
      ∫ ω, positiveLog ‖profile.paperIndicatorOpenExteriorRow center z q (rows ω)‖ ∂μ ≤
        (3 * ‖z‖ + 3) * dimensionLogScale d := by
  let : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty_bridge _ _
  have hmeas : ∀ ell, Measurable (fun ω => paperIndicatorOpenRowAtoms (rows ω) ell) := by
    intro ell
    cases ell with
    | none => exact (measurable_pi_apply _).comp hRows
    | some j => exact (measurable_pi_apply _).comp hRows
  have hmajor := positiveLog_freshRowMajorant_integrable_and_bound μ d profile hc₀ z
    (fun ω => paperIndicatorOpenRowAtoms (rows ω)) hmeas hcoord
  have hnorm : ∀ ω, ‖profile.paperIndicatorOpenExteriorRow center z q (rows ω)‖ ≤
      profile.freshRowNormMajorant z (paperIndicatorOpenRowAtoms (rows ω)) := by
    intro ω
    rw [profile.paperIndicatorOpenExteriorRow_eq_freshExteriorRow]
    exact profile.norm_freshExteriorRow_le_freshRowNormMajorant center z _ q 0
  have hdom : ∀ ω, positiveLog ‖profile.paperIndicatorOpenExteriorRow center z q (rows ω)‖ ≤
      positiveLog (profile.freshRowNormMajorant z (paperIndicatorOpenRowAtoms (rows ω))) := by
    intro ω
    change Real.posLog _ ≤ Real.posLog _
    apply Real.monotoneOn_posLog (norm_nonneg _) (profile.freshRowNormMajorant_nonneg _ _) (hnorm ω)
  have hmeasNorm : Measurable (fun ω => ‖profile.paperIndicatorOpenExteriorRow center z q (rows ω)‖) :=
    (profile.continuous_paperIndicatorOpenExteriorRow center z q).norm.measurable.comp hRows
  have hmeasCost : Measurable
      (fun ω => positiveLog ‖profile.paperIndicatorOpenExteriorRow center z q (rows ω)‖) :=
    measurable_const.max (Real.measurable_log.comp hmeasNorm)
  have hi : Integrable (fun ω => positiveLog ‖profile.paperIndicatorOpenExteriorRow center z q (rows ω)‖) μ :=
    hmajor.1.mono' hmeasCost.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (positiveLog_nonneg _)]
      exact hdom ω)
  exact ⟨hi, (integral_mono_ae hi hmajor.1 (Filter.Eventually.of_forall hdom)).trans hmajor.2⟩

end CircularLawSections56.Section5
