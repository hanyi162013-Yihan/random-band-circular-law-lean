import CircularLawSections56.Section5.LiteralComplementaryInverse
import CircularLawSections56.Section5.CompletedSection4UniformInputs

/-! # Concrete terminal paths: append actual IID rows to the physical product

Both endpoints and every intermediate pressure are expectations of the literal
open-row matrix product.  Invertibility, integrability, probability transport,
and the two-sided row cost are derived here rather than supplied as a path ledger.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

def literalOpenMeanPressure (d n : ℕ) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1)) : ℝ :=
  ∫ rows, profile.paperIndicatorOpenPressure center z q rows
    ∂paperIndicatorOpenRowSampleMeasure n d ν

theorem literal_open_mean_pressure_succ
    (d W n : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (f : ℂ → ℝ≥0∞)
    [IsProbabilityMeasure ((volume : Measure ℂ).withDensity f)]
    (hL : 0 ≤ L) (hf : ∀ᵐ u ∂(volume : Measure ℂ), f u ≤ ENNReal.ofReal L)
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity f))
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity f ≤ 1) :
    |literalOpenMeanPressure d (n + 1) (volume.withDensity f) profile center z q -
      literalOpenMeanPressure d n (volume.withDensity f) profile center z q| ≤
      uniformInverseRowConstant c₀ L z * Real.log (Real.exp 1 * (W : ℝ)) := by
  let ν : Measure ℂ := volume.withDensity f
  let ρ := paperIndicatorRowMeasure d ν
  let μ := paperIndicatorOpenRowSampleMeasure n d ν
  let : IsProbabilityMeasure ρ := iidMeasure_isProbability ν _
  let : IsProbabilityMeasure μ := iidMeasure_isProbability ρ _
  let : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty_bridge _ _
  have hjoin : MeasurePreserving
      (joinLast : ((Fin n → PaperIndicatorAtomRow d) × PaperIndicatorAtomRow d) → _)
      (μ.prod ρ) (paperIndicatorOpenRowSampleMeasure (n + 1) d ν) :=
    ⟨measurable_joinLast, rfl⟩
  have hrow : ∀ s, MeasurePreserving
      (fun ω : (Fin n → PaperIndicatorAtomRow d) × PaperIndicatorAtomRow d => ω.2 s)
      (μ.prod ρ) ν := by
    intro s
    have heval : MeasurePreserving (fun row : PaperIndicatorAtomRow d => row s) ρ ν := by
      simpa only [ρ, paperIndicatorRowMeasure, iidMeasure_eq_pi] using
        measurePreserving_eval (fun _ : Fin (d + 2) => ν) s
    exact heval.comp measurePreserving_snd
  have hpress := fun k => complex_literalPhysicalOpenPressure_integrable k ν
    (complexBallBound_withDensity hf) hL profile hc₀ hsqrt center z q hInt hSecond
  have hunit := ae_literalPhysicalOutsideExteriorProduct_isUnit_complex_withDensity
    n profile hc₀ center hcenter z q hf
  have hbase : ∀ᵐ ω : (Fin n → PaperIndicatorAtomRow d) × PaperIndicatorAtomRow d ∂μ.prod ρ,
      profile.paperIndicatorOpenExteriorProduct center z q ω.1 ≠ 0 := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hunit] with ω hω
    exact hω.ne_zero
  have hprod : ∀ ω : (Fin n → PaperIndicatorAtomRow d) × PaperIndicatorAtomRow d,
      profile.paperIndicatorOpenExteriorProduct center z q (joinLast ω) =
        profile.paperIndicatorOpenExteriorRow center z q ω.2 *
          profile.paperIndicatorOpenExteriorProduct center z q ω.1 := by
    intro ω
    exact iidMatrixCellProduct_joinLast _ _ _
  have hlog : (fun ω : (Fin n → PaperIndicatorAtomRow d) × PaperIndicatorAtomRow d =>
      profile.paperIndicatorOpenPressure center z q (joinLast ω)) =ᵐ[μ.prod ρ]
      (fun ω => Real.log ‖profile.paperIndicatorOpenExteriorRow center z q ω.2 *
        profile.paperIndicatorOpenExteriorProduct center z q ω.1‖) := by
    apply ae_of_all
    intro ω
    change Real.log ‖profile.paperIndicatorOpenExteriorProduct center z q (joinLast ω)‖ = _
    rw [hprod ω]
  have hfullInt : Integrable (fun ω : (Fin n → PaperIndicatorAtomRow d) × PaperIndicatorAtomRow d =>
      Real.log ‖profile.paperIndicatorOpenExteriorRow center z q ω.2 *
        profile.paperIndicatorOpenExteriorProduct center z q ω.1‖) (μ.prod ρ) := by
    exact (hjoin.integrable_comp_of_integrable (hpress (n + 1))).congr hlog
  have h := literal_row_pressure_increment (μ.prod ρ) d W hW hd ν profile hc₀ hL
    (complexBallBound_withDensity hf) center hcenter z q Prod.snd measurable_snd hrow hInt hSecond
    (fun ω => profile.paperIndicatorOpenExteriorProduct center z q ω.1) hbase hfullInt
    (measurePreserving_fst.integrable_comp_of_integrable (hpress n))
  have hfullMean : (∫ ω : (Fin n → PaperIndicatorAtomRow d) × PaperIndicatorAtomRow d,
      Real.log ‖profile.paperIndicatorOpenExteriorRow center z q ω.2 *
        profile.paperIndicatorOpenExteriorProduct center z q ω.1‖ ∂μ.prod ρ) =
      literalOpenMeanPressure d (n + 1) ν profile center z q :=
    (integral_congr_ae hlog).symm.trans (integral_comp_measurePreserving_eq hjoin
      (profile.paperIndicatorOpenPressure center z q) (hpress (n + 1)))
  have hbaseMean : (∫ ω : (Fin n → PaperIndicatorAtomRow d) × PaperIndicatorAtomRow d,
      Real.log ‖profile.paperIndicatorOpenExteriorProduct center z q ω.1‖ ∂μ.prod ρ) =
      literalOpenMeanPressure d n ν profile center z q := integral_comp_measurePreserving_eq
    (measurePreserving_fst : MeasurePreserving
      (Prod.fst : ((Fin n → PaperIndicatorAtomRow d) × PaperIndicatorAtomRow d) → _) (μ.prod ρ) μ)
    (profile.paperIndicatorOpenPressure center z q) (hpress n)
  rw [hfullMean, hbaseMean] at h
  exact h

/-- An arbitrary number of actual terminal rows has a degree-uniform cost. -/
theorem literal_open_mean_pressure_terminal
    (d W start steps : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (f : ℂ → ℝ≥0∞)
    [IsProbabilityMeasure ((volume : Measure ℂ).withDensity f)]
    (hL : 0 ≤ L) (hf : ∀ᵐ u ∂(volume : Measure ℂ), f u ≤ ENNReal.ofReal L)
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity f))
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity f ≤ 1) :
    |literalOpenMeanPressure d (start + steps) (volume.withDensity f) profile center z q -
      literalOpenMeanPressure d start (volume.withDensity f) profile center z q| ≤
      (steps : ℝ) * (completedLiteralConstant c₀ L z * Real.log (Real.exp 1 * (W : ℝ))) := by
  have hH : 0 ≤ Real.log (Real.exp 1 * (W : ℝ)) := by
    have := dimensionLogScale_le_logEW d W hW hd
    have := one_le_dimensionLogScale d
    linarith
  have h := uniform_step_cost_telescope
    (fun j => literalOpenMeanPressure d (start + j) (volume.withDensity f) profile center z q)
    steps (completedLiteralConstant c₀ L z * Real.log (Real.exp 1 * (W : ℝ))) (by
      intro j _
      exact (literal_open_mean_pressure_succ d W (start + j) hW hd profile hc₀ hsqrt
        center hcenter z q f hL hf hInt hSecond).trans
        (mul_le_mul_of_nonneg_right (completedLiteralConstant_bounds c₀ L z).2.2.2 hH))
  simpa only [Nat.add_zero] using h

end CircularLawSections56.Section5
