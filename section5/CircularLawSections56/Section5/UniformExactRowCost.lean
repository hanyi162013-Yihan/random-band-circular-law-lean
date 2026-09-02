import CircularLawSections56.Section5.LiteralExactRowCost
import CircularLawSections56.Section5.RealSampleTransport
import CircularLawSections56.Section5.TaperLiteralProfile

/-! # Uniform actual forward/inverse expectation, including original real rows

The displayed manuscript cost is the sum of two expectations of positive
logarithms. It is bounded by one fixed coefficient times `log(eW)`, uniformly
over all exterior degrees and sizes; the taper specialization discharges the
deteriorating endpoint-weight bound internally.
-/

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

def exactRowCostConstant (A K : ℝ) (z : ℂ) : ℝ := 3 * (6 * ‖z‖ + 7 + A + 2 * K)

theorem literal_row_forward_inverse_uniform
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d W : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    {c₀ C₀ A K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hc : |Real.log c₀| ≤ A * dimensionLogScale d)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hν : AtomLogControl ν K) (rows : Ω → PaperIndicatorAtomRow d) (hRows : Measurable rows)
    (hMarginal : ∀ s, MeasurePreserving (fun ω => rows ω s) μ ν) :
    let R := fun ω => profile.paperIndicatorOpenExteriorRow center z q (rows ω)
    Integrable (fun ω => positiveLog ‖R ω‖) μ ∧
      Integrable (fun ω => positiveLog ‖(R ω)⁻¹‖) μ ∧
      (∫ ω, positiveLog ‖R ω‖ ∂μ) + (∫ ω, positiveLog ‖(R ω)⁻¹‖ ∂μ) ≤
        exactRowCostConstant A K z * Real.log (Real.exp 1 * (W : ℝ)) := by
  have h := literal_row_forward_inverse_expectation μ d profile hc₀ center hcenter z q
    ν hν rows hRows hMarginal
  refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
  apply (literalAtomRowCostBound_le_logarithmic d profile hc₀ A K hA hK hc z).trans
  have hs := mul_le_mul_of_nonneg_left (dimensionLogScale_le_logEW d W hW hd)
    (show 0 ≤ 6 * ‖z‖ + 7 + A + 2 * K by positivity)
  simpa only [exactRowCostConstant, mul_assoc, mul_left_comm, mul_comm] using hs

theorem real_iid_row_forward_inverse_uniform
    (d W : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    {c₀ C₀ A : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hA : 0 ≤ A) (hc : |Real.log c₀| ≤ A * dimensionLogScale d)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ) (q : ExteriorDegree (d + 1))
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (L : ℝ) (hL : 0 ≤ L)
    (hDensity : RealIntervalBound ρ (ENNReal.ofReal L))
    (hInt : Integrable (fun u : ℝ => u ^ 2) ρ) (hSecond : ∫ u : ℝ, u ^ 2 ∂ρ ≤ 1) :
    let R := fun ω => profile.paperIndicatorOpenExteriorRow center z q (realSampleComplexify _ ω)
    Integrable (fun ω => positiveLog ‖R ω‖) (iidMeasure ρ (d + 2)) ∧
      Integrable (fun ω => positiveLog ‖(R ω)⁻¹‖) (iidMeasure ρ (d + 2)) ∧
      (∫ ω, positiveLog ‖R ω‖ ∂iidMeasure ρ (d + 2)) +
        (∫ ω, positiveLog ‖(R ω)⁻¹‖ ∂iidMeasure ρ (d + 2)) ≤
        exactRowCostConstant A (Real.log (max 1 (2 * L)) + 1) z *
          Real.log (Real.exp 1 * (W : ℝ)) := by
  let : IsProbabilityMeasure (iidMeasure ρ (d + 2)) := iidMeasure_isProbability ρ _
  have hMP := realSampleComplexify_measurePreserving (d + 2) ρ
  apply literal_row_forward_inverse_uniform (iidMeasure ρ (d + 2)) d W hW hd profile
    hc₀ hA (by linarith [Real.log_nonneg (le_max_left 1 (2 * L))]) hc
    center hcenter z q (realComplexAtomLaw ρ) (AtomLogControl.real ρ L hL hDensity hInt hSecond)
    (realSampleComplexify (d + 2)) hMP.measurable
  intro s
  exact (show MeasurePreserving (fun ω : Fin (d + 2) → ℂ => ω s)
      (iidMeasure (realComplexAtomLaw ρ) (d + 2)) (realComplexAtomLaw ρ) from
    ⟨measurable_pi_apply _, iidMeasure_map_coordinate _ _⟩).comp hMP

theorem tapered_real_row_forward_inverse_uniform
    (p : PolynomialTaperProfile) (W : ℕ) (hW : 0 < W) (z : ℂ)
    (q : ExteriorDegree (taperStateDimension W + 1))
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (L : ℝ) (hL : 0 ≤ L)
    (hDensity : RealIntervalBound ρ (ENNReal.ofReal L))
    (hInt : Integrable (fun u : ℝ => u ^ 2) ρ) (hSecond : ∫ u : ℝ, u ^ 2 ∂ρ ≤ 1) :
    let R := fun ω => (p.literalWeights W hW).paperIndicatorOpenExteriorRow
      (taperCenter W hW) z q (realSampleComplexify _ ω)
    Integrable (fun ω => positiveLog ‖R ω‖) (iidMeasure ρ (taperStateDimension W + 2)) ∧
      Integrable (fun ω => positiveLog ‖(R ω)⁻¹‖) (iidMeasure ρ (taperStateDimension W + 2)) ∧
      (∫ ω, positiveLog ‖R ω‖ ∂iidMeasure ρ (taperStateDimension W + 2)) +
        (∫ ω, positiveLog ‖(R ω)⁻¹‖ ∂iidMeasure ρ (taperStateDimension W + 2)) ≤
        exactRowCostConstant p.logarithmicWeightConstant (Real.log (max 1 (2 * L)) + 1) z *
          Real.log (Real.exp 1 * (W : ℝ)) :=
  real_iid_row_forward_inverse_uniform (taperStateDimension W) W hW
    (taperStateDimension_succ W hW) (p.literalWeights W hW) (p.lowerParameter_pos W)
    p.logarithmicWeightConstant_nonneg (p.literalWeights_logarithmic W hW)
    (taperCenter W hW) (taperCenter_ne_zero W hW) z q ρ L hL hDensity hInt hSecond

end CircularLawSections56.Section5
