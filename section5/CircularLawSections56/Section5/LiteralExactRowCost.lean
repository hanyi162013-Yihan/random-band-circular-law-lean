import CircularLawSections56.Section5.LiteralExactComplement
import CircularLawSections56.Section5.LiteralAtomPressure
import CircularLawSections56.Section5.UniformLogarithmicWeights

/-! # The literal forward-plus-inverse expectation in the manuscript

The exact complementary-degree identity supplies inverse-norm measurability,
while the integrable two-edge majorant supplies the expectation bound.  This
gives the actual sum of the two expected positive logarithms, not merely an
auxiliary terminal-increment estimate.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

theorem literal_row_cost_integrable_and_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ) {c₀ C₀ K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hν : AtomLogControl ν K) (rows : Ω → PaperIndicatorAtomRow d) (hRows : Measurable rows)
    (hMarginal : ∀ s, MeasurePreserving (fun ω => rows ω s) μ ν) :
    Integrable (fun ω => matrixInverseRowCost
        (profile.paperIndicatorOpenExteriorRow center z q (rows ω))) μ ∧
      (∫ ω, matrixInverseRowCost
        (profile.paperIndicatorOpenExteriorRow center z q (rows ω)) ∂μ) ≤
        literalAtomRowCostBound d profile z K := by
  let : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty_bridge _ _
  let R := fun ω => profile.paperIndicatorOpenExteriorRow center z q (rows ω)
  let Q := fun ω => profile.paperIndicatorOpenExteriorRow center z (complementaryDegree d q) (rows ω)
  let edge := fun ω => (profile.b 0 * rows ω 0) *
    (profile.b (Fin.last (d + 1)) * rows ω (Fin.last (d + 1)))
  let G := fun ω => positiveLog ‖R ω‖ + positiveLog (‖Q ω‖ / ‖edge ω‖)
  have hR : Measurable (fun ω => ‖R ω‖) :=
    (profile.continuous_paperIndicatorOpenExteriorRow center z q).norm.measurable.comp hRows
  have hQ : Measurable (fun ω => ‖Q ω‖) :=
    (profile.continuous_paperIndicatorOpenExteriorRow center z (complementaryDegree d q)).norm.measurable.comp hRows
  have he : Measurable (fun ω => ‖edge ω‖) :=
    ((measurable_const.mul ((measurable_pi_apply 0).comp hRows)).mul
      (measurable_const.mul ((measurable_pi_apply (Fin.last (d + 1))).comp hRows))).norm
  have hG : Measurable G :=
    (measurable_const.max (Real.measurable_log.comp hR)).add
      (measurable_const.max (Real.measurable_log.comp (hQ.div he)))
  have hIdentity := literal_exterior_row_inverse_eq_complement_ae μ d profile hc₀ center hcenter
    z q rows ν hν.nonzero hMarginal
  have hEq : (fun ω => matrixInverseRowCost (R ω)) =ᵐ[μ] G := by
    filter_upwards [hIdentity] with ω hω
    dsimp only [matrixInverseRowCost, R, G, Q, edge]
    rw [hω]
  have hm : AEStronglyMeasurable (fun ω => matrixInverseRowCost (R ω)) μ :=
    hG.aestronglyMeasurable.congr hEq.symm
  have hmajor := literalRowLogMajorant_integrable_and_bound μ d profile hc₀ center z q ν
    rows hRows hMarginal hν.second_integrable hν.second_le_one K hν.nonzero
    hν.negative_integrable hν.negative_bound
  have hdom : ∀ᵐ ω ∂μ, matrixInverseRowCost (R ω) ≤
      literalRowLogMajorant d profile center z q (rows ω) := by
    filter_upwards [(hMarginal 0).quasiMeasurePreserving.ae hν.nonzero,
      (hMarginal (Fin.last (d + 1))).quasiMeasurePreserving.ae hν.nonzero] with ω hl hr
    exact matrixInverseRowCost_le_literalRowLogMajorant d profile center hcenter z q (rows ω)
      (mul_ne_zero (profile.b_ne_zero hc₀ _) hl) (mul_ne_zero (profile.b_ne_zero hc₀ _) hr)
  have hi : Integrable (fun ω => matrixInverseRowCost (R ω)) μ := by
    apply hmajor.1.mono' hm
    filter_upwards [hdom] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ matrixInverseRowCost (R ω) from
      add_nonneg (positiveLog_nonneg _) (positiveLog_nonneg _))]
    exact hω
  exact ⟨hi, (integral_mono_ae hi hmajor.1 hdom).trans hmajor.2⟩

/-- The exact expectation form of the one-row lemma, for arbitrary marginals
including the real-atom law embedded in the complex plane. -/
theorem literal_row_forward_inverse_expectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ) {c₀ C₀ K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hν : AtomLogControl ν K) (rows : Ω → PaperIndicatorAtomRow d) (hRows : Measurable rows)
    (hMarginal : ∀ s, MeasurePreserving (fun ω => rows ω s) μ ν) :
    let R := fun ω => profile.paperIndicatorOpenExteriorRow center z q (rows ω)
    Integrable (fun ω => positiveLog ‖R ω‖) μ ∧
      Integrable (fun ω => positiveLog ‖(R ω)⁻¹‖) μ ∧
      (∫ ω, positiveLog ‖R ω‖ ∂μ) + (∫ ω, positiveLog ‖(R ω)⁻¹‖ ∂μ) ≤
        literalAtomRowCostBound d profile z K := by
  let R := fun ω => profile.paperIndicatorOpenExteriorRow center z q (rows ω)
  have hcost := literal_row_cost_integrable_and_bound μ d profile hc₀ center hcenter z q ν
    hν rows hRows hMarginal
  have hm : Measurable (fun ω => positiveLog ‖R ω‖) :=
    measurable_const.max (Real.measurable_log.comp
      ((profile.continuous_paperIndicatorOpenExteriorRow center z q).norm.measurable.comp hRows))
  have hf : Integrable (fun ω => positiveLog ‖R ω‖) μ := by
    apply hcost.1.mono' hm.aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (positiveLog_nonneg _)]
      exact le_add_of_nonneg_right (positiveLog_nonneg _)
  have hi : Integrable (fun ω => positiveLog ‖(R ω)⁻¹‖) μ := by
    have h := hcost.1.sub hf
    have heq : (fun ω => matrixInverseRowCost (R ω) - positiveLog ‖R ω‖) =
        (fun ω => positiveLog ‖(R ω)⁻¹‖) := by
      funext ω
      exact add_sub_cancel_left _ _
    exact h.congr (ae_of_all _ fun ω => congrFun heq ω)
  refine ⟨hf, hi, ?_⟩
  have hadd := integral_add hf hi
  rw [← hadd]
  exact hcost.2

end CircularLawSections56.Section5
