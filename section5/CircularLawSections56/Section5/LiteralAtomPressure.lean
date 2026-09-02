import CircularLawSections56.Section5.LiteralAtomProductIntegrability
import CircularLawSections56.Section5.AtomLogControl
import CircularLawSections56.Section5.LiteralTerminalPressure

/-! # Literal open pressures and terminal increments for both atom branches -/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

local instance rowProbability (d : ℕ) (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (paperIndicatorRowMeasure d ν) := iidMeasure_isProbability ν _

local instance rowsProbability (n d : ℕ) (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (paperIndicatorOpenRowSampleMeasure n d ν) :=
  iidMeasure_isProbability (paperIndicatorRowMeasure d ν) _

theorem literal_iid_open_product_integrable_of_atom_log
    (n d : ℕ) {c₀ C₀ K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (hcenter : center ≠ 0)
    (z : ℂ) (q : ExteriorDegree (d + 1)) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hν : AtomLogControl ν K) :
    Integrable (profile.paperIndicatorOpenPressure center z q)
        (paperIndicatorOpenRowSampleMeasure n d ν) ∧
      ∀ᵐ rows ∂paperIndicatorOpenRowSampleMeasure n d ν,
        IsUnit (profile.paperIndicatorOpenExteriorProduct center z q rows) := by
  apply literal_open_product_integrable_of_atom_log
    (paperIndicatorOpenRowSampleMeasure n d ν) n d profile hc₀ center hcenter z q ν
    id measurable_id _ hν.second_integrable hν.second_le_one K hν.nonzero
    hν.negative_integrable hν.negative_bound
  intro t s
  have hr : MeasurePreserving (fun rows : Fin n → PaperIndicatorAtomRow d => rows t)
      (paperIndicatorOpenRowSampleMeasure n d ν) (paperIndicatorRowMeasure d ν) := by
    simpa only [paperIndicatorOpenRowSampleMeasure, iidMeasure_eq_pi] using
      measurePreserving_eval (fun _ : Fin n => paperIndicatorRowMeasure d ν) t
  have hs : MeasurePreserving (fun row : PaperIndicatorAtomRow d => row s)
      (paperIndicatorRowMeasure d ν) ν := by
    simpa only [paperIndicatorRowMeasure, iidMeasure_eq_pi] using
      measurePreserving_eval (fun _ : Fin (d + 2) => ν) s
  exact hs.comp hr

theorem literal_row_pressure_increment_of_atom_log
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ) {c₀ C₀ K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hν : AtomLogControl ν K) (rows : Ω → PaperIndicatorAtomRow d) (hRows : Measurable rows)
    (hMarginal : ∀ s, MeasurePreserving (fun ω => rows ω s) μ ν)
    (P : Ω → Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hBase : ∀ᵐ ω ∂μ, P ω ≠ 0)
    (hExtendedInt : Integrable (fun ω =>
      Real.log ‖profile.paperIndicatorOpenExteriorRow center z q (rows ω) * P ω‖) μ)
    (hBaseInt : Integrable (fun ω => Real.log ‖P ω‖) μ) :
    |(∫ ω, Real.log ‖profile.paperIndicatorOpenExteriorRow center z q (rows ω) * P ω‖ ∂μ) -
        (∫ ω, Real.log ‖P ω‖ ∂μ)| ≤ literalAtomRowCostBound d profile z K := by
  let : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty_bridge _ _
  have hc := literalRowLogMajorant_integrable_and_bound μ d profile hc₀ center z q ν
    rows hRows hMarginal hν.second_integrable hν.second_le_one K hν.nonzero
    hν.negative_integrable hν.negative_bound
  have hdom : ∀ᵐ ω ∂μ,
      |Real.log ‖profile.paperIndicatorOpenExteriorRow center z q (rows ω) * P ω‖ -
        Real.log ‖P ω‖| ≤ literalRowLogMajorant d profile center z q (rows ω) := by
    filter_upwards [hBase, (hMarginal 0).quasiMeasurePreserving.ae hν.nonzero,
      (hMarginal (Fin.last (d + 1))).quasiMeasurePreserving.ae hν.nonzero] with ω hP hl hr
    have hleft := mul_ne_zero (profile.b_ne_zero hc₀ 0) hl
    have hright := mul_ne_zero (profile.b_ne_zero hc₀ (Fin.last (d + 1))) hr
    exact (matrix_pathwise_remainder _ _
      (literal_exterior_row_isUnit_of_edges d profile center hcenter z q (rows ω) hleft hright)
      hP).trans (matrixInverseRowCost_le_literalRowLogMajorant d profile center hcenter z q
        (rows ω) hleft hright)
  have h := (integral_mono_ae (hExtendedInt.sub hBaseInt).abs hc.1 hdom).trans hc.2
  rw [← integral_sub hExtendedInt hBaseInt]
  exact abs_integral_le_integral_abs.trans h

/-- Appending one actual IID row has an explicit two-edge logarithmic cost. -/
theorem literal_open_mean_pressure_succ_of_atom_log
    (d n : ℕ) {c₀ C₀ K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hν : AtomLogControl ν K) :
    |literalOpenMeanPressure d (n + 1) ν profile center z q -
      literalOpenMeanPressure d n ν profile center z q| ≤ literalAtomRowCostBound d profile z K := by
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
  have hall := fun k => literal_iid_open_product_integrable_of_atom_log
    k d profile hc₀ center hcenter z q ν hν
  have hpress := fun k => (hall k).1
  have hunit := (hall n).2
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
  have h := literal_row_pressure_increment_of_atom_log (μ.prod ρ) d profile hc₀
    center hcenter z q ν hν Prod.snd measurable_snd hrow
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

end CircularLawSections56.Section5
