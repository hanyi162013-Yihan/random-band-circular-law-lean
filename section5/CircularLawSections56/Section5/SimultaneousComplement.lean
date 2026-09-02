import CircularLawSections56.Section5.LiteralExactComplement
import CircularLawSections56.Section5.LiteralAtomRowCost

/-! # One full-measure event for all spectral parameters and exterior degrees

The exceptional event depends only on the two edge atoms. Thus no uncountable
intersection of fixed-parameter full-measure events is used when the identity
is asserted simultaneously for every complex spectral parameter.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

theorem literal_row_simultaneous_complement_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (hcenter : center ≠ 0)
    (rows : Ω → PaperIndicatorAtomRow d) (ν : Measure ℂ)
    (hzero : ∀ᵐ u : ℂ ∂ν, u ≠ 0)
    (hMarginal : ∀ s, MeasurePreserving (fun ω => rows ω s) μ ν) :
    ∀ᵐ ω ∂μ, ∀ z : ℂ, ∀ q : ExteriorDegree (d + 1),
      IsUnit (profile.paperIndicatorOpenExteriorRow center z q (rows ω)) ∧
      ‖(profile.paperIndicatorOpenExteriorRow center z q (rows ω))⁻¹‖ =
        ‖profile.paperIndicatorOpenExteriorRow center z (complementaryDegree d q) (rows ω)‖ /
          ‖(profile.b 0 * rows ω 0) *
            (profile.b (Fin.last (d + 1)) * rows ω (Fin.last (d + 1)))‖ := by
  filter_upwards [(hMarginal 0).quasiMeasurePreserving.ae hzero,
    (hMarginal (Fin.last (d + 1))).quasiMeasurePreserving.ae hzero] with ω hl hr z q
  have hleft := mul_ne_zero (profile.b_ne_zero hc₀ 0) hl
  have hright := mul_ne_zero (profile.b_ne_zero hc₀ (Fin.last (d + 1))) hr
  exact ⟨literal_exterior_row_isUnit_of_edges d profile center hcenter z q (rows ω) hleft hright,
    literal_exterior_row_inverse_eq_complement d profile center hcenter z q (rows ω) hleft hright⟩

theorem literal_rows_simultaneous_complement_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : ℕ → ℕ) {c₀ C₀ : ℕ → ℝ}
    (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n)) (hc₀ : ∀ n, 0 < c₀ n)
    (center : ∀ n, Fin (d n + 1)) (hcenter : ∀ n, center n ≠ 0)
    (rows : ∀ n, Ω → PaperIndicatorAtomRow (d n)) (ν : ℕ → Measure ℂ)
    (hzero : ∀ n, ∀ᵐ u : ℂ ∂ν n, u ≠ 0)
    (hMarginal : ∀ n s, MeasurePreserving (fun ω => rows n ω s) μ (ν n)) :
    ∀ᵐ ω ∂μ, ∀ n, ∀ z : ℂ, ∀ q : ExteriorDegree (d n + 1),
      IsUnit ((profile n).paperIndicatorOpenExteriorRow (center n) z q (rows n ω)) ∧
      ‖((profile n).paperIndicatorOpenExteriorRow (center n) z q (rows n ω))⁻¹‖ =
        ‖(profile n).paperIndicatorOpenExteriorRow (center n) z
          (complementaryDegree (d n) q) (rows n ω)‖ /
          ‖((profile n).b 0 * rows n ω 0) *
            ((profile n).b (Fin.last (d n + 1)) * rows n ω (Fin.last (d n + 1)))‖ := by
  apply ae_all_iff.2
  intro n
  exact literal_row_simultaneous_complement_ae μ (d n) (profile n) (hc₀ n)
    (center n) (hcenter n) (rows n) (ν n) (hzero n) (hMarginal n)

end CircularLawSections56.Section5
