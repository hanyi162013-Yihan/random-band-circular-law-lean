import CircularLawSections56.Section5.RealAtomLogMoments
import CircularLawSections56.Section5.LiteralComplementaryInverse

/-! # Row costs from atom log moments, independent of planar densities

The deterministic weight loss is kept explicit.  Consequently the same theorem
serves real atoms, complex atoms, and weights whose endpoints decay polynomially.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

theorem literal_exterior_row_isUnit_of_edges
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (row : PaperIndicatorAtomRow d)
    (hleft : profile.b 0 * row 0 ≠ 0)
    (hright : profile.b (Fin.last (d + 1)) * row (Fin.last (d + 1)) ≠ 0) :
    IsUnit (profile.paperIndicatorOpenExteriorRow center z q row) := by
  have hc : profile.paperIndicatorOpenShiftedInterior center z row 0 ≠ 0 := by
    simpa [paperIndicatorOpenShiftedInterior, Ne.symm hcenter] using hleft
  rw [profile.paperIndicatorOpenExteriorRow_eq_clearedCompound center z q row hright,
    Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
  exact (isUnit_iff_ne_zero.2 hright).pow _ |>.mul
    ((Matrix.isUnit_iff_isUnit_det _).1
      (rowCompanion_finLeftShift_compound_isUnit d q.val _ _ hright hc))

def literalRowLogMajorant (d : ℕ) {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1))
    (row : PaperIndicatorAtomRow d) : ℝ :=
  positiveLog ‖profile.paperIndicatorOpenExteriorRow center z q row‖ +
    positiveLog (profile.freshRowNormMajorant z (paperIndicatorOpenRowAtoms row)) +
    negativeLog ‖profile.b 0 * row 0‖ +
    negativeLog ‖profile.b (Fin.last (d + 1)) * row (Fin.last (d + 1))‖

def literalAtomRowCostBound (d : ℕ) {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (z : ℂ) (K : ℝ) : ℝ :=
  2 * ((3 * ‖z‖ + 3) * dimensionLogScale d) +
    negativeLog ‖profile.b 0‖ + negativeLog ‖profile.b (Fin.last (d + 1))‖ + 2 * K

theorem literalRowLogMajorant_nonneg (d : ℕ) {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1))
    (row : PaperIndicatorAtomRow d) : 0 ≤ literalRowLogMajorant d profile center z q row := by
  unfold literalRowLogMajorant positiveLog negativeLog
  positivity

theorem matrixInverseRowCost_le_literalRowLogMajorant
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (row : PaperIndicatorAtomRow d)
    (hleft : profile.b 0 * row 0 ≠ 0)
    (hright : profile.b (Fin.last (d + 1)) * row (Fin.last (d + 1)) ≠ 0) :
    matrixInverseRowCost (profile.paperIndicatorOpenExteriorRow center z q row) ≤
      literalRowLogMajorant d profile center z q row := by
  let : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty_bridge _ _
  exact matrixInverseRowCost_le_complementary _ _ _ _
    (literal_exterior_row_isUnit_of_edges d profile center hcenter z q row hleft hright)
    (norm_pos_iff.2 hleft) (norm_pos_iff.2 hright)
    (literal_exterior_row_inverse_le d profile center hcenter z q row hleft hright)

theorem literalRowLogMajorant_integrable_and_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1))
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (rows : Ω → PaperIndicatorAtomRow d) (hRows : Measurable rows)
    (hMarginal : ∀ s, MeasurePreserving (fun ω => rows ω s) μ ν)
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1)
    (K : ℝ) (hzero : ∀ᵐ u : ℂ ∂ν, u ≠ 0)
    (hNegInt : Integrable (fun u : ℂ => negativeLog ‖u‖) ν)
    (hNeg : ∫ u : ℂ, negativeLog ‖u‖ ∂ν ≤ K) :
    Integrable (fun ω => literalRowLogMajorant d profile center z q (rows ω)) μ ∧
      ∫ ω, literalRowLogMajorant d profile center z q (rows ω) ∂μ ≤
        literalAtomRowCostBound d profile z K := by
  have hs : ∀ s, Integrable (fun ω => ‖rows ω s‖ ^ 2) μ ∧
      ∫ ω, ‖rows ω s‖ ^ 2 ∂μ ≤ 1 := fun s =>
    ⟨(hMarginal s).integrable_comp_of_integrable hInt,
      (integral_comp_measurePreserving_eq (hMarginal s) _ hInt).trans_le hSecond⟩
  have hcoord : ∀ ell,
      Integrable (fun ω => ‖paperIndicatorOpenRowAtoms (rows ω) ell‖ ^ 2) μ ∧
      ∫ ω, ‖paperIndicatorOpenRowAtoms (rows ω) ell‖ ^ 2 ∂μ ≤ 1 := by
    intro ell
    cases ell with
    | none => exact hs _
    | some s => exact hs _
  have hm : ∀ ell, Measurable (fun ω => paperIndicatorOpenRowAtoms (rows ω) ell) := by
    intro ell
    cases ell with
    | none => exact (measurable_pi_apply _).comp hRows
    | some s => exact (measurable_pi_apply _).comp hRows
  have hf := positiveLog_paperIndicatorOpenExteriorRow_integrable_and_bound
    μ d profile hc₀ center z q rows hRows hcoord
  have hg := positiveLog_freshRowMajorant_integrable_and_bound μ d profile hc₀ z
    (fun ω => paperIndicatorOpenRowAtoms (rows ω)) hm hcoord
  have he : ∀ s, Integrable (fun ω => negativeLog ‖profile.b s * rows ω s‖) μ ∧
      ∫ ω, negativeLog ‖profile.b s * rows ω s‖ ∂μ ≤ negativeLog ‖profile.b s‖ + K := by
    intro s
    have h := negativeLog_weighted_of_atom_cost ν (profile.b s) (profile.b_ne_zero hc₀ s)
      K hzero hNegInt hNeg
    exact ⟨(hMarginal s).integrable_comp_of_integrable h.1,
      (integral_comp_measurePreserving_eq (hMarginal s) _ h.1).trans_le h.2⟩
  refine ⟨((hf.1.add hg.1).add (he 0).1).add (he (Fin.last (d + 1))).1, ?_⟩
  unfold literalRowLogMajorant
  have h₃ := integral_add ((hf.1.add hg.1).add (he 0).1) (he (Fin.last (d + 1))).1
  have h₂ := integral_add (hf.1.add hg.1) (he 0).1
  have h₁ := integral_add hf.1 hg.1
  simp only [Pi.add_apply] at h₃ h₂ h₁
  rw [h₃, h₂, h₁]
  dsimp only [literalAtomRowCostBound]
  linarith [(he 0).2, (he (Fin.last (d + 1))).2, hf.2, hg.2]

end CircularLawSections56.Section5
