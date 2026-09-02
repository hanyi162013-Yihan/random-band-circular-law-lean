import CircularLawSections56.Section5.CompanionInverseNorm
import CircularLawSections56.Section5.Section4CompletedInverse

/-! # The complementary inverse input is a theorem for the literal model -/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

theorem literal_companion_coefficient_size_le_majorant
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ) (row : PaperIndicatorAtomRow d) :
    ‖profile.paperIndicatorOpenBeta row‖ +
        ∑ j, ‖profile.paperIndicatorOpenShiftedInterior center z row j‖ ≤
      profile.freshRowNormMajorant z (paperIndicatorOpenRowAtoms row) := by
  classical
  have hsum : (∑ j : Fin (d + 1),
      ‖profile.b j.castSucc * row j.castSucc - if j = center then z else 0‖) ≤
      (∑ j : Fin (d + 1), ‖profile.b j.castSucc * row j.castSucc‖) + ‖z‖ := by
    calc
      _ ≤ ∑ j : Fin (d + 1),
          (‖profile.b j.castSucc * row j.castSucc‖ + ‖if j = center then z else 0‖) :=
        Finset.sum_le_sum fun j _ => norm_sub_le _ _
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        have he : ∀ j : Fin (d + 1), ‖if j = center then z else 0‖ =
            if j = center then ‖z‖ else 0 := by
          intro j
          by_cases hj : j = center <;> simp [hj]
        simp_rw [he]
        simp
  unfold freshRowNormMajorant
  rw [Fintype.sum_option]
  simpa only [paperIndicatorOpenBeta, paperIndicatorOpenShiftedInterior,
    paperIndicatorOpenRowAtoms_none, paperIndicatorOpenRowAtoms_some, orderedResetWeight,
    norm_mul, add_assoc, add_comm, add_left_comm] using
      add_le_add_left hsum ‖profile.paperIndicatorOpenBeta row‖

/-- Pointwise complementary inverse bound, with no inverse-norm premise.
The center must not be the left edge, so its spectral shift leaves that edge intact. -/
theorem literal_exterior_row_inverse_le
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (row : PaperIndicatorAtomRow d)
    (hleft : profile.b 0 * row 0 ≠ 0)
    (hright : profile.b (Fin.last (d + 1)) * row (Fin.last (d + 1)) ≠ 0) :
    ‖(profile.paperIndicatorOpenExteriorRow center z q row)⁻¹‖ ≤
      profile.freshRowNormMajorant z (paperIndicatorOpenRowAtoms row) /
        (‖profile.b 0 * row 0‖ *
          ‖profile.b (Fin.last (d + 1)) * row (Fin.last (d + 1))‖) := by
  have hc : profile.paperIndicatorOpenShiftedInterior center z row 0 = profile.b 0 * row 0 := by
    simp [paperIndicatorOpenShiftedInterior, Ne.symm hcenter]
  rw [profile.paperIndicatorOpenExteriorRow_eq_clearedCompound center z q row hright]
  have h := norm_clearedCompanion_inverse_le d q (profile.paperIndicatorOpenBeta row)
    (profile.paperIndicatorOpenShiftedInterior center z row) hright (by simpa only [hc] using hleft)
  rw [hc] at h
  exact h.trans (div_le_div_of_nonneg_right
    (literal_companion_coefficient_size_le_majorant d profile center z row) (by positivity))

/-- The former Section 4 inverse input follows from atom marginals and the
bounded-density small-ball estimate. Independence of the row from the past is unnecessary. -/
theorem section4ComplementaryInverseInput_of_literal
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : ℕ) {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (ν : Measure ℂ) (hν : ComplexBallBound ν (ENNReal.ofReal L))
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (rows : Ω → PaperIndicatorAtomRow d)
    (hMarginal : ∀ s, MeasurePreserving (fun ω => rows ω s) μ ν) :
    Section4ComplementaryInverseInput μ d profile center z q rows := by
  have hzero : ∀ᵐ u : ℂ ∂ν, u ≠ 0 := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using
      measure_singleton_zero_eq_zero_of_complexBallBound hν
  filter_upwards [(hMarginal 0).quasiMeasurePreserving.ae hzero,
    (hMarginal (Fin.last (d + 1))).quasiMeasurePreserving.ae hzero] with ω hleft hright
  exact literal_exterior_row_inverse_le d profile center hcenter z q (rows ω)
    (mul_ne_zero (profile.b_ne_zero hc₀ _) hleft)
    (mul_ne_zero (profile.b_ne_zero hc₀ _) hright)

theorem literal_exterior_row_isUnit_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : ℕ) {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (ν : Measure ℂ) (hν : ComplexBallBound ν (ENNReal.ofReal L))
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (rows : Ω → PaperIndicatorAtomRow d)
    (hMarginal : ∀ s, MeasurePreserving (fun ω => rows ω s) μ ν) :
    ∀ᵐ ω ∂μ, IsUnit (profile.paperIndicatorOpenExteriorRow center z q (rows ω)) := by
  have hzero : ∀ᵐ u : ℂ ∂ν, u ≠ 0 := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using
      measure_singleton_zero_eq_zero_of_complexBallBound hν
  filter_upwards [(hMarginal 0).quasiMeasurePreserving.ae hzero,
    (hMarginal (Fin.last (d + 1))).quasiMeasurePreserving.ae hzero] with ω hleft hright
  have hβ : profile.paperIndicatorOpenBeta (rows ω) ≠ 0 :=
    mul_ne_zero (profile.b_ne_zero hc₀ _) hright
  have hc : profile.paperIndicatorOpenShiftedInterior center z (rows ω) 0 ≠ 0 := by
    simpa [paperIndicatorOpenShiftedInterior, Ne.symm hcenter] using
      mul_ne_zero (profile.b_ne_zero hc₀ 0) hleft
  rw [profile.paperIndicatorOpenExteriorRow_eq_clearedCompound center z q (rows ω) hβ,
    Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
  exact (isUnit_iff_ne_zero.2 hβ).pow _ |>.mul
    ((Matrix.isUnit_iff_isUnit_det _).1
      (rowCompanion_finLeftShift_compound_isUnit d q.val _ _ hβ hc))

/-- The uniform row cost now requires neither a complementary inverse hypothesis
nor a row-invertibility hypothesis. -/
theorem literal_row_pressure_increment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d W : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hL : 0 ≤ L) (hν : ComplexBallBound ν (ENNReal.ofReal L))
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ) (q : ExteriorDegree (d + 1))
    (rows : Ω → PaperIndicatorAtomRow d) (hRows : Measurable rows)
    (hMarginal : ∀ s, MeasurePreserving (fun ω => rows ω s) μ ν)
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1)
    (P : Ω → Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hBase : ∀ᵐ ω ∂μ, P ω ≠ 0)
    (hExtendedInt : Integrable (fun ω =>
      Real.log ‖profile.paperIndicatorOpenExteriorRow center z q (rows ω) * P ω‖) μ)
    (hBaseInt : Integrable (fun ω => Real.log ‖P ω‖) μ) :
    |(∫ ω, Real.log ‖profile.paperIndicatorOpenExteriorRow center z q (rows ω) * P ω‖ ∂μ) -
      (∫ ω, Real.log ‖P ω‖ ∂μ)| ≤
      uniformInverseRowConstant c₀ L z * Real.log (Real.exp 1 * (W : ℝ)) :=
  literal_row_pressure_increment_of_section4_inverse μ d W hW hd ν profile hc₀ hL hν
    center z q rows hRows hMarginal hInt hSecond P
    (literal_exterior_row_isUnit_ae μ d profile hc₀ ν hν center hcenter z q rows hMarginal) hBase
    (section4ComplementaryInverseInput_of_literal μ d profile hc₀ ν hν
      center hcenter z q rows hMarginal) hExtendedInt hBaseInt

end CircularLawSections56.Section5
