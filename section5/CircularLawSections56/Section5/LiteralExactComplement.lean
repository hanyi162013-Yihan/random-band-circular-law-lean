import CircularLawSections56.Section5.ComplementaryExteriorNorm
import CircularLawSections56.Section5.LiteralComplementaryInverse
import CircularLawSections56.Section5.RealAtomLogMoments

/-! # The manuscript's exact two-edge complementary norm identity

This is an equality for the actual cleared companion rows, not the earlier
linear-majorant inequality.  It applies to real and complex atoms alike.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights Matrix

theorem norm_clearedCompanion_inverse_eq_complement
    (d : ℕ) (q : ExteriorDegree (d + 1)) (β : ℂ) (c : Fin (d + 1) → ℂ)
    (hβ : β ≠ 0) (hc : c 0 ≠ 0) :
    ‖(β • compound q.val (rowCompanion (finLeftShift d) (Fin.last d) β c))⁻¹‖ =
      ‖β • compound (complementaryDegree d q).val
        (rowCompanion (finLeftShift d) (Fin.last d) β c)‖ / ‖c 0 * β‖ := by
  let T := rowCompanion (finLeftShift d) (Fin.last d) β c
  have hT : IsUnit T.det :=
    Matrix.isUnit_det_of_left_inverse (reversedCompanion_mul_companion d β c hβ hc)
  have hi : (β • compound q.val T)⁻¹ = β⁻¹ • compound q.val T⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← compound_mul,
      Matrix.nonsing_inv_mul _ hT, compound_identity, inv_mul_cancel₀ hβ, one_smul]
  have hd : ‖T.det‖ = ‖c 0‖ / ‖β‖ := by
    simp only [T, rowCompanion_finLeftShift_det, norm_mul, norm_pow, norm_neg,
      norm_one, one_pow, one_mul, norm_div]
  change ‖(β • compound q.val T)⁻¹‖ =
    ‖β • compound (complementaryDegree d q).val T‖ / ‖c 0 * β‖
  rw [hi, norm_smul, norm_inv, compound_nonsing_inv d q.val T hT,
    norm_compound_inverse_eq_complement d q T hT, hd, norm_smul, norm_mul]
  field_simp

/-- The exact formula `‖(A^(r))⁻¹‖ = ‖A^(D-r)‖ / |αβ|` for a literal row.
The left-edge spectral shift is excluded by the physical center condition. -/
theorem literal_exterior_row_inverse_eq_complement
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (row : PaperIndicatorAtomRow d)
    (hleft : profile.b 0 * row 0 ≠ 0)
    (hright : profile.b (Fin.last (d + 1)) * row (Fin.last (d + 1)) ≠ 0) :
    ‖(profile.paperIndicatorOpenExteriorRow center z q row)⁻¹‖ =
      ‖profile.paperIndicatorOpenExteriorRow center z (complementaryDegree d q) row‖ /
        ‖(profile.b 0 * row 0) *
          (profile.b (Fin.last (d + 1)) * row (Fin.last (d + 1)))‖ := by
  have hc : profile.paperIndicatorOpenShiftedInterior center z row 0 = profile.b 0 * row 0 := by
    simp [paperIndicatorOpenShiftedInterior, Ne.symm hcenter]
  rw [profile.paperIndicatorOpenExteriorRow_eq_clearedCompound center z q row hright,
    profile.paperIndicatorOpenExteriorRow_eq_clearedCompound center z (complementaryDegree d q) row hright]
  exact norm_clearedCompanion_inverse_eq_complement d q
    (profile.paperIndicatorOpenBeta row) (profile.paperIndicatorOpenShiftedInterior center z row)
    hright (by simpa only [hc] using hleft) |>.trans (by rw [hc]; rfl)

/-- Only the two nonzero edge marginals are needed for the almost-sure identity. -/
theorem literal_exterior_row_inverse_eq_complement_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (q : ExteriorDegree (d + 1)) (rows : Ω → PaperIndicatorAtomRow d)
    (ν : Measure ℂ) (hzero : ∀ᵐ u : ℂ ∂ν, u ≠ 0)
    (hMarginal : ∀ s, MeasurePreserving (fun ω => rows ω s) μ ν) :
    ∀ᵐ ω ∂μ,
      ‖(profile.paperIndicatorOpenExteriorRow center z q (rows ω))⁻¹‖ =
        ‖profile.paperIndicatorOpenExteriorRow center z (complementaryDegree d q) (rows ω)‖ /
          ‖(profile.b 0 * rows ω 0) *
            (profile.b (Fin.last (d + 1)) * rows ω (Fin.last (d + 1)))‖ := by
  filter_upwards [(hMarginal 0).quasiMeasurePreserving.ae hzero,
    (hMarginal (Fin.last (d + 1))).quasiMeasurePreserving.ae hzero] with ω hl hr
  exact literal_exterior_row_inverse_eq_complement d profile center hcenter z q (rows ω)
    (mul_ne_zero (profile.b_ne_zero hc₀ _) hl) (mul_ne_zero (profile.b_ne_zero hc₀ _) hr)

end CircularLawSections56.Section5
