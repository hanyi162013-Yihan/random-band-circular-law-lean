import CircularLawSections56.Section5.PublishedSection3GaussianAtom
import CircularLawSections56.Section5.AtomLogControl
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Actual Gaussian atoms satisfy the Section 5 density input

We use the convenient nonsharp bound `circularComplexGaussian ≤ 2 • volume`.
This suffices for every bounded-density interface and avoids optimizing an
irrelevant universal constant. The Gaussian measure itself is unchanged.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

noncomputable section

namespace CircularLawSections56.Section5.PublishedSection3Concrete

theorem gaussianReal_standard_le_volume : gaussianReal 0 1 ≤ (volume : Measure ℝ) := by
  have hpdf (x : ℝ) : gaussianPDF 0 1 x ≤ 1 := by
    have hsqrt : 1 ≤ Real.sqrt (2 * π) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [Real.pi_gt_three]
    have hinv : (Real.sqrt (2 * π))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrt
    have hexp : Real.exp (-(x ^ 2) / 2) ≤ 1 := Real.exp_le_one_iff.2
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by norm_num))
    have hr : gaussianPDFReal 0 1 x ≤ 1 := by
      simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
      exact (mul_le_mul hinv hexp (Real.exp_pos _).le (by norm_num)).trans_eq (by norm_num)
    simpa only [gaussianPDF, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  calc
    volume.withDensity (gaussianPDF 0 1) ≤ volume.withDensity (fun _ : ℝ => 1) :=
      withDensity_mono (ae_of_all _ hpdf)
    _ = volume := by simp

theorem realStandardComplexGaussian_eq_map_pair :
    stdGaussian ℂ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      Complex.measurableEquivRealProd.symm := by
  have hmap := measurePreserving_finTwoArrow (gaussianReal 0 1)
  rw [stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI]
  have hfun : (fun x : Fin 2 → ℝ => ∑ i, x i • Complex.orthonormalBasisOneI i) =
      Complex.measurableEquivRealProd.symm ∘ MeasurableEquiv.finTwoArrow := by
    funext x
    simp only [Complex.coe_orthonormalBasisOneI, Fin.sum_univ_two]
    change (x 0 : ℂ) * 1 + (x 1 : ℂ) * Complex.I =
      Complex.measurableEquivRealProd.symm (x 0, x 1)
    apply Complex.ext <;> simp
  rw [hfun, ← Measure.map_map Complex.measurableEquivRealProd.symm.measurable
    MeasurableEquiv.finTwoArrow.measurable, hmap.map_eq]

theorem realStandardComplexGaussian_le_volume : stdGaussian ℂ ≤ (volume : Measure ℂ) := by
  rw [realStandardComplexGaussian_eq_map_pair]
  have hprod := Measure.prod_mono gaussianReal_standard_le_volume gaussianReal_standard_le_volume
  have h := Measure.map_mono hprod Complex.measurableEquivRealProd.symm.measurable
  simpa only [← Measure.volume_eq_prod, Complex.volume_preserving_equiv_real_prod.symm.map_eq] using h

theorem complexGaussianScale_map_volume :
    (volume : Measure ℂ).map complexGaussianScale = (2 : ℝ≥0∞) • volume := by
  change (volume : Measure ℂ).map (fun z : ℂ => (Real.sqrt 2)⁻¹ • z) = _
  rw [Measure.map_addHaar_smul (volume : Measure ℂ) (inv_ne_zero (by positivity : Real.sqrt 2 ≠ 0))]
  simp only [Complex.finrank_real_complex, inv_pow, inv_inv, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]

theorem circularComplexGaussian_le_two_volume :
    circularComplexGaussian ≤ (2 : ℝ≥0∞) • (volume : Measure ℂ) := by
  have h := Measure.map_mono realStandardComplexGaussian_le_volume complexGaussianScale.measurable
  simpa only [circularComplexGaussian, complexGaussianScale_map_volume] using h

theorem circularComplexGaussian_ballBound :
    CircularLawSection4.ComplexBallBound circularComplexGaussian (ENNReal.ofReal 2) := by
  apply CircularLawSection4.complexBallBound_of_le_smul_volume
  simpa only [ENNReal.ofReal_ofNat] using circularComplexGaussian_le_two_volume

/-- The full existing Section 5 atom-log package is instantiated, not assumed. -/
theorem circularComplexGaussian_atomLogControl :
    CircularLawSections56.Section5.AtomLogControl circularComplexGaussian
      ((Real.log (max 1 (Real.pi * 2)) + 1) / 2) :=
  CircularLawSections56.Section5.AtomLogControl.complex circularComplexGaussian 2 (by norm_num)
    circularComplexGaussian_ballBound circularComplexGaussian_sq_integrable
    circularComplexGaussian_secondMoment.le

end CircularLawSections56.Section5.PublishedSection3Concrete
