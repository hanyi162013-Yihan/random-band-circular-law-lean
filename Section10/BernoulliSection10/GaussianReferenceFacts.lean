import BernoulliSection10.Section3Inputs
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The literal circular Gaussian atom used by both density branches

The reference law is the already-defined product of two independent
`N(0, 1/2)` coordinates. Its moments and planar density domination are
proved here; they are not part of the retained BC12 hypotheses.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section

namespace BernoulliSection10.SourceInputs

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def circularGaussianAtom (x : ℝ × ℝ) : ℂ :=
  (x.1 : ℂ) + Complex.I * (x.2 : ℂ)

theorem measurable_circularGaussianAtom : Measurable circularGaussianAtom := by
  unfold circularGaussianAtom
  fun_prop

theorem circularGaussianAtom_eq_equiv (x : ℝ × ℝ) :
    circularGaussianAtom x = Complex.measurableEquivRealProd.symm x := by
  apply Complex.ext <;> simp [circularGaussianAtom]

theorem circularGaussian_fst_memLp (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x : ℝ × ℝ => x.1) p circularGaussianPairLaw := by
  exact (memLp_id_gaussianReal' (μ := 0) (v := 1 / 2) p hp).comp_measurePreserving
    (measurePreserving_fst (μ := gaussianReal 0 (1 / 2)) (ν := gaussianReal 0 (1 / 2)))

theorem circularGaussian_snd_memLp (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x : ℝ × ℝ => x.2) p circularGaussianPairLaw := by
  exact (memLp_id_gaussianReal' (μ := 0) (v := 1 / 2) p hp).comp_measurePreserving
    (measurePreserving_snd (μ := gaussianReal 0 (1 / 2)) (ν := gaussianReal 0 (1 / 2)))

theorem circularGaussianAtom_memLp (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp circularGaussianAtom p circularGaussianPairLaw := by
  have hf : MemLp (fun x : ℝ × ℝ => (x.1 : ℂ)) p circularGaussianPairLaw :=
    (circularGaussian_fst_memLp p hp).ofReal
  have hg : MemLp (fun x : ℝ × ℝ => (x.2 : ℂ)) p circularGaussianPairLaw :=
    (circularGaussian_snd_memLp p hp).ofReal
  have hsum : MemLp (fun x : ℝ × ℝ => (x.1 : ℂ) + Complex.I * (x.2 : ℂ))
      p circularGaussianPairLaw := hf.add (hg.const_mul Complex.I)
  exact hsum

theorem circularGaussianAtom_integrable :
    Integrable circularGaussianAtom circularGaussianPairLaw :=
  memLp_one_iff_integrable.mp (circularGaussianAtom_memLp 1 (by norm_num))

theorem circularGaussianAtom_third_integrable :
    Integrable (fun x => ‖circularGaussianAtom x‖ ^ 3) circularGaussianPairLaw :=
  (circularGaussianAtom_memLp 3 (by norm_num)).integrable_norm_pow (by norm_num)

theorem circularGaussianAtom_centered :
    (∫ x, circularGaussianAtom x ∂circularGaussianPairLaw) = 0 := by
  have hf : Integrable (fun x : ℝ × ℝ => (x.1 : ℂ)) circularGaussianPairLaw :=
    memLp_one_iff_integrable.mp ((circularGaussian_fst_memLp 1 (by norm_num)).ofReal)
  have hg : Integrable (fun x : ℝ × ℝ => (x.2 : ℂ)) circularGaussianPairLaw :=
    memLp_one_iff_integrable.mp ((circularGaussian_snd_memLp 1 (by norm_num)).ofReal)
  have hfst : (∫ x : ℝ × ℝ, x.1 ∂circularGaussianPairLaw) = 0 := by
    simpa [circularGaussianPairLaw] using
      (integral_fun_fst (μ := gaussianReal 0 (1 / 2)) (ν := gaussianReal 0 (1 / 2))
        (fun x : ℝ => x))
  have hsnd : (∫ x : ℝ × ℝ, x.2 ∂circularGaussianPairLaw) = 0 := by
    simpa [circularGaussianPairLaw] using
      (integral_fun_snd (μ := gaussianReal 0 (1 / 2)) (ν := gaussianReal 0 (1 / 2))
        (fun x : ℝ => x))
  simp only [circularGaussianAtom]
  rw [integral_add hf (hg.const_mul Complex.I), integral_const_mul]
  simp only [integral_complex_ofReal, hfst, hsnd, Complex.ofReal_zero, mul_zero, add_zero]

theorem gaussianHalf_second_moment :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 (1 / 2)) = 1 / 2 := by
  have h := variance_eq_integral
    (μ := gaussianReal 0 (1 / 2)) (X := fun x : ℝ => x) measurable_id.aemeasurable
  simpa using h.symm

theorem circularGaussianAtom_second_moment :
    (∫ x, ‖circularGaussianAtom x‖ ^ 2 ∂circularGaussianPairLaw) = 1 := by
  have hf : Integrable (fun x : ℝ × ℝ => x.1 ^ 2) circularGaussianPairLaw := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (circularGaussian_fst_memLp 2 (by norm_num)).integrable_norm_pow (by norm_num)
  have hg : Integrable (fun x : ℝ × ℝ => x.2 ^ 2) circularGaussianPairLaw := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (circularGaussian_snd_memLp 2 (by norm_num)).integrable_norm_pow (by norm_num)
  have he (x : ℝ × ℝ) : ‖circularGaussianAtom x‖ ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, circularGaussianAtom, pow_two]
  have hfst : (∫ x : ℝ × ℝ, x.1 ^ 2 ∂circularGaussianPairLaw) = 1 / 2 := by
    calc
      _ = (gaussianReal 0 (1 / 2)).real Set.univ •
          (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 (1 / 2)) :=
        integral_fun_fst (fun x : ℝ => x ^ 2)
      _ = 1 / 2 := by rw [gaussianHalf_second_moment]; simp
  have hsnd : (∫ x : ℝ × ℝ, x.2 ^ 2 ∂circularGaussianPairLaw) = 1 / 2 := by
    calc
      _ = (gaussianReal 0 (1 / 2)).real Set.univ •
          (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 (1 / 2)) :=
        integral_fun_snd (fun x : ℝ => x ^ 2)
      _ = 1 / 2 := by rw [gaussianHalf_second_moment]; simp
  simp_rw [he]
  rw [integral_add hf hg]
  rw [hfst, hsnd]
  norm_num

theorem gaussianHalf_le_volume : gaussianReal 0 (1 / 2) ≤ (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)]
  conv_rhs => rw [← withDensity_one (μ := (volume : Measure ℝ))]
  apply withDensity_mono
  apply ae_of_all
  intro x
  rw [gaussianPDF, gaussianPDFReal]
  apply ENNReal.ofReal_le_one.mpr
  have he : Real.exp (-((x - 0) ^ 2) / (2 * ((1 / 2 : ℝ≥0) : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  have hs : 1 ≤ Real.sqrt (2 * Real.pi * ((1 / 2 : ℝ≥0) : ℝ)) := by
    apply Real.one_le_sqrt.mpr
    norm_num
    linarith [Real.pi_gt_three]
  exact (mul_le_of_le_one_right (by positivity) he).trans
    (inv_le_one_of_one_le₀ hs)

theorem circularGaussianAtom_law_le_volume :
    Measure.map circularGaussianAtom circularGaussianPairLaw ≤ (volume : Measure ℂ) := by
  have hp : circularGaussianPairLaw ≤ (volume : Measure (ℝ × ℝ)) := by
    exact Measure.prod_mono gaussianHalf_le_volume gaussianHalf_le_volume
  have hv : Measure.map circularGaussianAtom (volume : Measure (ℝ × ℝ)) = volume := by
    rw [show circularGaussianAtom =
      (Complex.measurableEquivRealProd.symm : (ℝ × ℝ) → ℂ) from
        funext circularGaussianAtom_eq_equiv]
    exact Complex.volume_preserving_equiv_real_prod.symm.map_eq
  exact hv ▸ Measure.map_mono hp measurable_circularGaussianAtom

end BernoulliSection10.SourceInputs
