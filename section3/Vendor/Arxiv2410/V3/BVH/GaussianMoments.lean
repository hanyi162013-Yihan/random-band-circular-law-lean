/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/GaussianMoments.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.GaussianDiagonal
import Vendor.Arxiv2410.V3.RandomModel
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Gaussian third moments for the BVH replacement step

This file contains the elementary Gaussian input needed by an application-specific
Lindeberg reconstruction of BVH Remark 6.13.  It does not state or assume the BVH
comparison theorem.

The constants below are intentionally coarse.  The only important feature for the
application is the scale `variance^(3/2)`.
-/

namespace Arxiv2410V3.BVH

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

/-- A convenient absolute constant in the real Gaussian third-moment estimate. -/
def realGaussianThirdMomentConstant : ℝ := 54 * Real.exp (1 / 2)

/-- A convenient absolute constant in the complex Gaussian third-moment estimate. -/
def complexGaussianThirdMomentConstant : ℝ :=
  8 * realGaussianThirdMomentConstant

/-- Exponential domination of the third absolute moment of a sub-Gaussian variable.

The estimate is deliberately coarse: taking `t = c⁻¹²` in the MGF bound and using
`|x|³ ≤ (3/t)³ max (exp (t x)) (exp (-t x))` gives the stated constant. -/
theorem integral_abs_cube_le_of_hasSubgaussianMGF
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c mu) :
    (∫ omega, |X omega| ^ 3 ∂mu) ≤
      realGaussianThirdMomentConstant * (Real.sqrt (c : ℝ)) ^ 3 := by
  by_cases hc : c = 0
  · subst c
    have hzero : X =ᵐ[mu] 0 := hX.ae_eq_zero_of_hasSubgaussianMGF_zero
    have hint : (∫ omega, |X omega| ^ 3 ∂mu) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hzero] with omega homega
      simp [homega]
    simp [hint, realGaussianThirdMomentConstant]
  · have hcposNN : 0 < c := (pos_iff_ne_zero.mpr hc)
    have hcpos : 0 < (c : ℝ) := by exact_mod_cast hcposNN
    let s : ℝ := Real.sqrt (c : ℝ)
    let t : ℝ := 1 / s
    have hspos : 0 < s := by
      dsimp only [s]
      exact Real.sqrt_pos.2 hcpos
    have htpos : 0 < t := by
      dsimp only [t]
      positivity
    have hposInt : Integrable (fun omega ↦ Real.exp (t * X omega)) mu :=
      hX.integrable_exp_mul t
    have hnegInt : Integrable (fun omega ↦ Real.exp ((-t) * X omega)) mu :=
      hX.integrable_exp_mul (-t)
    have hrightInt : Integrable
        (fun omega ↦ (3 / |t|) ^ 3 *
          (Real.exp (t * X omega) + Real.exp ((-t) * X omega))) mu := by
      exact (hposInt.add hnegInt).const_mul _
    have hpoint (omega : Omega) :
        |X omega| ^ 3 ≤ (3 / |t|) ^ 3 *
          (Real.exp (t * X omega) + Real.exp ((-t) * X omega)) := by
      have hraw := rpow_abs_le_mul_max_exp (X omega)
        (p := ((3 : ℕ) : ℝ)) (t := t) (by norm_num) htpos.ne'
      simp_rw [← Real.rpow_natCast]
      exact hraw.trans
        (mul_le_mul_of_nonneg_left
          (max_le_add_of_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
          (by positivity))
    have hIntegral :
        (∫ omega, |X omega| ^ 3 ∂mu) ≤
          (3 / |t|) ^ 3 *
            ((∫ omega, Real.exp (t * X omega) ∂mu) +
              ∫ omega, Real.exp ((-t) * X omega) ∂mu) := by
      calc
        (∫ omega, |X omega| ^ 3 ∂mu) ≤
            ∫ omega, (3 / |t|) ^ 3 *
              (Real.exp (t * X omega) + Real.exp ((-t) * X omega)) ∂mu :=
          integral_mono_of_nonneg
            (ae_of_all _ fun omega ↦ pow_nonneg (abs_nonneg _) 3)
            hrightInt (ae_of_all _ hpoint)
        _ = (3 / |t|) ^ 3 *
            ((∫ omega, Real.exp (t * X omega) ∂mu) +
              ∫ omega, Real.exp ((-t) * X omega) ∂mu) := by
          rw [integral_const_mul, integral_add hposInt hnegInt]
    have hMGFpos :
        (∫ omega, Real.exp (t * X omega) ∂mu) ≤
          Real.exp ((c : ℝ) * t ^ 2 / 2) := hX.mgf_le t
    have hMGFneg :
        (∫ omega, Real.exp ((-t) * X omega) ∂mu) ≤
          Real.exp ((c : ℝ) * t ^ 2 / 2) := by
      have h := hX.mgf_le (-t)
      simpa only [mgf, neg_sq] using h
    have hscale : (c : ℝ) * t ^ 2 = 1 := by
      dsimp only [t, s]
      rw [div_pow]
      field_simp
      rw [Real.sq_sqrt hcpos.le]
    calc
      (∫ omega, |X omega| ^ 3 ∂mu) ≤
          (3 / |t|) ^ 3 *
            ((∫ omega, Real.exp (t * X omega) ∂mu) +
              ∫ omega, Real.exp ((-t) * X omega) ∂mu) := hIntegral
      _ ≤ (3 / |t|) ^ 3 *
          (Real.exp ((c : ℝ) * t ^ 2 / 2) +
            Real.exp ((c : ℝ) * t ^ 2 / 2)) := by
        gcongr
      _ = realGaussianThirdMomentConstant * (Real.sqrt (c : ℝ)) ^ 3 := by
        rw [hscale]
        have hfactor : 3 / |t| = 3 * s := by
          rw [abs_of_pos htpos]
          dsimp only [t]
          field_simp
        rw [hfactor]
        dsimp only [s, realGaussianThirdMomentConstant]
        ring

/-- A centered real Gaussian with variance bounded by `c` has third absolute moment
bounded by an absolute constant times `c^(3/2)`. -/
theorem integral_abs_cube_le_of_centered_gaussian_of_variance_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {c : ℝ≥0}
    (hG : HasGaussianLaw X mu)
    (hmean : ∫ omega, X omega ∂mu = 0)
    (hvar : Var[X; mu] ≤ c) :
    (∫ omega, |X omega| ^ 3 ∂mu) ≤
      realGaussianThirdMomentConstant * (Real.sqrt (c : ℝ)) ^ 3 := by
  exact integral_abs_cube_le_of_hasSubgaussianMGF
    (hG.hasSubgaussianMGF_of_integral_eq_zero_of_variance_le hmean hvar)

/-- Model data for a Gaussian companion to an actual v3 random matrix.

For every complex entry, joint Gaussianity is imposed on the pair `(re, im)`.
The five matching fields are precisely the two real first moments and the three
entries of the real `2 × 2` second-moment matrix.  Thus they encode the complete
first- and second-order complex moment data without assuming a comparison result. -/
structure GaussianCompanionModelV3
    (n : ℕ)
    (Omega OmegaXi OmegaG : Type*)
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi] [MeasurableSpace OmegaG]
    (mu : Measure Omega) (nu : Measure OmegaXi) (muG : Measure OmegaG)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure muG]
    (actual : RandomMatrixModelV3 n Omega OmegaXi mu nu) where
  matrix : OmegaG → Matrix (Fin n) (Fin n) ℂ
  entry_measurable : ∀ i j, Measurable (fun omega ↦ matrix omega i j)
  entries_independent :
    iIndepFun (fun ij : Fin n × Fin n ↦ fun omega ↦ matrix omega ij.1 ij.2) muG
  entry_jointGaussian : ∀ i j,
    HasGaussianLaw
      (fun omega ↦ ((matrix omega i j).re, (matrix omega i j).im)) muG
  re_mean_match : ∀ i j,
    (∫ omega, (matrix omega i j).re ∂muG) =
      ∫ omega, (actual.matrix omega i j).re ∂mu
  im_mean_match : ∀ i j,
    (∫ omega, (matrix omega i j).im ∂muG) =
      ∫ omega, (actual.matrix omega i j).im ∂mu
  re_second_match : ∀ i j,
    (∫ omega, (matrix omega i j).re ^ 2 ∂muG) =
      ∫ omega, (actual.matrix omega i j).re ^ 2 ∂mu
  im_second_match : ∀ i j,
    (∫ omega, (matrix omega i j).im ^ 2 ∂muG) =
      ∫ omega, (actual.matrix omega i j).im ^ 2 ∂mu
  re_im_second_match : ∀ i j,
    (∫ omega, (matrix omega i j).re * (matrix omega i j).im ∂muG) =
      ∫ omega,
        (actual.matrix omega i j).re * (actual.matrix omega i j).im ∂mu

end

end Arxiv2410V3.BVH

