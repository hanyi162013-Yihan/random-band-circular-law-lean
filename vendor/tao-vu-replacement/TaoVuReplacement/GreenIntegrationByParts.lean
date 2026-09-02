import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Green integration by parts with one compactly supported factor

This file proves the analytic integration-by-parts identity needed in
Tao--Vu, Theorem 2.1, Section 3.6.  It is stated for ordinary `C^2`
functions on a finite-dimensional real inner-product space; only the first
factor is required to have compact support.  In particular, the second
factor may be the regularized logarithmic potential, which grows at
infinity and is not a Schwartz function.
-/

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

namespace TaoVuReplacement

open InnerProductSpace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A single-coordinate, twice-integrated-by-parts identity.  This is the
coordinate step in Green's formula. -/
theorem integral_mul_iteratedFDeriv_two_eq
    (f g : E → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (v : E) :
    ∫ x, f x * iteratedFDeriv ℝ 2 g x ![v, v] =
      ∫ x, iteratedFDeriv ℝ 2 f x ![v, v] * g x := by
  let Df : E → ℝ := fun x ↦ fderiv ℝ f x v
  let Dg : E → ℝ := fun x ↦ fderiv ℝ g x v

  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hDf : ContDiff ℝ 1 Df := by
    exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hDg : ContDiff ℝ 1 Dg := by
    exact (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hDf_compact : HasCompactSupport Df := hfc.fderiv_apply (𝕜 := ℝ) v

  have h_f_Dg : HasCompactSupport (fun x ↦ f x * Dg x) := hfc.mul_right
  have h_Df_g : HasCompactSupport (fun x ↦ Df x * g x) := hDf_compact.mul_right
  have h_Df_Dg : HasCompactSupport (fun x ↦ Df x * Dg x) := hDf_compact.mul_right
  have h_f_D2g : HasCompactSupport
      (fun x ↦ f x * fderiv ℝ Dg x v) := hfc.mul_right
  have h_D2f_g : HasCompactSupport
      (fun x ↦ fderiv ℝ Df x v * g x) :=
    (hDf_compact.fderiv_apply (𝕜 := ℝ) v).mul_right

  have int_f_Dg : Integrable (fun x ↦ f x * Dg x) :=
    (hf1.continuous.mul hDg.continuous).integrable_of_hasCompactSupport h_f_Dg
  have int_Df_g : Integrable (fun x ↦ Df x * g x) :=
    (hDf.continuous.mul hg1.continuous).integrable_of_hasCompactSupport h_Df_g
  have int_Df_Dg : Integrable (fun x ↦ Df x * Dg x) :=
    (hDf.continuous.mul hDg.continuous).integrable_of_hasCompactSupport h_Df_Dg
  have hD2g : ContDiff ℝ 0 (fun x ↦ fderiv ℝ Dg x v) := by
    exact (hDg.fderiv_right (m := 0) (by norm_num)).clm_apply
      (contDiff_const : ContDiff ℝ 0 (fun _ : E ↦ v))
  have hD2f : ContDiff ℝ 0 (fun x ↦ fderiv ℝ Df x v) := by
    exact (hDf.fderiv_right (m := 0) (by norm_num)).clm_apply
      (contDiff_const : ContDiff ℝ 0 (fun _ : E ↦ v))
  have int_f_D2g : Integrable (fun x ↦ f x * fderiv ℝ Dg x v) :=
    (hf1.continuous.mul hD2g.continuous).integrable_of_hasCompactSupport h_f_D2g
  have int_D2f_g : Integrable (fun x ↦ fderiv ℝ Df x v * g x) :=
    (hD2f.continuous.mul hg1.continuous).integrable_of_hasCompactSupport h_D2f_g

  have hfirst :
      (∫ x, f x * fderiv ℝ Dg x v) = -∫ x, Df x * Dg x := by
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      int_Df_Dg int_f_D2g int_f_Dg
      (fun x _ ↦ hf1.differentiable (by norm_num) x)
      (fun x _ ↦ hDg.differentiable (by norm_num) x)
  have hsecond :
      (∫ x, Df x * fderiv ℝ g x v) =
        -∫ x, fderiv ℝ Df x v * g x := by
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      int_D2f_g int_Df_Dg int_Df_g
      (fun x _ ↦ hDf.differentiable (by norm_num) x)
      (fun x _ ↦ hg1.differentiable (by norm_num) x)

  have hDg_second : ∀ x,
      fderiv ℝ Dg x v = iteratedFDeriv ℝ 2 g x ![v, v] := by
    intro x
    rw [iteratedFDeriv_two_apply]
    dsimp only [Dg]
    rw [fderiv_clm_apply
      ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
      (differentiableAt_const v)]
    simp
  have hDf_second : ∀ x,
      fderiv ℝ Df x v = iteratedFDeriv ℝ 2 f x ![v, v] := by
    intro x
    rw [iteratedFDeriv_two_apply]
    dsimp only [Df]
    rw [fderiv_clm_apply
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
      (differentiableAt_const v)]
    simp

  simp_rw [← hDg_second] at ⊢
  simp_rw [← hDf_second] at ⊢
  calc
    (∫ x, f x * fderiv ℝ Dg x v) = -∫ x, Df x * Dg x := hfirst
    _ = ∫ x, fderiv ℝ Df x v * g x := by
      rw [hsecond]
      simp

/-- Green's second identity without a boundary term when the first factor is
compactly supported:

`integral f * Δg = integral (Δf) * g`.

This is the exact integration-by-parts step used after regularizing
`log ‖z-w‖` in Tao--Vu §3.6. -/
theorem integral_mul_laplacian_eq_laplacian_mul
    (f g : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) :
    ∫ x, f x * Δ g x = ∫ x, Δ f x * g x := by
  have hcontg : ∀ v : ℂ, Continuous
      (fun x ↦ iteratedFDeriv ℝ 2 g x ![v, v]) := by
    intro v
    have hbase : Continuous (fun x ↦ iteratedFDeriv ℝ 2 g x) :=
      hg.continuous_iteratedFDeriv le_rfl
    fun_prop
  have hcontf : ∀ v : ℂ, Continuous
      (fun x ↦ iteratedFDeriv ℝ 2 f x ![v, v]) := by
    intro v
    have hbase : Continuous (fun x ↦ iteratedFDeriv ℝ 2 f x) :=
      hf.continuous_iteratedFDeriv le_rfl
    fun_prop
  have hint_left : ∀ v : ℂ, Integrable
      (fun x ↦ f x * iteratedFDeriv ℝ 2 g x ![v, v]) := by
    intro v
    exact (hf.continuous.mul (hcontg v)).integrable_of_hasCompactSupport hfc.mul_right
  have hint_right : ∀ v : ℂ, Integrable
      (fun x ↦ iteratedFDeriv ℝ 2 f x ![v, v] * g x) := by
    intro v
    have hsupp : HasCompactSupport
        (fun x ↦ iteratedFDeriv ℝ 2 f x ![v, v]) := by
      apply hfc.mono'
      intro x hx
      apply (support_iteratedFDeriv_subset (𝕜 := ℝ) (f := f) 2)
      intro hzero
      apply hx
      simp [hzero]
    exact ((hcontf v).mul hg.continuous).integrable_of_hasCompactSupport hsupp.mul_right
  rw [laplacian_eq_iteratedFDeriv_complexPlane,
    laplacian_eq_iteratedFDeriv_complexPlane]
  simp_rw [mul_add, add_mul]
  rw [integral_add (hint_left 1) (hint_left Complex.I),
    integral_add (hint_right 1) (hint_right Complex.I)]
  rw [integral_mul_iteratedFDeriv_two_eq f g hf hfc hg 1,
    integral_mul_iteratedFDeriv_two_eq f g hf hfc hg Complex.I]

/-- Symmetric orientation of `integral_mul_laplacian_eq_laplacian_mul`. -/
theorem integral_laplacian_mul_eq_mul_laplacian
    (f g : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) :
    ∫ x, Δ f x * g x = ∫ x, f x * Δ g x :=
  (integral_mul_laplacian_eq_laplacian_mul f g hf hfc hg).symm

end TaoVuReplacement

