import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TaoVuReplacement.GreenIntegrationByParts
import TaoVuReplacement.LogKernelBounds

/-!
# The logarithmic Green kernel on the complex plane

This file develops the analytic kernel used in Tao--Vu, Theorem 2.1,
Section 3.6.  The paper uses the distributional identity

`Δ log ‖z - w‖ = 2π δ_w`.

We regularize the singular potential by

`u_ε(w,z) = (1 / 2) log (‖z-w‖² + ε²)`

and isolate its nonnegative classical Laplacian

`K_ε(w,z) = 2 ε² / (‖z-w‖² + ε²)²`.

The results below are ordinary Lean theorems: this module introduces no
axioms or external interfaces.
-/

open Filter Set MeasureTheory Topology
open MeasureTheory.Measure
open InnerProductSpace Laplacian Module Bornology
open scoped ENNReal InnerProductSpace Real Topology

noncomputable section

namespace TaoVuReplacement

/-- Tao--Vu §3.6: the nonsingular approximation
`u_ε(w,z) = 1/2 log (‖z-w‖² + ε²)` to `log ‖z-w‖`. -/
def regularizedLogKernel (ε : ℝ) (w z : ℂ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (Complex.normSq (z - w) + ε ^ 2)

/-- Tao--Vu §3.6: the density obtained by applying the planar Laplacian to
`regularizedLogKernel`. -/
def regularizedGreenKernel (ε : ℝ) (w z : ℂ) : ℝ :=
  2 * ε ^ 2 / (Complex.normSq (z - w) + ε ^ 2) ^ 2

/-- The radial form of `regularizedGreenKernel`, before translation by its
centre. -/
def radialGreenKernel (ε r : ℝ) : ℝ :=
  2 * ε ^ 2 / (r ^ 2 + ε ^ 2) ^ 2

theorem regularizedGreenKernel_eq_radial (ε : ℝ) (w z : ℂ) :
    regularizedGreenKernel ε w z = radialGreenKernel ε ‖z - w‖ := by
  simp [regularizedGreenKernel, radialGreenKernel, Complex.sq_norm]

/-- The regularized Green density is pointwise nonnegative. -/
theorem regularizedGreenKernel_nonneg (ε : ℝ) (w z : ℂ) :
    0 ≤ regularizedGreenKernel ε w z := by
  unfold regularizedGreenKernel
  positivity

/-- With nonzero regularization parameter, the logarithmic regularization is
continuous on the whole plane. -/
theorem continuous_regularizedLogKernel {ε : ℝ} (hε : ε ≠ 0) (w : ℂ) :
    Continuous (regularizedLogKernel ε w) := by
  unfold regularizedLogKernel
  have hinner : Continuous
      (fun z : ℂ ↦ Complex.normSq (z - w) + ε ^ 2) := by
    exact (Complex.continuous_normSq.comp (continuous_id.sub continuous_const)).add
      continuous_const
  apply Continuous.mul continuous_const
  apply continuous_iff_continuousAt.mpr
  intro z
  have hz : Complex.normSq (z - w) + ε ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (sq_pos_of_ne_zero hε)).ne'
  exact ContinuousAt.comp' (f := fun y : ℂ ↦ Complex.normSq (y - w) + ε ^ 2)
    (Real.continuousAt_log hz) hinner.continuousAt

/-- The regularized logarithmic kernel is globally `C²`, the regularity
needed by Green integration by parts. -/
theorem contDiff_two_regularizedLogKernel {ε : ℝ} (hε : ε ≠ 0) (w : ℂ) :
    ContDiff ℝ 2 (regularizedLogKernel ε w) := by
  unfold regularizedLogKernel
  have hre : ContDiff ℝ 2 (fun z : ℂ ↦ z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ 2 (fun z : ℂ ↦ z.im) := Complex.imCLM.contDiff
  have hreSub : ContDiff ℝ 2 (fun z : ℂ ↦ z.re - w.re) :=
    hre.sub (contDiff_const : ContDiff ℝ 2 (fun _ : ℂ ↦ w.re))
  have himSub : ContDiff ℝ 2 (fun z : ℂ ↦ z.im - w.im) :=
    him.sub (contDiff_const : ContDiff ℝ 2 (fun _ : ℂ ↦ w.im))
  have hεconst : ContDiff ℝ 2 (fun _ : ℂ ↦ ε ^ 2) := contDiff_const
  have hinner : ContDiff ℝ 2
      (fun z : ℂ ↦ Complex.normSq (z - w) + ε ^ 2) := by
    simpa only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] using
      ((hreSub.mul hreSub).add (himSub.mul himSub)).add hεconst
  have hlog : ContDiff ℝ 2
      (fun z : ℂ ↦ Real.log (Complex.normSq (z - w) + ε ^ 2)) :=
    hinner.log fun z ↦ (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (sq_pos_of_ne_zero hε)).ne'
  exact (contDiff_const : ContDiff ℝ 2 (fun _ : ℂ ↦ (1 / 2 : ℝ))).mul hlog

/-! ## Classical Laplacian of the regularization -/

/-- The first real Fréchet derivative of the regularized logarithmic kernel.
This is the directional-gradient calculation underlying Tao--Vu §3.6. -/
theorem fderiv_regularizedLogKernel {ε : ℝ} (hε : ε ≠ 0) (w z v : ℂ) :
    fderiv ℝ (regularizedLogKernel ε w) z v =
      ((z - w).re * v.re + (z - w).im * v.im) /
        (Complex.normSq (z - w) + ε ^ 2) := by
  let a : ℂ → ℝ := fun y ↦ (y - w).re
  let b : ℂ → ℝ := fun y ↦ (y - w).im
  let s : ℂ → ℝ := fun y ↦ Complex.normSq (y - w) + ε ^ 2
  have ha : HasFDerivAt a Complex.reCLM z := by
    simpa [a, Complex.sub_re] using Complex.reCLM.hasFDerivAt.sub_const w.re
  have hb : HasFDerivAt b Complex.imCLM z := by
    simpa [b, Complex.sub_im] using Complex.imCLM.hasFDerivAt.sub_const w.im
  have hs : HasFDerivAt s
      (a z • Complex.reCLM + a z • Complex.reCLM +
        (b z • Complex.imCLM + b z • Complex.imCLM)) z := by
    have h := (ha.mul ha).add (hb.mul hb) |>.add_const (ε ^ 2)
    simpa only [s, a, b, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Pi.add_apply, Pi.mul_apply] using h
  have hsne : s z ≠ 0 := by
    dsimp only [s]
    exact (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (sq_pos_of_ne_zero hε)).ne'
  have hlog := (Real.hasDerivAt_log hsne).hasFDerivAt.comp z hs
  have hu := hlog.const_mul (1 / 2 : ℝ)
  change fderiv ℝ (fun y : ℂ ↦ (1 / 2 : ℝ) * (Real.log ∘ s) y) z v = _
  rw [hu.fderiv]
  dsimp only [s, a, b]
  simp
  field_simp
  ring

/-- The second directional derivative of the explicit gradient formula. -/
theorem fderiv_directional_regularizedLogKernel {ε : ℝ} (hε : ε ≠ 0)
    (w z v : ℂ) :
    fderiv ℝ (fun y : ℂ ↦
      (((y - w).re * v.re + (y - w).im * v.im) /
        (Complex.normSq (y - w) + ε ^ 2))) z v =
      (((v.re ^ 2 + v.im ^ 2) * (Complex.normSq (z - w) + ε ^ 2) -
        2 * ((z - w).re * v.re + (z - w).im * v.im) ^ 2) /
        (Complex.normSq (z - w) + ε ^ 2) ^ 2) := by
  let a : ℂ → ℝ := fun y ↦ (y - w).re
  let b : ℂ → ℝ := fun y ↦ (y - w).im
  have ha : HasFDerivAt a Complex.reCLM z := by
    simpa [a, Complex.sub_re] using Complex.reCLM.hasFDerivAt.sub_const w.re
  have hb : HasFDerivAt b Complex.imCLM z := by
    simpa [b, Complex.sub_im] using Complex.imCLM.hasFDerivAt.sub_const w.im
  have hn := (ha.mul_const v.re).add (hb.mul_const v.im)
  have hs := (ha.mul ha).add (hb.mul hb) |>.add_const (ε ^ 2)
  have hsne : (a z * a z + b z * b z + ε ^ 2) ≠ 0 := by
    dsimp only [a, b]
    rw [← Complex.normSq_apply]
    exact (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (sq_pos_of_ne_zero hε)).ne'
  have hinv := (hasFDerivAt_inv' (𝕜 := ℝ) hsne).comp z hs
  have hquot := hn.mul hinv
  change (fderiv ℝ
    ((((fun y : ℂ ↦ a y * v.re) + fun y ↦ b y * v.im) *
      (Inv.inv ∘ fun y ↦ (a * a + b * b) y + ε ^ 2))) z) v = _
  rw [hquot.fderiv]
  dsimp only [a, b]
  simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply, _root_.add_apply,
    _root_.smul_apply, _root_.neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  rw [Complex.normSq_apply]
  field_simp [hsne]
  ring

/-- Tao--Vu §3.6, regularized kernel calculation:
`Δ_z u_ε(w,z) = K_ε(w,z)`. -/
theorem laplacian_regularizedLogKernel {ε : ℝ} (hε : ε ≠ 0) (w z : ℂ) :
    Δ (regularizedLogKernel ε w) z = regularizedGreenKernel ε w z := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply]
  let u : ℂ → ℝ := regularizedLogKernel ε w
  have hu2 : ContDiff ℝ 2 u := contDiff_two_regularizedLogKernel hε w
  have hfu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    ((hu2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z)
  have happ (v : ℂ) :
      fderiv ℝ (fun y ↦ fderiv ℝ u y v) z v =
        (fderiv ℝ (fderiv ℝ u) z) v v := by
    rw [fderiv_clm_apply hfu (differentiableAt_const v)]
    simp
  change (fderiv ℝ (fderiv ℝ u) z) 1 1 +
      (fderiv ℝ (fderiv ℝ u) z) Complex.I Complex.I = _
  rw [← happ 1, ← happ Complex.I]
  have hfun (v : ℂ) : (fun y ↦ fderiv ℝ u y v) =
      (fun y ↦ ((y - w).re * v.re + (y - w).im * v.im) /
        (Complex.normSq (y - w) + ε ^ 2)) := by
    funext y
    exact fderiv_regularizedLogKernel hε w y v
  rw [hfun 1, hfun Complex.I, fderiv_directional_regularizedLogKernel hε w z 1,
    fderiv_directional_regularizedLogKernel hε w z Complex.I]
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    one_pow, zero_pow two_ne_zero, add_zero, zero_add, mul_one, mul_zero]
  unfold regularizedGreenKernel
  field_simp
  rw [Complex.normSq_apply]
  ring

/-- Regularized Green identity obtained by global integration by parts. -/
theorem integral_laplacian_mul_regularizedLogKernel
    (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {ε : ℝ} (hε : ε ≠ 0) (w : ℂ) :
    ∫ z : ℂ, Δ f z * regularizedLogKernel ε w z =
      ∫ z : ℂ, f z * regularizedGreenKernel ε w z := by
  rw [integral_laplacian_mul_eq_mul_laplacian f (regularizedLogKernel ε w)
    hf hfc (contDiff_two_regularizedLogKernel hε w)]
  congr 1
  funext z
  rw [laplacian_regularizedLogKernel hε]

/-- Away from its centre, `u_ε(w,z)` tends to the singular logarithmic
kernel as `ε → 0`. -/
theorem tendsto_regularizedLogKernel_zero {w z : ℂ} (hzw : z ≠ w) :
    Tendsto (fun ε : ℝ ↦ regularizedLogKernel ε w z) (𝓝 0)
      (𝓝 (Real.log ‖z - w‖)) := by
  have hnormSq : Complex.normSq (z - w) ≠ 0 := by
    exact (Complex.normSq_pos.mpr (sub_ne_zero.mpr hzw)).ne'
  have harg : Tendsto
      (fun ε : ℝ ↦ Complex.normSq (z - w) + ε ^ 2) (𝓝 0)
      (𝓝 (Complex.normSq (z - w))) := by
    have hconst : Tendsto (fun _ : ℝ ↦ Complex.normSq (z - w)) (𝓝 0)
        (𝓝 (Complex.normSq (z - w))) := tendsto_const_nhds
    simpa using hconst.add (tendsto_id.pow 2)
  have hlog := (Real.continuousAt_log hnormSq).tendsto.comp harg
  convert hlog.const_mul (1 / 2 : ℝ) using 1
  · ext ε
    rfl
  · rw [← Complex.sq_norm, Real.log_pow]
    ring

/-- The radial density has the elementary antiderivative
`-ε²/(r²+ε²)`. -/
theorem hasDerivAt_radialGreenKernel_antiderivative {ε : ℝ} (hε : ε ≠ 0)
    (r : ℝ) :
    HasDerivAt (fun x : ℝ ↦ -ε ^ 2 / (x ^ 2 + ε ^ 2))
      (r * radialGreenKernel ε r) r := by
  have hden : r ^ 2 + ε ^ 2 ≠ 0 := by
    positivity
  have hdenDeriv : HasDerivAt (fun x : ℝ ↦ x ^ 2 + ε ^ 2) (2 * r) r := by
    simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using
      (((hasDerivAt_id r).pow 2).add_const (ε ^ 2))
  have h : HasDerivAt (fun x : ℝ ↦ -ε ^ 2 / (x ^ 2 + ε ^ 2))
      ((0 * (r ^ 2 + ε ^ 2) - (-ε ^ 2) * (2 * r)) /
        (r ^ 2 + ε ^ 2) ^ 2) r := by
    exact (hasDerivAt_const r (-ε ^ 2)).div hdenDeriv hden
  apply h.congr_deriv
  unfold radialGreenKernel
  field_simp [hden]
  ring

/-- The radial mass integral is one.  Multiplication by the angular length
`2π` gives the full planar mass of the Green density. -/
theorem integral_Ioi_mul_radialGreenKernel {ε : ℝ} (hε : ε ≠ 0) :
    ∫ r in Ioi (0 : ℝ), r * radialGreenKernel ε r = 1 := by
  let F : ℝ → ℝ := fun r ↦ -ε ^ 2 / (r ^ 2 + ε ^ 2)
  have hderiv : ∀ r ∈ Ici (0 : ℝ),
      HasDerivAt F (r * radialGreenKernel ε r) r := by
    intro r hr
    exact hasDerivAt_radialGreenKernel_antiderivative hε r
  have hnonneg : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * radialGreenKernel ε r := by
    intro r hr
    exact mul_nonneg hr.le (by unfold radialGreenKernel; positivity)
  have hdenom : Tendsto (fun r : ℝ ↦ r ^ 2 + ε ^ 2) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (max b 1)] with r hr
    have hrb : b ≤ r := le_trans (le_max_left _ _) hr
    have hrone : 1 ≤ r := le_trans (le_max_right _ _) hr
    nlinarith [sq_nonneg ε]
  have hlim : Tendsto F atTop (𝓝 0) := by
    exact hdenom.const_div_atTop (-ε ^ 2)
  have hFTC := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg hlim
  simpa [F, hε] using hFTC

/-- The exact mass inside a radial interval.  This is the quantitative
concentration estimate used by the approximate-identity argument. -/
theorem integral_Ioc_mul_radialGreenKernel {ε R : ℝ} (hε : ε ≠ 0)
    (hR : 0 ≤ R) :
    ∫ r in Ioc (0 : ℝ) R, r * radialGreenKernel ε r =
      R ^ 2 / (R ^ 2 + ε ^ 2) := by
  let F : ℝ → ℝ := fun r ↦ -ε ^ 2 / (r ^ 2 + ε ^ 2)
  have hderiv : ∀ r ∈ Icc (0 : ℝ) R,
      HasDerivAt F (r * radialGreenKernel ε r) r := by
    intro r hr
    exact hasDerivAt_radialGreenKernel_antiderivative hε r
  have hcont : ContinuousOn F (Icc (0 : ℝ) R) := by
    intro r hr
    apply ContinuousAt.continuousWithinAt
    dsimp only [F]
    fun_prop (disch := positivity)
  have hcont_integrand : ContinuousOn
      (fun r ↦ r * radialGreenKernel ε r) (Icc (0 : ℝ) R) := by
    intro r hr
    apply ContinuousAt.continuousWithinAt
    unfold radialGreenKernel
    fun_prop (disch := positivity)
  have hint : IntervalIntegrable (fun r ↦ r * radialGreenKernel ε r) volume 0 R :=
    hcont_integrand.intervalIntegrable_of_Icc hR
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR hcont
    (fun r hr ↦ hderiv r ⟨hr.1.le, hr.2.le⟩) hint
  rw [← intervalIntegral.integral_of_le hR, hFTC]
  simp only [F]
  field_simp
  ring

/-! ## Planar mass -/

/-- The centered regularized Green density has total planar mass `2π`.
This is the normalization in `Δ log ‖z‖ = 2π δ₀`. -/
theorem integral_regularizedGreenKernel_zero {ε : ℝ} (hε : ε ≠ 0) :
    ∫ z : ℂ, regularizedGreenKernel ε 0 z = 2 * Real.pi := by
  calc
    ∫ z : ℂ, regularizedGreenKernel ε 0 z =
        ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 * radialGreenKernel ε |p.1| := by
      rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
      simp_rw [regularizedGreenKernel_eq_radial, sub_zero,
        Complex.norm_polarCoord_symm, smul_eq_mul]
    _ = (∫ r in Ioi (0 : ℝ), r * radialGreenKernel ε r) *
        ∫ _θ in Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      rw [← setIntegral_prod_mul, Measure.volume_eq_prod]
      refine setIntegral_congr_fun
        (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp ↦ ?_
      rw [abs_of_pos hp.1]
      ring
    _ = 2 * Real.pi := by
      rw [integral_Ioi_mul_radialGreenKernel hε]
      rw [integral_const]
      simp only [measureReal_restrict_apply MeasurableSet.univ, univ_inter, one_smul,
        one_mul]
      rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_nonneg])]
      ring

/-- Translation does not change the `2π` mass of the regularized Green
density. -/
theorem integral_regularizedGreenKernel {ε : ℝ} (hε : ε ≠ 0) (w : ℂ) :
    ∫ z : ℂ, regularizedGreenKernel ε w z = 2 * Real.pi := by
  calc
    ∫ z : ℂ, regularizedGreenKernel ε w z =
        ∫ z : ℂ, regularizedGreenKernel ε 0 (z - w) := by
      congr 1
      funext z
      simp [regularizedGreenKernel]
    _ = ∫ z : ℂ, regularizedGreenKernel ε 0 z := by
      exact integral_sub_right_eq_self _ w
    _ = 2 * Real.pi := integral_regularizedGreenKernel_zero hε

/-- For `ε ≠ 0`, the regularized Green density is integrable on the whole
plane. -/
theorem integrable_regularizedGreenKernel {ε : ℝ} (hε : ε ≠ 0) (w : ℂ) :
    Integrable (regularizedGreenKernel ε w) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_regularizedGreenKernel hε w]
  positivity

/-- Exact centered mass inside a closed ball.  For fixed positive radius this
tends to `2π` as `ε → 0`. -/
theorem integral_closedBall_regularizedGreenKernel_zero {ε R : ℝ}
    (hε : ε ≠ 0) (hR : 0 ≤ R) :
    ∫ z : ℂ in Metric.closedBall 0 R, regularizedGreenKernel ε 0 z =
      2 * Real.pi * (R ^ 2 / (R ^ 2 + ε ^ 2)) := by
  rw [← integral_indicator measurableSet_closedBall]
  calc
    ∫ z : ℂ, (Metric.closedBall 0 R).indicator
        (regularizedGreenKernel ε 0) z =
        ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          ((Iic R).indicator (fun r ↦ r * radialGreenKernel ε r) p.1) * 1 := by
      rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
      refine setIntegral_congr_fun
        (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp ↦ ?_
      have hpr : 0 < p.1 := hp.1
      have hnorm : ‖(Complex.polarCoord.symm p : ℂ)‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hpr]
      have hmem : (Complex.polarCoord.symm p : ℂ) ∈ Metric.closedBall 0 R ↔
          p.1 ≤ R := by
        simp [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm,
          abs_of_pos hpr]
      by_cases hpR : p.1 ≤ R
      · rw [Set.indicator_of_mem (hmem.mpr hpR)]
        have hpRic : p.1 ∈ Iic R := hpR
        rw [Set.indicator_of_mem hpRic]
        simp only [smul_eq_mul, mul_one]
        rw [regularizedGreenKernel_eq_radial, sub_zero, hnorm]
      · rw [Set.indicator_of_notMem (hmem.not.mpr hpR)]
        have hpRic : p.1 ∉ Iic R := by simpa using hpR
        rw [Set.indicator_of_notMem hpRic]
        simp
    _ = (∫ r in Ioi (0 : ℝ),
          (Iic R).indicator (fun r ↦ r * radialGreenKernel ε r) r) *
        ∫ _θ in Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      rw [← setIntegral_prod_mul, Measure.volume_eq_prod]
    _ = 2 * Real.pi * (R ^ 2 / (R ^ 2 + ε ^ 2)) := by
      have hrad :
          ∫ r in Ioi (0 : ℝ),
              (Iic R).indicator (fun r ↦ r * radialGreenKernel ε r) r =
            ∫ r in Ioc (0 : ℝ) R, r * radialGreenKernel ε r := by
        rw [setIntegral_indicator measurableSet_Iic]
        congr 1
      rw [hrad, integral_Ioc_mul_radialGreenKernel hε hR, integral_const]
      simp only [measureReal_restrict_apply MeasurableSet.univ, univ_inter, one_smul]
      rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_nonneg])]
      ring

theorem abs_regularizedLogKernel_le {ε : ℝ} (_hε : ε ≠ 0)
    (hεsq : ε ^ 2 ≤ 1) {w z : ℂ} (hzw : z ≠ w) :
    |regularizedLogKernel ε w z| ≤
      |Real.log ‖w - z‖| + ‖w - z‖ ^ 2 + 1 := by
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr hzw.symm
  have hrpos : 0 < ‖w - z‖ := norm_pos_iff.mpr hwz
  have hnormSq : Complex.normSq (z - w) = ‖w - z‖ ^ 2 := by
    rw [← Complex.sq_norm, norm_sub_rev]
  have hargpos : 0 < ‖w - z‖ ^ 2 + ε ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hrpos) (sq_nonneg ε)
  have hmono : Real.log (‖w - z‖ ^ 2) ≤
      Real.log (‖w - z‖ ^ 2 + ε ^ 2) :=
    Real.log_le_log (sq_pos_of_pos hrpos) (le_add_of_nonneg_right (sq_nonneg ε))
  rw [Real.log_pow] at hmono
  have hlower : Real.log ‖w - z‖ ≤ regularizedLogKernel ε w z := by
    rw [regularizedLogKernel, hnormSq]
    norm_num at hmono ⊢
    nlinarith
  have hlogupper := Real.log_le_sub_one_of_pos hargpos
  have hupper : regularizedLogKernel ε w z ≤ ‖w - z‖ ^ 2 + 1 := by
    rw [regularizedLogKernel, hnormSq]
    nlinarith [sq_nonneg ‖w - z‖]
  rw [abs_le]
  constructor
  · calc
      -(|Real.log ‖w - z‖| + ‖w - z‖ ^ 2 + 1) ≤ Real.log ‖w - z‖ := by
        linarith [neg_abs_le (Real.log ‖w - z‖), sq_nonneg ‖w - z‖]
      _ ≤ regularizedLogKernel ε w z := hlower
  · exact hupper.trans (by linarith [abs_nonneg (Real.log ‖w - z‖)])

/-- The normalized unit-scale Green peak used by the approximate-identity theorem. -/
def normalizedGreenPeak (z : ℂ) : ℝ :=
  regularizedGreenKernel 1 0 z / (2 * Real.pi)

theorem normalizedGreenPeak_nonneg (z : ℂ) : 0 ≤ normalizedGreenPeak z := by
  exact div_nonneg (regularizedGreenKernel_nonneg 1 0 z) (by positivity)

theorem integral_normalizedGreenPeak :
    ∫ z : ℂ, normalizedGreenPeak z = 1 := by
  rw [show normalizedGreenPeak = fun z : ℂ ↦
    regularizedGreenKernel 1 0 z / (2 * Real.pi) by rfl]
  rw [integral_div, integral_regularizedGreenKernel_zero one_ne_zero]
  field_simp

theorem tendsto_normalizedGreenPeak_tail :
    Tendsto (fun z : ℂ ↦ ‖z‖ ^ finrank ℝ ℂ * normalizedGreenPeak z)
      (cobounded ℂ) (𝓝 0) := by
  have hnormSq : Tendsto (fun z : ℂ ↦ ‖z‖ ^ 2) (cobounded ℂ) atTop :=
    (tendsto_pow_atTop (by norm_num)).comp tendsto_norm_cobounded_atTop
  have hden : Tendsto (fun z : ℂ ↦ Real.pi * ‖z‖ ^ 2) (cobounded ℂ) atTop :=
    hnormSq.const_mul_atTop Real.pi_pos
  have hupper : Tendsto (fun z : ℂ ↦ 1 / (Real.pi * ‖z‖ ^ 2))
      (cobounded ℂ) (𝓝 0) := tendsto_const_nhds.div_atTop hden
  apply squeeze_zero' (g := fun z : ℂ ↦ 1 / (Real.pi * ‖z‖ ^ 2))
  · exact Eventually.of_forall fun z ↦
      mul_nonneg (pow_nonneg (norm_nonneg _) _) (normalizedGreenPeak_nonneg z)
  · filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with z hz
    rw [Complex.finrank_real_complex]
    simp only [normalizedGreenPeak, regularizedGreenKernel, sub_zero, one_pow,
      mul_one, Complex.sq_norm]
    have hzpos : 0 < ‖z‖ := zero_lt_one.trans_le hz
    have hpi : 0 < Real.pi := Real.pi_pos
    rw [← Complex.sq_norm]
    have hleft :
        ‖z‖ ^ 2 * (2 / (‖z‖ ^ 2 + 1) ^ 2 / (2 * Real.pi)) =
          ‖z‖ ^ 2 / (Real.pi * (‖z‖ ^ 2 + 1) ^ 2) := by
      field_simp
    rw [hleft]
    apply (div_le_div_iff₀
      (mul_pos hpi (sq_pos_of_pos (by positivity : 0 < ‖z‖ ^ 2 + 1)))
      (mul_pos hpi (pow_pos hzpos 2))).2
    nlinarith [sq_nonneg (‖z‖ ^ 2)]
  · exact hupper

theorem tendsto_normalized_regularizedGreenKernel_mul
    {g : ℂ → ℝ} (hg : Integrable g) (hgc : Continuous g) (w : ℂ) :
    Tendsto (fun c : ℝ ↦ ∫ z : ℂ,
      (regularizedGreenKernel c⁻¹ w z / (2 * Real.pi)) * g z)
      atTop (𝓝 (g w)) := by
  have hpeak := tendsto_integral_comp_smul_smul_of_integrable'
    (x₀ := w) normalizedGreenPeak_nonneg integral_normalizedGreenPeak
    tendsto_normalizedGreenPeak_tail hg hgc.continuousAt
  apply hpeak.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  congr 1
  funext z
  simp only [Complex.finrank_real_complex, normalizedGreenPeak, smul_eq_mul]
  unfold regularizedGreenKernel
  have hcne : c ≠ 0 := hc.ne'
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.smul_re, Complex.smul_im, sub_zero]
  field_simp
  ring

/-- Dominated convergence on the compact support of `Δf`. -/
private theorem continuous_laplacian_for_green {f : ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) : Continuous (Δ f) := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  have hbase : Continuous (fun x ↦ iteratedFDeriv ℝ 2 f x) :=
    hf.continuous_iteratedFDeriv le_rfl
  fun_prop

private theorem hasCompactSupport_laplacian_for_green {f : ℂ → ℝ}
    (hfc : HasCompactSupport f) : HasCompactSupport (Δ f) := by
  apply hfc.mono'
  intro z hz
  apply support_iteratedFDeriv_subset (𝕜 := ℝ) (f := f) 2
  intro hzero
  apply hz
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp [hzero]

theorem tendsto_integral_laplacian_mul_regularizedLogKernel_inv_nat
    (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (w : ℂ) :
    Tendsto (fun n : ℕ ↦ ∫ z : ℂ, Δ f z *
      regularizedLogKernel (1 / ((n : ℝ) + 1)) w z)
      atTop (𝓝 (∫ z : ℂ, Δ f z * Real.log ‖w - z‖)) := by
  let L : ℂ → ℝ := Δ f
  have hLcont : Continuous L := continuous_laplacian_for_green hf
  have hLcomp : HasCompactSupport L := hasCompactSupport_laplacian_for_green hfc
  obtain ⟨C, hC⟩ := hLcont.bounded_above_of_compact_support hLcomp
  have hCnonneg : 0 ≤ C := (norm_nonneg (L 0)).trans (hC 0)
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
    hLcomp.isCompact.isBounded
  let B : Set ℂ := Metric.closedBall 0 R
  let q : ℂ → ℝ := fun z ↦ logKernelSq w z + (‖w - z‖ ^ 2 + 2)
  let bound : ℂ → ℝ := B.indicator (fun z ↦ C * q z)
  have hq : IntegrableOn q B := by
    have hlog : IntegrableOn (logKernelSq w) B := by
      simpa [B] using integrableOn_logKernelSq_closedBall R w
    have hpoly : IntegrableOn (fun z : ℂ ↦ ‖w - z‖ ^ 2 + 2) B := by
      exact (by fun_prop : Continuous (fun z : ℂ ↦ ‖w - z‖ ^ 2 + 2)).continuousOn
        |>.integrableOn_compact (isCompact_closedBall (0 : ℂ) R)
    unfold q
    exact hlog.add hpoly
  have hbound_int : Integrable bound := by
    have hCq : IntegrableOn (fun z ↦ C * q z) B := hq.const_mul C
    exact hCq.integrable_indicator measurableSet_closedBall
  have hε (n : ℕ) : 1 / ((n : ℝ) + 1) ≠ 0 := by positivity
  have hεsq (n : ℕ) : (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 := by
    have hpos : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    have hone : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      exact_mod_cast Nat.le_add_left 1 n
    simpa using (sq_le_sq₀ hpos zero_le_one).2 hone
  have hF_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun z : ℂ ↦ L z * regularizedLogKernel (1 / ((n : ℝ) + 1)) w z) := by
    intro n
    exact (hLcont.mul (continuous_regularizedLogKernel (hε n) w)).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ z : ℂ,
      ‖L z * regularizedLogKernel (1 / ((n : ℝ) + 1)) w z‖ ≤ bound z := by
    intro n
    filter_upwards [show ∀ᵐ z : ℂ ∂volume, z ≠ w by rw [ae_iff]; simp] with z hzw
    by_cases hzB : z ∈ B
    · simp only [bound, Set.indicator_of_mem hzB, Real.norm_eq_abs, abs_mul]
      have hu := abs_regularizedLogKernel_le (hε n) (hεsq n) hzw
      have habslog : |Real.log ‖w - z‖| ≤ (Real.log ‖w - z‖) ^ 2 + 1 := by
        nlinarith [sq_nonneg (|Real.log ‖w - z‖| - 1),
          sq_abs (Real.log ‖w - z‖)]
      have huq : |regularizedLogKernel (1 / ((n : ℝ) + 1)) w z| ≤ q z := by
        unfold q logKernelSq
        exact hu.trans (by linarith)
      exact mul_le_mul (hC z) huq (abs_nonneg _) hCnonneg
    · have hznot : z ∉ tsupport L := fun hz ↦ hzB (hR hz)
      have hLzero : L z = 0 := by
        by_contra hne
        exact hznot (subset_closure hne)
      simp [bound, hzB, hLzero]
  have heps : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : ∀ᵐ z : ℂ, Tendsto
      (fun n : ℕ ↦ L z * regularizedLogKernel (1 / ((n : ℝ) + 1)) w z)
      atTop (𝓝 (L z * Real.log ‖w - z‖)) := by
    filter_upwards [show ∀ᵐ z : ℂ ∂volume, z ≠ w by rw [ae_iff]; simp] with z hzw
    simpa only [Function.comp_apply, norm_sub_rev] using tendsto_const_nhds.mul
      ((tendsto_regularizedLogKernel_zero hzw).comp heps)
  simpa only [L] using tendsto_integral_of_dominated_convergence bound hF_meas
    hbound_int hbound hlim

/-- The single-root distributional Green identity, in integral form. -/
theorem integral_laplacian_mul_logKernel_eq_two_pi_mul
    (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (w : ℂ) :
    (∫ z : ℂ, Δ f z * Real.log ‖w - z‖) = 2 * Real.pi * f w := by
  let cseq : ℕ → ℝ := fun n ↦ (n : ℝ) + 1
  have hcseq : Tendsto cseq atTop atTop := by
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hfint : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
  have hpeak := (tendsto_normalized_regularizedGreenKernel_mul
    hfint hf.continuous w).comp hcseq
  have hreg (n : ℕ) :
      (∫ z : ℂ, Δ f z * regularizedLogKernel (1 / ((n : ℝ) + 1)) w z) /
          (2 * Real.pi) =
        ∫ z : ℂ, (regularizedGreenKernel (1 / ((n : ℝ) + 1)) w z /
          (2 * Real.pi)) * f z := by
    have hn : 1 / ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [integral_laplacian_mul_regularizedLogKernel f hf hfc hn w]
    rw [← integral_div]
    congr 1
    funext z
    ring
  have hright : Tendsto (fun n : ℕ ↦
      (∫ z : ℂ, Δ f z * regularizedLogKernel (1 / ((n : ℝ) + 1)) w z) /
        (2 * Real.pi)) atTop (𝓝 (f w)) := by
    apply hpeak.congr'
    filter_upwards with n
    simpa only [Function.comp_apply, cseq, one_div] using (hreg n).symm
  have hleft := (tendsto_integral_laplacian_mul_regularizedLogKernel_inv_nat
    f hf hfc w).div_const (2 * Real.pi)
  have hunique := tendsto_nhds_unique hleft hright
  have hmul := (div_eq_iff (by positivity : 2 * Real.pi ≠ 0)).mp hunique
  simpa [mul_comm] using hmul

/-- Tao--Vu §3.6, single-root Green--Girko identity. -/
theorem green_identity_single_root
    (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (w : ℂ) :
    f w = (1 / (2 * Real.pi)) *
      ∫ z : ℂ, Δ f z * Real.log ‖w - z‖ := by
  rw [integral_laplacian_mul_logKernel_eq_two_pi_mul f hf hfc w]
  field_simp

/-- The singular Green integrand is absolutely integrable. -/
theorem integrable_laplacian_mul_logKernel
    (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (w : ℂ) :
    Integrable (fun z : ℂ ↦ Δ f z * Real.log ‖w - z‖) := by
  let L : ℂ → ℝ := Δ f
  have hLcont : Continuous L := continuous_laplacian_for_green hf
  have hLcomp : HasCompactSupport L := hasCompactSupport_laplacian_for_green hfc
  obtain ⟨C, hC⟩ := hLcont.bounded_above_of_compact_support hLcomp
  have hCnonneg : 0 ≤ C := (norm_nonneg (L 0)).trans (hC 0)
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
    hLcomp.isCompact.isBounded
  let B : Set ℂ := Metric.closedBall 0 R
  let q : ℂ → ℝ := fun z ↦ logKernelSq w z + (‖w - z‖ ^ 2 + 2)
  let bound : ℂ → ℝ := B.indicator (fun z ↦ C * q z)
  have hq : IntegrableOn q B := by
    have hlog : IntegrableOn (logKernelSq w) B := by
      simpa [B] using integrableOn_logKernelSq_closedBall R w
    have hpoly : IntegrableOn (fun z : ℂ ↦ ‖w - z‖ ^ 2 + 2) B := by
      exact (by fun_prop : Continuous (fun z : ℂ ↦ ‖w - z‖ ^ 2 + 2)).continuousOn
        |>.integrableOn_compact (isCompact_closedBall (0 : ℂ) R)
    unfold q
    exact hlog.add hpoly
  have hbound_int : Integrable bound := by
    have hCq : IntegrableOn (fun z ↦ C * q z) B := hq.const_mul C
    exact hCq.integrable_indicator measurableSet_closedBall
  apply hbound_int.mono'
  · exact (hLcont.aestronglyMeasurable.mul
      (((measurable_const.sub measurable_id).norm.log).aestronglyMeasurable))
  · filter_upwards with z
    change ‖L z * Real.log ‖w - z‖‖ ≤ bound z
    by_cases hzB : z ∈ B
    · simp only [bound, Set.indicator_of_mem hzB, Real.norm_eq_abs, abs_mul]
      have habslog : |Real.log ‖w - z‖| ≤ (Real.log ‖w - z‖) ^ 2 + 1 := by
        nlinarith [sq_nonneg (|Real.log ‖w - z‖| - 1),
          sq_abs (Real.log ‖w - z‖)]
      have hlogq : |Real.log ‖w - z‖| ≤ q z := by
        unfold q logKernelSq
        nlinarith [sq_nonneg ‖w - z‖]
      exact mul_le_mul (hC z) hlogq (abs_nonneg _) hCnonneg
    · have hznot : z ∉ tsupport L := fun hz ↦ hzB (hR hz)
      have hLzero : L z = 0 := by
        by_contra hne
        exact hznot (subset_closure hne)
      simp [bound, hzB, hLzero]

/-! ## Finite spectra -/

/-- The occurrence-type sum used in `multisetAverage` is the ordinary
multiset map-and-sum. -/
private theorem sum_occurrences_eq_map_sum {α : Type*} [DecidableEq α]
    (s : Multiset α) (g : α → ℝ) :
    (∑ x : ↥s, g (x : α)) = (s.map g).sum := by
  rw [← Multiset.map_univ]
  rfl

theorem multisetAverage_eq_map_sum {α : Type*} [DecidableEq α]
    (s : Multiset α) (g : α → ℝ) :
    multisetAverage s g = (s.map g).sum / (s.card : ℝ) := by
  unfold multisetAverage
  rw [sum_occurrences_eq_map_sum]

/-- Absolute integrability after averaging the logarithmic kernel over a
finite multiset, with multiplicities. -/
theorem integrable_laplacian_mul_multisetLogPotential
    (s : Multiset ℂ) (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Integrable (fun z : ℂ ↦ Δ f z * multisetLogPotential s z) := by
  classical
  have hsum (t : Multiset ℂ) : Integrable (fun z : ℂ ↦
      Δ f z * (t.map fun w ↦ Real.log ‖w - z‖).sum) := by
    induction t using Multiset.induction_on with
    | empty => simp
    | cons w t iht =>
        apply ((integrable_laplacian_mul_logKernel f hf hfc w).add iht).congr
        filter_upwards with z
        simp only [Pi.add_apply, Multiset.map_cons, Multiset.sum_cons, mul_add]
  have hdiv := (hsum s).div_const (s.card : ℝ)
  apply hdiv.congr
  filter_upwards with z
  rw [multisetLogPotential, multisetAverage_eq_map_sum]
  ring

/-- The single-root Green identity averaged over a finite multiset. -/
theorem green_identity_multiset
    (s : Multiset ℂ) (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    multisetAverage s f = (1 / (2 * Real.pi)) *
      ∫ z : ℂ, Δ f z * multisetLogPotential s z := by
  classical
  have hsum (t : Multiset ℂ) : Integrable (fun z : ℂ ↦
      Δ f z * (t.map fun w ↦ Real.log ‖w - z‖).sum) := by
    induction t using Multiset.induction_on with
    | empty => simp
    | cons w t iht =>
        apply ((integrable_laplacian_mul_logKernel f hf hfc w).add iht).congr
        filter_upwards with z
        simp only [Pi.add_apply, Multiset.map_cons, Multiset.sum_cons, mul_add]
  have hsumIntegral (t : Multiset ℂ) :
      (∫ z : ℂ, Δ f z * (t.map fun w ↦ Real.log ‖w - z‖).sum) =
        (t.map fun w ↦ ∫ z : ℂ, Δ f z * Real.log ‖w - z‖).sum := by
    induction t using Multiset.induction_on with
    | empty => simp
    | cons w t iht =>
        simp only [Multiset.map_cons, Multiset.sum_cons, mul_add]
        rw [integral_add (integrable_laplacian_mul_logKernel f hf hfc w) (hsum t), iht]
  have hinter :
      (∫ z : ℂ, Δ f z * multisetLogPotential s z) =
        (s.map fun w ↦ ∫ z : ℂ, Δ f z * Real.log ‖w - z‖).sum /
          (s.card : ℝ) := by
    unfold multisetLogPotential
    simp_rw [multisetAverage_eq_map_sum]
    calc
      (∫ z : ℂ, Δ f z *
          ((s.map fun w ↦ Real.log ‖w - z‖).sum / (s.card : ℝ))) =
          ∫ z : ℂ, (Δ f z *
            (s.map fun w ↦ Real.log ‖w - z‖).sum) / (s.card : ℝ) := by
        congr 1
        funext z
        ring
      _ = (∫ z : ℂ, Δ f z *
          (s.map fun w ↦ Real.log ‖w - z‖).sum) / (s.card : ℝ) := by
        rw [integral_div]
      _ = (s.map fun w ↦ ∫ z : ℂ,
          Δ f z * Real.log ‖w - z‖).sum / (s.card : ℝ) := by
        rw [hsumIntegral]
  rw [hinter, multisetAverage_eq_map_sum]
  simp_rw [green_identity_single_root f hf hfc]
  rw [Multiset.sum_map_mul_left]
  ring

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `realEsdTest` is the multiset average over characteristic roots. -/
theorem realEsdTest_eq_multisetAverage (A : Matrix n n ℂ) (g : ℂ → ℝ) :
    realEsdTest A g = multisetAverage (eigenvalueMultiset A) g := by
  rw [multisetAverage_eq_map_sum]
  simp [realEsdTest, realSpectralSum, card_eigenvalueMultiset]

/-- Absolute integrability of the matrix empirical log-potential Green
integrand. -/
theorem integrable_laplacian_mul_realEsdLogPotential [Nonempty n]
    (A : Matrix n n ℂ) (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Integrable (fun z : ℂ ↦ Δ f z *
      realEsdTest A (fun w ↦ Real.log ‖w - z‖)) := by
  have h := integrable_laplacian_mul_multisetLogPotential
    (eigenvalueMultiset A) f hf hfc
  apply h.congr
  filter_upwards with z
  rw [realEsdTest_eq_multisetAverage]
  rfl

/-- Green--Girko identity for the empirical spectral test functional. -/
theorem green_identity_realEsdTest [Nonempty n]
    (A : Matrix n n ℂ) (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    realEsdTest A f = (1 / (2 * Real.pi)) *
      ∫ z : ℂ, Δ f z * realEsdTest A
        (fun w ↦ Real.log ‖w - z‖) := by
  rw [realEsdTest_eq_multisetAverage]
  rw [green_identity_multiset (eigenvalueMultiset A) f hf hfc]
  congr 2
  funext z
  rw [realEsdTest_eq_multisetAverage]
  rfl

end TaoVuReplacement

