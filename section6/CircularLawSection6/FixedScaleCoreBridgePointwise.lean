import CircularLawSection6.FixedScaleCoreBridge
import CircularLawSection6.WeightedCyclicPointwiseNonzero

/-! # Fixed-shift compact-core mean bridge

These are the pointwise counterparts of the historical planar-a.e. bridge.
The actual Gaussian core is nonsingular at every prescribed shift, so the
scaling identity and the deterministic dense-radius squeeze introduce no
exceptional spectral parameter.
-/

open MeasureTheory Filter Topology Set
open CircularLawSection4
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

theorem scaledUnitCoreMean_eq_log_add (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    p.scaledUnitCoreMean N H W r z =
      Real.log r + ∫ ω, p.unitCoreLogPotential N H W (z / (r : ℂ)) ω
        ∂gaussianProfileLaw N := by
  have hdet := p.gaussian_unitCore_det_nonzero N H W (z / (r : ℂ))
  have hu0 := (p.scaledUnitCoreLogDet_memLp N H W (r := 1) zero_lt_one
    (z / (r : ℂ))).integrable (by norm_num)
  have hu : Integrable (p.unitCoreLogPotential N H W (z / (r : ℂ)))
      (gaussianProfileLaw N) := by
    unfold scaledUnitCoreLogDet at hu0
    unfold unitCoreLogPotential
    simpa only [Complex.ofReal_one, one_smul] using hu0.div_const (N : ℝ)
  have heq : ∀ᵐ ω ∂gaussianProfileLaw N,
      p.scaledUnitCoreLogDet N H W r z ω / (N : ℝ) =
        Real.log r + p.unitCoreLogPotential N H W (z / (r : ℂ)) ω := by
    filter_upwards [hdet] with ω hω
    simpa only [matrixRawPotential, ZMod.card, scaledUnitCoreLogDet,
      unitCoreLogPotential] using
      matrixRawPotential_shifted_smul (p.unitCoreMatrix N H W ω) z hr hω
  unfold scaledUnitCoreMean
  rw [← integral_div]
  calc
    _ = ∫ ω, Real.log r + p.unitCoreLogPotential N H W (z / (r : ℂ)) ω
        ∂gaussianProfileLaw N := integral_congr_ae heq
    _ = _ := by rw [integral_add (integrable_const _) hu]; simp

theorem gaussian_core_raw_mean_of_fixed_scales_at (p : NoncompactProfile)
    (N H : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ)
    {v : ℝ} (hv : 0 < v)
    (hmass : Tendsto (fun n => p.coreMass (N n) (H n) (W n)) atTop (𝓝 v))
    {S : Set ℝ} (hS : Dense S)
    (z : ℂ)
    (hfixed : ∀ r ∈ S, 0 < r →
      Tendsto (fun n => p.scaledUnitCoreMean (N n) (H n) (W n) r z) atTop
        (𝓝 (varianceScaledRadialPotential (r ^ 2) ‖z‖))) :
    Tendsto (fun n => (∫ ω, p.rawCoreLogDet (N n) (H n) (W n) z ω
      ∂gaussianProfileLaw (N n)) / (N n : ℝ)) atTop
      (𝓝 (varianceScaledRadialPotential v ‖z‖)) := by
  have hroot : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hcont : ContinuousAt (fun r : ℝ => varianceScaledRadialPotential (r ^ 2) ‖z‖)
      (Real.sqrt v) := by
    exact (continuousAt_varianceScaledRadialPotential
      (radius := ‖z‖) (sq_pos_of_pos hroot)).comp
      (f := fun r : ℝ => r ^ 2)
      (show ContinuousAt (fun r : ℝ => r ^ 2) (Real.sqrt v) from
        (continuous_id.pow 2).continuousAt)
  have h := tendsto_varying_radius_of_monotone_dense hS
    (fun n r => p.scaledUnitCoreMean (N n) (H n) (W n) r z)
    (fun r => varianceScaledRadialPotential (r ^ 2) ‖z‖)
    (fun n => Real.sqrt (p.coreMass (N n) (H n) (W n))) hroot hmass.sqrt
    (fun n => p.scaledUnitCoreMean_monotoneOn (N n) (H n) (W n) z)
    hfixed hcont
  simpa only [p.rawCoreMean_eq_scaledUnitCoreMean, Real.sq_sqrt hv.le] using h

theorem scaledUnitCore_mean_of_section5_at (p : NoncompactProfile)
    (size band : ℕ → ℕ) (hsize : Tendsto (fun n => size n + 2) atTop atTop)
    (center : ∀ n, Fin (band n + 1)) (hfit : ∀ n, band n + 2 ≤ size n + 2)
    (hsym : ∀ n, band n + 1 = 2 * (center n).val) (W : ℕ → ℝ)
    {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hSection5 : TendstoInProbabilityTri
      (fun n => paperIndicatorSampleMeasure (size n + 2) (band n) circularComplexGaussian)
      (fun n ω => physicalLogPotential (literalIndicatorMatrix (size n + 1) (band n)
        (center n) (fun s => (Real.sqrt (p.coreBandWeight (size n + 2) (band n)
          (center n) (W n) s) : ℂ)) ω) (z / (r : ℂ)))
      (circularRadialPotential ‖z / (r : ℂ)‖)) :
    Tendsto (fun n => p.scaledUnitCoreMean (size n + 2) (center n).val (W n) r z)
      atTop (𝓝 (varianceScaledRadialPotential (r ^ 2) ‖z‖)) := by
  have hmean := p.unitCore_mean_of_section5 size band hsize center hfit hsym W
    (z / (r : ℂ)) (circularRadialPotential ‖z / (r : ℂ)‖) hSection5
  have hlim := (hmean.const_add (Real.log r)).congr'
    (Eventually.of_forall fun n =>
      (p.scaledUnitCoreMean_eq_log_add (size n + 2) (center n).val (W n) hr z).symm)
  have htarget : Real.log r + circularRadialPotential ‖z / (r : ℂ)‖ =
      varianceScaledRadialPotential (r ^ 2) ‖z‖ := by
    rw [varianceScaledRadialPotential, Real.log_pow, Real.sqrt_sq hr.le,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    ring
  simpa only [htarget] using hlim

theorem rawCore_mean_of_section5_at (p : NoncompactProfile)
    (size band : ℕ → ℕ) (hsize : Tendsto (fun n => size n + 2) atTop atTop)
    (center : ∀ n, Fin (band n + 1)) (hfit : ∀ n, band n + 2 ≤ size n + 2)
    (hsym : ∀ n, band n + 1 = 2 * (center n).val) (W : ℕ → ℝ)
    {v : ℝ} (hv : 0 < v)
    (hmass : Tendsto (fun n => p.coreMass (size n + 2) (center n).val (W n))
      atTop (𝓝 v))
    (hSection5 : ∀ z : ℂ, TendstoInProbabilityTri
      (fun n => paperIndicatorSampleMeasure (size n + 2) (band n) circularComplexGaussian)
      (fun n ω => physicalLogPotential (literalIndicatorMatrix (size n + 1) (band n)
        (center n) (fun s => (Real.sqrt (p.coreBandWeight (size n + 2) (band n)
          (center n) (W n) s) : ℂ)) ω) z)
      (circularRadialPotential ‖z‖))
    (z : ℂ) :
    Tendsto (fun n => (∫ ω, p.rawCoreLogDet (size n + 2) (center n).val (W n) z ω
      ∂gaussianProfileLaw (size n + 2)) / (size n + 2 : ℕ)) atTop
      (𝓝 (varianceScaledRadialPotential v ‖z‖)) := by
  apply p.gaussian_core_raw_mean_of_fixed_scales_at (fun n => size n + 2)
    (fun n => (center n).val) W hv hmass Rat.denseRange_cast z
  intro r _ hr
  exact p.scaledUnitCore_mean_of_section5_at size band hsize center hfit hsym W hr z
    (hSection5 (z / (r : ℂ)))

end CircularLawSection6.NoncompactProfile
