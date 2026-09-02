import CircularLawSection6.GaussianRadialMean
import CircularLawSection6.RawPotentialScaling
import CircularLawSection6.CompactCoreRawBridge
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Fixed positive scaling of the actual Section 5 core endpoint

Division of the planar spectral parameter by a positive real scalar
preserves null sets. The actual determinant scaling identity is integrated
using the proved Gaussian logarithmic integrability. Thus the literal
Section 5 probability limit supplies every fixed positive-scale core mean
limit, rather than an additional expectation-convergence hypothesis.
-/

open MeasureTheory Filter Topology
open CircularLawSection4
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem ae_div_real {P : ℂ → Prop} {r : ℝ} (hr : r ≠ 0)
    (hP : ∀ᵐ z ∂(volume : Measure ℂ), P z) :
    ∀ᵐ z ∂(volume : Measure ℂ), P (z / (r : ℂ)) := by
  have h := (quasiMeasurePreserving_smul (volume : Measure ℂ) (inv_ne_zero hr)).ae hP
  have heq (z : ℂ) : r⁻¹ • z = z / (r : ℂ) := by
    rw [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  simpa only [heq] using h

namespace NoncompactProfile

theorem scaledUnitCoreMean_eq_log_add_ae (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ z ∂(volume : Measure ℂ), p.scaledUnitCoreMean N H W r z =
      Real.log r + ∫ ω, p.unitCoreLogPotential N H W (z / (r : ℂ)) ω ∂gaussianProfileLaw N := by
  have hdet := ae_shifted_cyclic_det_ne_zero (gaussianProfileLaw N) N (p.unitCoreMatrix N H W)
    (fun i j => weightedCyclicMatrix_measurable N
      (maskedWeight (coreOffsets N H) (p.normalizedCoreWeight N H W)) i j)
  filter_upwards [ae_div_real hr.ne' hdet] with z hz
  have hu0 := (p.scaledUnitCoreLogDet_memLp N H W (r := 1) zero_lt_one (z / (r : ℂ))).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hu : Integrable (p.unitCoreLogPotential N H W (z / (r : ℂ))) (gaussianProfileLaw N) := by
    unfold scaledUnitCoreLogDet at hu0
    unfold unitCoreLogPotential
    simpa only [Complex.ofReal_one, one_smul] using hu0.div_const (N : ℝ)
  have heq : ∀ᵐ ω ∂gaussianProfileLaw N,
      p.scaledUnitCoreLogDet N H W r z ω / (N : ℝ) =
        Real.log r + p.unitCoreLogPotential N H W (z / (r : ℂ)) ω := by
    filter_upwards [hz] with ω hω
    simpa only [matrixRawPotential, ZMod.card, scaledUnitCoreLogDet, unitCoreLogPotential] using
      matrixRawPotential_shifted_smul (p.unitCoreMatrix N H W ω) z hr hω
  unfold scaledUnitCoreMean
  rw [← integral_div]
  calc
    _ = ∫ ω, Real.log r + p.unitCoreLogPotential N H W (z / (r : ℂ)) ω ∂gaussianProfileLaw N :=
      integral_congr_ae heq
    _ = _ := by rw [integral_add (integrable_const _) hu]; simp

theorem scaledUnitCore_mean_of_section5 (p : NoncompactProfile)
    (size band : ℕ → ℕ) (hsize : Tendsto (fun n => size n + 2) atTop atTop)
    (center : ∀ n, Fin (band n + 1)) (hfit : ∀ n, band n + 2 ≤ size n + 2)
    (hsym : ∀ n, band n + 1 = 2 * (center n).val) (W : ℕ → ℝ)
    (hSection5 : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
      (fun n => paperIndicatorSampleMeasure (size n + 2) (band n) circularComplexGaussian)
      (fun n ω => physicalLogPotential (literalIndicatorMatrix (size n + 1) (band n) (center n)
        (fun s => (Real.sqrt (p.coreBandWeight (size n + 2) (band n) (center n) (W n) s) : ℂ)) ω) z)
      (circularRadialPotential ‖z‖)) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => p.scaledUnitCoreMean (size n + 2) (center n).val (W n) r z)
        atTop (𝓝 (varianceScaledRadialPotential (r ^ 2) ‖z‖)) := by
  have hscaled := ae_all_iff.2 (fun n =>
    p.scaledUnitCoreMean_eq_log_add_ae (size n + 2) (center n).val (W n) hr)
  filter_upwards [ae_div_real hr.ne' hSection5, hscaled] with z hz hid
  have hmean := p.unitCore_mean_of_section5 size band hsize center hfit hsym W
    (z / (r : ℂ)) (circularRadialPotential ‖z / (r : ℂ)‖) hz
  have hlim := (hmean.const_add (Real.log r)).congr'
    (Eventually.of_forall fun n => (hid n).symm)
  have htarget : Real.log r + circularRadialPotential ‖z / (r : ℂ)‖ =
      varianceScaledRadialPotential (r ^ 2) ‖z‖ := by
    rw [varianceScaledRadialPotential, Real.log_pow, Real.sqrt_sq hr.le,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    ring
  simpa only [htarget] using hlim

/-- The actual Section 5 probability conclusion implies the raw core mean
limit with its size-dependent variance. No extra fixed-scale expectation
limit or radial monotonicity is supplied as an input. -/
theorem rawCore_mean_of_section5 (p : NoncompactProfile)
    (size band : ℕ → ℕ) (hsize : Tendsto (fun n => size n + 2) atTop atTop)
    (center : ∀ n, Fin (band n + 1)) (hfit : ∀ n, band n + 2 ≤ size n + 2)
    (hsym : ∀ n, band n + 1 = 2 * (center n).val) (W : ℕ → ℝ)
    (hSection5 : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
      (fun n => paperIndicatorSampleMeasure (size n + 2) (band n) circularComplexGaussian)
      (fun n ω => physicalLogPotential (literalIndicatorMatrix (size n + 1) (band n) (center n)
        (fun s => (Real.sqrt (p.coreBandWeight (size n + 2) (band n) (center n) (W n) s) : ℂ)) ω) z)
      (circularRadialPotential ‖z‖))
    {v : ℝ} (hv : 0 < v)
    (hmass : Tendsto (fun n => p.coreMass (size n + 2) (center n).val (W n)) atTop (𝓝 v)) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => (∫ ω, p.rawCoreLogDet (size n + 2) (center n).val (W n) z ω
        ∂gaussianProfileLaw (size n + 2)) / (size n + 2 : ℕ)) atTop
          (𝓝 (varianceScaledRadialPotential v ‖z‖)) := by
  apply p.gaussian_core_raw_mean_of_fixed_scales (fun n => size n + 2)
    (fun n => (center n).val) W hv hmass
    (S := Set.range (fun q : ℚ => (q : ℝ))) Rat.denseRange_cast (Set.countable_range _)
  intro r _
  by_cases hr : 0 < r
  · filter_upwards [p.scaledUnitCore_mean_of_section5 size band hsize center hfit hsym W
      hSection5 hr] with z hz
    exact fun _ => hz
  · exact ae_of_all _ (fun _ h => (hr h).elim)

end NoncompactProfile
end CircularLawSection6
