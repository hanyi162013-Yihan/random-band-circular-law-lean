import CircularLawSection6.CanonicalCoreBand
import CircularLawSection6.FixedScaleCoreBridge
import CircularLawSection6.VaryingCoreCutoff
import CircularLawSection6.LimitingProfileMass

/-! # Raw core limits and the varying cutoff normalization

For the canonical floor-radius core, the mass limit is the actual profile
integral. The raw expectation follows from the literal Section 5 probability
conclusion; its scaling and radial squeeze are proved in the imported layer.
For the cutoff expectation, only the genuine fixed-scale compact cutoff
limit remains an input. The varying normalization is discharged here.
The all-index band-fit conditions below can be obtained after discarding
the finite prefix in `canonical_floor_core_eventually_fits`.
-/

open MeasureTheory Filter Topology
open CircularLawSection4
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

theorem canonical_core_raw_mean_of_section5 (p : NoncompactProfile)
    (size : ℕ → ℕ) (hsize : Tendsto (fun n => size n + 2) atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (size n + 2 : ℕ)) atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) (hH : ∀ n, 0 < ⌊R * W n⌋₊)
    (hfit : ∀ n, 2 * ⌊R * W n⌋₊ + 1 ≤ size n + 2)
    (hSection5 : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
      (fun n => paperIndicatorSampleMeasure (size n + 2)
        (canonicalCoreBand ⌊R * W n⌋₊) circularComplexGaussian)
      (fun n ω => physicalLogPotential (literalIndicatorMatrix (size n + 1)
        (canonicalCoreBand ⌊R * W n⌋₊) (canonicalCoreCenter _ (hH n))
        (fun s => (Real.sqrt (p.coreBandWeight (size n + 2)
          (canonicalCoreBand ⌊R * W n⌋₊) (canonicalCoreCenter _ (hH n)) (W n) s) : ℂ)) ω) z)
      (circularRadialPotential ‖z‖)) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => (∫ ω, p.rawCoreLogDet (size n + 2) ⌊R * W n⌋₊ (W n) z ω
        ∂gaussianProfileLaw (size n + 2)) / (size n + 2 : ℕ)) atTop
          (𝓝 (varianceScaledRadialPotential (p.limitingCoreMass R) ‖z‖)) := by
  apply p.rawCore_mean_of_section5 size (fun n => canonicalCoreBand ⌊R * W n⌋₊)
    hsize (fun n => canonicalCoreCenter _ (hH n))
    (fun n => by simpa only [canonicalCoreBand_width (hH n)] using hfit n)
    (fun n => canonicalCoreCenter_symmetric (hH n)) W hSection5 (p.limitingCoreMass_pos hR)
  exact p.coreMass_tendsto_sparse (fun n => size n + 2) hsize W hW hWlim hsparse hR.le

theorem gaussian_core_cutoff_normalization_error (p : NoncompactProfile)
    (N H : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ) {v a : ℝ}
    (hmass : Tendsto (fun n => p.coreMass (N n) (H n) (W n)) atTop (𝓝 v))
    (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n =>
        |(∫ ω, matrixCutoffPotential (p.coreMatrix (N n) (H n) (W n) ω - z • 1) a
          ∂gaussianProfileLaw (N n)) -
          ∫ ω, matrixCutoffPotential ((Real.sqrt v : ℂ) •
            p.unitCoreMatrix (N n) (H n) (W n) ω - z • 1) a
            ∂gaussianProfileLaw (N n)|) atTop (𝓝 0) := by
  simpa only [p.coreMatrix_eq_scale_unitCoreMatrix] using
    p.gaussian_unitCore_cutoff_varying_scale N H W
      (fun n => Real.sqrt (p.coreMass (N n) (H n) (W n))) hmass.sqrt ha

theorem gaussian_core_cutoff_limit_of_fixed_scale (p : NoncompactProfile)
    (N H : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ) {v a : ℝ}
    (hmass : Tendsto (fun n => p.coreMass (N n) (H n) (W n)) atTop (𝓝 v))
    (ha : 0 < a) (target : ℂ → ℝ)
    (hfixed : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => ∫ ω, matrixCutoffPotential ((Real.sqrt v : ℂ) •
        p.unitCoreMatrix (N n) (H n) (W n) ω - z • 1) a ∂gaussianProfileLaw (N n))
        atTop (𝓝 (target z))) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => ∫ ω, matrixCutoffPotential (p.coreMatrix (N n) (H n) (W n) ω - z • 1) a
        ∂gaussianProfileLaw (N n)) atTop (𝓝 (target z)) := by
  filter_upwards [p.gaussian_core_cutoff_normalization_error N H W hmass ha, hfixed] with z hz ht
  have hd : Tendsto (fun n =>
      (∫ ω, matrixCutoffPotential (p.coreMatrix (N n) (H n) (W n) ω - z • 1) a
        ∂gaussianProfileLaw (N n)) -
      ∫ ω, matrixCutoffPotential ((Real.sqrt v : ℂ) •
        p.unitCoreMatrix (N n) (H n) (W n) ω - z • 1) a ∂gaussianProfileLaw (N n))
      atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 (by simpa only [Real.norm_eq_abs] using hz)
  simpa only [sub_add_cancel, zero_add] using hd.add ht

end CircularLawSection6.NoncompactProfile
