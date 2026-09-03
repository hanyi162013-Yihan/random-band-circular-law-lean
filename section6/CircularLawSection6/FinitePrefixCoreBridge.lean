import CircularLawSection6.CanonicalCoreLimits

/-! # Removing the finite unwrapped-core prefix

The core center only exists in the literal band parametrization once its
half-width is positive. Sparse geometry supplies a finite shift where all
dimensions fit. The verified Section 5 endpoint is used there and the
ordinary finite-shift limit equivalence restores the original sequence.
No arbitrary center or false inactive-branch filler is introduced.
-/

open MeasureTheory Filter Topology CircularLawSection4
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

def CanonicalCoreSection5Input (p : NoncompactProfile) (size : ℕ → ℕ) (W : ℕ → ℝ) (R : ℝ) : Prop :=
  ∀ K : ℕ, ∀ hH : ∀ n, 0 < ⌊R * W (n + K)⌋₊,
    (∀ n, 2 * ⌊R * W (n + K)⌋₊ + 1 ≤ size (n + K) + 2) →
    ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
      (fun n => paperIndicatorSampleMeasure (size (n + K) + 2)
        (canonicalCoreBand ⌊R * W (n + K)⌋₊) circularComplexGaussian)
      (fun n ω => physicalLogPotential (literalIndicatorMatrix (size (n + K) + 1)
        (canonicalCoreBand ⌊R * W (n + K)⌋₊) (canonicalCoreCenter _ (hH n))
        (fun s => (Real.sqrt (p.coreBandWeight (size (n + K) + 2)
          (canonicalCoreBand ⌊R * W (n + K)⌋₊) (canonicalCoreCenter _ (hH n)) (W (n + K)) s) : ℂ)) ω) z)
      (circularRadialPotential ‖z‖)

theorem canonical_core_raw_mean_of_eventual_section5 (p : NoncompactProfile)
    (size : ℕ → ℕ) (hsize : Tendsto (fun n => size n + 2) atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (size n + 2 : ℕ)) atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) (hSection5 : p.CanonicalCoreSection5Input size W R) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => (∫ ω, p.rawCoreLogDet (size n + 2) ⌊R * W n⌋₊ (W n) z ω
        ∂gaussianProfileLaw (size n + 2)) / (size n + 2 : ℕ)) atTop
          (𝓝 (varianceScaledRadialPotential (p.limitingCoreMass R) ‖z‖)) := by
  have hgeom := canonical_floor_core_eventually_fits (fun n => size n + 2)
    hsize W hW hWlim hsparse hR
  obtain ⟨K, hK⟩ := eventually_atTop.1 hgeom
  have hH (n : ℕ) : 0 < ⌊R * W (n + K)⌋₊ := (hK (n + K) (by omega)).1
  have hfit (n : ℕ) : 2 * ⌊R * W (n + K)⌋₊ + 1 ≤ size (n + K) + 2 := by
    have h := (hK (n + K) (by omega)).2
    rwa [canonicalCoreBand_width (hH n)] at h
  have hraw := p.canonical_core_raw_mean_of_section5
    (fun n => size (n + K)) (hsize.comp (tendsto_add_atTop_nat K))
    (fun n => W (n + K)) (fun n => hW (n + K)) (hWlim.comp (tendsto_add_atTop_nat K))
    (hsparse.comp (tendsto_add_atTop_nat K)) hR hH hfit (hSection5 K hH hfit)
  filter_upwards [hraw] with z hz
  exact (tendsto_add_atTop_iff_nat K).mp hz

end CircularLawSection6.NoncompactProfile
