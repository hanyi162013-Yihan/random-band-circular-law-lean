import CircularLawSection6.ClampedCoreSubsequence
import CircularLawSection6.FixedScaleCoreBridgePointwise
import CircularLawSection6.VerifiedCorePressure

/-! # Pointwise compact-core input after a finite prefix

The finite-prefix bookkeeping is unchanged from the historical a.e. API.  Its
source is now the constructed fixed-`z` Section 5 endpoint, so every positive
scale required by the deterministic dense-radius squeeze is available at the
same prescribed `z`.
-/

open MeasureTheory Filter Topology CircularLawSection4
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput)

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

def CanonicalCoreSection5InputPointwise (p : NoncompactProfile)
    (size : ℕ → ℕ) (W : ℕ → ℝ) (R : ℝ) : Prop :=
  ∀ K : ℕ, ∀ hH : ∀ n, 0 < ⌊R * W (n + K)⌋₊,
    (∀ n, 2 * ⌊R * W (n + K)⌋₊ + 1 ≤ size (n + K) + 2) →
    ∀ z : ℂ, TendstoInProbabilityTri
      (fun n => paperIndicatorSampleMeasure (size (n + K) + 2)
        (canonicalCoreBand ⌊R * W (n + K)⌋₊) circularComplexGaussian)
      (fun n ω => physicalLogPotential (literalIndicatorMatrix (size (n + K) + 1)
        (canonicalCoreBand ⌊R * W (n + K)⌋₊) (canonicalCoreCenter _ (hH n))
        (fun s => (Real.sqrt (p.coreBandWeight (size (n + K) + 2)
          (canonicalCoreBand ⌊R * W (n + K)⌋₊) (canonicalCoreCenter _ (hH n))
          (W (n + K)) s) : ℂ)) ω) z)
      (circularRadialPotential ‖z‖)

theorem canonical_core_raw_mean_of_eventual_section5_at (p : NoncompactProfile)
    (size : ℕ → ℕ) (hsize : Tendsto (fun n => size n + 2) atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (size n + 2 : ℕ)) atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R)
    (hSection5 : p.CanonicalCoreSection5InputPointwise size W R) (z : ℂ) :
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
  have hraw := p.rawCore_mean_of_section5_at
    (fun n => size (n + K)) (fun n => canonicalCoreBand ⌊R * W (n + K)⌋₊)
    (hsize.comp (tendsto_add_atTop_nat K))
    (fun n => canonicalCoreCenter _ (hH n))
    (fun n => by simpa only [canonicalCoreBand_width (hH n)] using hfit n)
    (fun n => canonicalCoreCenter_symmetric (hH n)) (fun n => W (n + K))
    (p.limitingCoreMass_pos hR)
    (p.coreMass_tendsto_sparse (fun n => size (n + K) + 2)
      (hsize.comp (tendsto_add_atTop_nat K)) (fun n => W (n + K))
      (fun n => hW (n + K)) (hWlim.comp (tendsto_add_atTop_nat K))
      (hsparse.comp (tendsto_add_atTop_nat K)) hR.le)
    (hSection5 K hH hfit) z
  exact (tendsto_add_atTop_iff_nat K).mp hraw

end CircularLawSection6.NoncompactProfile

namespace CircularLawSection6.CoreRadiusBounds

variable {p : NoncompactProfile} {R : ℝ}

theorem verifiedToCanonicalPointwise (B : CoreRadiusBounds p R) (W : ℕ → ℝ)
    (hR : 0 < R) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hBBV : BBVComparisonInput) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    p.CanonicalCoreSection5InputPointwise (subsequenceCoreSize φ)
      (fun n => W (φ (n + 1))) R := by
  intro K hH hfit z
  have h5 := B.verifiedClampedLogPotential_at W hR hWlim hBBV z
  have hψ : Tendsto (fun n => φ (n + K + 1)) atTop atTop :=
    hφ.tendsto_atTop.comp ((tendsto_add_atTop_nat 1).comp (tendsto_add_atTop_nat K))
  intro ε hε
  apply ((h5 ε hε).comp hψ).congr'
  apply Eventually.of_forall
  intro n
  have hidx : subsequenceCoreSize φ (n + K) + 1 = φ (n + K + 1) := by
    have h := subsequenceCoreSize_dimension φ hφ (n + K)
    omega
  have hfit' : 2 * ⌊R * W (φ (n + K + 1))⌋₊ + 1 ≤ φ (n + K + 1) + 1 := by
    simpa only [subsequenceCoreSize_dimension φ hφ] using hfit n
  change clampedCoreBadProbability B W (φ (n + K + 1)) z
      (circularRadialPotential ‖z‖) ε =
    literalCoreBadProbability p (subsequenceCoreSize φ (n + K) + 1)
      ⌊R * W (φ (n + K + 1))⌋₊ (hH n) (W (φ (n + K + 1))) z
      (circularRadialPotential ‖z‖) ε
  exact (B.clampedCoreBadProbability_eq_literal W (φ (n + K + 1))
    (hW _) (hH n) hfit' z (circularRadialPotential ‖z‖) ε).trans
    (literalCoreBadProbability_dimension p hidx.symm _ (hH n)
      (W (φ (n + K + 1))) z (circularRadialPotential ‖z‖) ε)

end CircularLawSection6.CoreRadiusBounds
