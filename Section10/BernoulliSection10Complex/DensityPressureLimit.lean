import BernoulliSection10Complex.FullBlockHighBandProfile
import BernoulliSection10Complex.PhysicalInputLaw
import BernoulliSection10Complex.PressureCalibration

/-! # Equation (10.35), with the short anchor supplied by Section 3 -/

open Filter MeasureTheory Topology

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open SourceInputs ShortRingAnchor ProbabilityLimits

/-- Proposition 10.1 for the literal finite physical-row laws, with every
variance-profile and comparison-model condition discharged internally. -/
theorem density_high_band_ring_log_limit
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ) (hSource : Section3Inputs μ L)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (ω : ℝ) (hω : 0 < ω) (hω1 : ω < 1 / 9)
    (hhigh : ∀ᶠ n in atTop, (((s n + 3) * W n : ℕ) : ℝ) ^ (8 / 9 + ω) ≤ W n)
    (z : ℂ) :
    letI := hμ.toIsProbabilityMeasure
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) μ)
      (fun n x => densityCyclicLogDet (W n) (s n) z x / (((s n + 3) * W n : ℕ) : ℝ))
      (circularLogPotential z) := by
  letI := hμ.toIsProbabilityMeasure
  exact (profile_log_converges_iff_physical_rows μ W s z (circularLogPotential z)).mp
    (fullBlockHighBand_profile_log_limit hμ h3 hSource W s hW hWtop ω hω hω1 hhigh z)

theorem densityCorePressureDensity_limit
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ) (hSource : Section3Inputs μ L)
    (W : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop) (z : ℂ) :
    Tendsto (fun n => densityCorePressureDensity μ (W n) z) atTop
      (𝓝 (circularLogPotential z)) := by
  letI := hμ.toIsProbabilityMeasure
  have hhigh := hWtop.eventually eventually_density_anchor_highBand
  have hrows := density_high_band_ring_log_limit hμ h3 hSource W
    (fun n => densityCoreSites (W n)) hW hWtop (1 / 20)
    (by norm_num) (by norm_num) hhigh z
  exact densityCorePressureDensity_tendsto_of_anchor hμ W hW hWtop z
    (circularLogPotential z) hrows

end BernoulliSection10Complex
