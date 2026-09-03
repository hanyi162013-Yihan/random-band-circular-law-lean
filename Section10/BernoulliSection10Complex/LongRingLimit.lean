import BernoulliSection10Complex.DensityPressureLimit
import BernoulliSection10Complex.LongPressureError
import BernoulliSection10.CellDimensionLimit

/-! # The complete long-ring log-determinant limit, (10.50)--(10.55) -/

open Filter MeasureTheory Topology

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open SourceInputs ShortRingAnchor ProbabilityLimits

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem density_long_ring_log_limit
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ) (hSource : Section3Inputs μ L)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, (W n : ℝ) ^ (101 / 100 : ℝ) ≤ ((s n + 3) * W n : ℕ))
    (z : ℂ) :
    letI := hμ.toIsProbabilityMeasure
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) μ)
      (fun n x => densityCyclicLogDet (W n) (s n) z x / (((s n + 3) * W n : ℕ) : ℝ))
      (circularLogPotential z) := by
  letI := hμ.toIsProbabilityMeasure
  let N := fun n => (s n + 3) * W n
  let K := fun n => densityCellCount (s n + 3) (W n)
  let q := fun n => densityRemainderSites (s n + 3) (W n)
  have hs (n : ℕ) : K n * densityCellSites (W n) + q n = s n :=
    Nat.add_right_cancel (densityCell_partition (m := s n + 3) (by omega) (W n))
  have herror := tendsto_cyclicStitchedPressureError_div L z W K q N hWtop
    (Eventually.of_forall fun n => (densityRemainderSites_lt (s n + 3) (W n)).le)
    (Eventually.of_forall fun n => by rw [hs n]) hlong
  have hratio := tendsto_densityCell_dimension_ratio (m := fun n => s n + 3) hWtop
    (Eventually.of_forall fun _ => by omega) (by simpa only [Nat.cast_mul] using hlong)
  have hcore := densityCorePressureDensity_limit hμ h3 hSource W hW hWtop z
  have he (n : ℕ) :
      ((K n : ℝ) * densityAnchorSize (W n) / (((s n + 3 : ℕ) : ℝ) * W n)) *
        densityCorePressureDensity μ (W n) z =
      (K n : ℝ) * densityMaxCorePressure μ (W n) z / (N n : ℝ) := by
    have hne : (densityAnchorSize (W n) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (densityAnchorSize_pos (hW n)).ne'
    simp only [densityCorePressureDensity, N, Nat.cast_mul]
    field_simp
  have hcenter : Tendsto
      (fun n => (K n : ℝ) * densityMaxCorePressure μ (W n) z / (N n : ℝ))
      atTop (𝓝 (circularLogPotential z)) := by
    have hproduct : Tendsto
        (fun n => ((K n : ℝ) * densityAnchorSize (W n) /
          (((s n + 3 : ℕ) : ℝ) * W n)) * densityCorePressureDensity μ (W n) z)
        atTop (𝓝 (circularLogPotential z)) := by
      simpa only [one_mul] using hratio.mul hcore
    exact hproduct.congr (fun n => he n)
  apply tendstoInProbabilityTri_of_center_tendsto_and_L1_close
    (fun n => intervalRowsLaw (W n) (s n + 3) μ)
    (fun n x => densityCyclicLogDet (W n) (s n) z x / (N n : ℝ))
    (fun n => (K n : ℝ) * densityMaxCorePressure μ (W n) z / (N n : ℝ))
    (fun n => cyclicStitchedPressureError L (W n) (K n) (q n) z / (N n : ℝ))
    (circularLogPotential z) hcenter
  · intro n
    exact (((densityCyclicLogDet_integrable hμ (W n) (s n) (hW n) z).div_const _).sub
      (integrable_const _)).abs
  · intro n
    have hbound (t : ℕ) (ht : K n * densityCellSites (W n) + q n = t) :
        (∫ x : IntervalRows (W n) (t + 3),
          |densityCyclicLogDet (W n) t z x / (((t + 3) * W n : ℕ) : ℝ) -
            (K n : ℝ) * densityMaxCorePressure μ (W n) z /
              (((t + 3) * W n : ℕ) : ℝ)| ∂intervalRowsLaw (W n) (t + 3) μ) ≤
          cyclicStitchedPressureError L (W n) (K n) (q n) z /
            (((t + 3) * W n : ℕ) : ℝ) := by
      subst t
      exact cyclicStitchedPressure_normalized_L1_bound hμ (W n) (K n) (q n) (hW n) z
    exact hbound (s n) (hs n)
  · exact herror

theorem density_long_profile_log_limit
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ) (hSource : Section3Inputs μ L)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, (W n : ℝ) ^ (101 / 100 : ℝ) ≤ ((s n + 3) * W n : ℕ))
    (z : ℂ) :
    ConvergesInProbability (inputLaw μ)
      (fun n ω => normalizedShiftLogDet (profileMatrix (physicalProfile (W n) (s n)) ω) z)
      (circularLogPotential z) := by
  letI := hμ.toIsProbabilityMeasure
  exact (profile_log_converges_iff_physical_rows μ W s z _).mpr
    (density_long_ring_log_limit hμ h3 hSource W s hW hWtop hlong z)

end BernoulliSection10Complex
