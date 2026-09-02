import BernoulliSection10.CyclicPressureComparison
import BernoulliSection10.AnchorScales
import BernoulliSection10.ProbabilityLimits

/-!
# Calibration of the literal maximal core pressure

Only the high-band anchor limit remains a premise of this intermediate
lemma. The public theorem obtains that limit from the permitted Section 3
inputs; no seam, singular-vector, or concentration certificate is assumed.
-/

open Filter MeasureTheory Topology

noncomputable section

namespace BernoulliSection10

open ProbabilityLimits

def densityCorePressureDensity (μ : Measure ℝ) (W : ℕ) (z : ℂ) : ℝ :=
  densityMaxCorePressure μ W z / densityAnchorSize W

theorem tendsto_cyclicAnchorPressureError (L : ℝ) (z : ℂ) :
    Tendsto (fun W => cyclicPressureErrorBound L W (densityCoreSites W) z /
      densityAnchorSize W) atTop (𝓝 0) := by
  have h1 := tendsto_densityAnchor_seam_scale.const_mul (physicalSeamConstant L z)
  have h2 := tendsto_densityAnchor_fluctuation_scale.const_mul
    (densityConcentrationConstant L)
  convert h1.add h2 using 1
  · funext W
    simp only [cyclicPressureErrorBound, add_div]
    ring
  · simp

theorem densityCorePressureDensity_tendsto_of_anchor
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (z : ℂ) (u : ℝ)
    (hAnchor : letI := hμ.toIsProbabilityMeasure
      TendstoInProbabilityTri
        (fun n => intervalRowsLaw (W n) (densityCoreSites (W n) + 3) μ)
        (fun n x => densityCyclicLogDet (W n) (densityCoreSites (W n)) z x /
          densityAnchorSize (W n)) u) :
    Tendsto (fun n => densityCorePressureDensity μ (W n) z) atTop (𝓝 u) := by
  letI := hμ.toIsProbabilityMeasure
  apply deterministic_center_tendsto_of_tri_anchor_and_L1_close
    (fun n => intervalRowsLaw (W n) (densityCoreSites (W n) + 3) μ)
    (fun n x => densityCyclicLogDet (W n) (densityCoreSites (W n)) z x /
      densityAnchorSize (W n))
    (fun n => densityCorePressureDensity μ (W n) z)
    (fun n => cyclicPressureErrorBound L (W n) (densityCoreSites (W n)) z /
      densityAnchorSize (W n)) u hAnchor
  · intro n
    exact (((densityCyclicLogDet_integrable hμ (W n) (densityCoreSites (W n))
      (hW n) z).div_const _).sub (integrable_const _)).abs
  · intro n
    exact cyclicPressure_normalized_L1_bound hμ (W n) (densityCoreSites (W n)) (hW n) z
  · exact (tendsto_cyclicAnchorPressureError L z).comp hWtop

end BernoulliSection10
