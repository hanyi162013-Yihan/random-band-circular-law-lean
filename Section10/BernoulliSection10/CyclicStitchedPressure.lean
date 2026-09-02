import BernoulliSection10.CyclicSeamAssembly
import BernoulliSection10.RemainderL1

/-! # The terminal seam, complete cells, and remainder in one literal estimate -/

open MeasureTheory

noncomputable section

namespace BernoulliSection10

set_option backward.isDefEq.respectTransparency false

def cyclicStitchedPressureError (L : ℝ) (W K q : ℕ) (z : ℂ) : ℝ :=
  physicalSeamConstant L z * W * densityLogScale W +
    (q : ℝ) * remainderHodgeConstant L z * W * densityLogScale W +
    stitchedPressureErrorBound L W K z

theorem cyclicStitchedPressure_L1_bound
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W K q : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫ x, |densityCyclicLogDet W (K * densityCellSites W + q) z x -
      (K : ℝ) * densityMaxCorePressure μ W z|
        ∂intervalRowsLaw W (K * densityCellSites W + q + 3) μ) ≤
      cyclicStitchedPressureError L W K q z := by
  letI := hμ.toIsProbabilityMeasure
  let s := K * densityCellSites W + q
  let M := (K : ℝ) * densityMaxCorePressure μ W z
  let Z := fun x : IntervalRows W (s + 3) =>
    intervalMaxDegreeLog W s z (intervalRestriction (Fin.castAddEmb 3) x)
  have hp := intervalRestriction_measurePreserving hμ (W := W) (Fin.castAddEmb 3 (n := s))
  have hZi : Integrable Z (intervalRowsLaw W (s + 3) μ) :=
    hp.integrable_comp_of_integrable (intervalMaxDegreeLog_integrable hμ W s hW z)
  have hLi := densityCyclicLogDet_integrable hμ W s hW z
  have hDi := (cyclicSeamDifference_integrable_and_L1_bound hμ W s hW z).1
  have hle := integral_mono ((hLi.sub (integrable_const M)).abs)
    (hDi.abs.add ((hZi.sub (integrable_const M)).abs))
      (fun x => abs_sub_le (densityCyclicLogDet W s z x) (Z x) M)
  simp only [Pi.add_apply] at hle
  rw [integral_add hDi.abs ((hZi.sub (integrable_const M)).abs)] at hle
  simp only [Pi.sub_apply] at hle
  have he : (∫ x, |Z x - M| ∂intervalRowsLaw W (s + 3) μ) =
      ∫ x, |intervalMaxDegreeLog W s z x - M| ∂intervalRowsLaw W s μ :=
    real_integral_comp_measurePreserving hp
      ((measurable_finitePressureMax (fun r => measurable_intervalDegreeLog W s z r)).sub_const M).norm
  rw [he] at hle
  have hb := add_le_add (cyclicSeamDifference_integrable_and_L1_bound hμ W s hW z).2
    (stitchedPressure_with_remainder_L1_bound hμ W K q hW z)
  exact (hle.trans hb).trans_eq (by simp only [cyclicStitchedPressureError, add_assoc])

theorem cyclicStitchedPressure_normalized_L1_bound
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W K q : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫ x, |densityCyclicLogDet W (K * densityCellSites W + q) z x /
      (((K * densityCellSites W + q + 3) * W : ℕ) : ℝ) -
      (K : ℝ) * densityMaxCorePressure μ W z /
        (((K * densityCellSites W + q + 3) * W : ℕ) : ℝ)|
        ∂intervalRowsLaw W (K * densityCellSites W + q + 3) μ) ≤
      cyclicStitchedPressureError L W K q z /
        (((K * densityCellSites W + q + 3) * W : ℕ) : ℝ) := by
  simp_rw [← sub_div, abs_div, abs_of_nonneg
    (Nat.cast_nonneg ((K * densityCellSites W + q + 3) * W) :
      (0 : ℝ) ≤ (((K * densityCellSites W + q + 3) * W : ℕ) : ℝ))]
  rw [integral_div]
  exact div_le_div_of_nonneg_right (cyclicStitchedPressure_L1_bound hμ W K q hW z)
    (Nat.cast_nonneg _)

end BernoulliSection10
