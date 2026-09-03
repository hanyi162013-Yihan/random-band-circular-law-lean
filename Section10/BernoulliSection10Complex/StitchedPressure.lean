import BernoulliSection10Complex.MeanStitching
import BernoulliSection10Complex.ConcentrationScale

/-!
# Whole-product pressure after mean stitching

Equation (10.42), proved in the stronger `L¹` form. The maximum is taken
after a single concentration estimate for the whole interval. The
optimizing degree and all cell means are the concrete definitions from
`ConcretePressure`.
-/

open MeasureTheory

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

set_option backward.isDefEq.respectTransparency false

theorem intervalMaxPressure_complete_cells
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W K : ℕ) (hW : 0 < W) (z : ℂ) :
    |intervalMaxPressure μ W (K * densityCellSites W) z -
      (K : ℝ) * densityMaxCorePressure μ W z| ≤
        (K : ℝ) * (densityCellMeanErrorConstant L z * W * densityLogScale W) := by
  have h := abs_finitePressureMax_sub_le
    (fun r => densityCorePressure_mean_stitching hμ W K hW z r)
  rw [finitePressureMax_mul_nonneg _ (Nat.cast_nonneg K)] at h
  exact h

def stitchedPressureErrorBound (L : ℝ) (W K : ℕ) (z : ℂ) : ℝ :=
  (K : ℝ) * (densityCellMeanErrorConstant L z * W * densityLogScale W) +
    densityConcentrationConstant L *
      Real.sqrt ((W : ℝ) * ((K * densityCellSites W * W : ℕ) : ℝ)) * densityLogScale W

theorem stitchedPressure_L1_bound
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W K : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫ x, |intervalMaxDegreeLog W (K * densityCellSites W) z x -
      (K : ℝ) * densityMaxCorePressure μ W z|
        ∂intervalRowsLaw W (K * densityCellSites W) μ) ≤
      stitchedPressureErrorBound L W K z := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W (K * densityCellSites W) μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  let P := intervalMaxPressure μ W (K * densityCellSites W) z
  let F := (K : ℝ) * densityMaxCorePressure μ W z
  let E := (K : ℝ) * (densityCellMeanErrorConstant L z * W * densityLogScale W)
  have hi := intervalMaxDegreeLog_integrable hμ W (K * densityCellSites W) hW z
  have hmean : |P - F| ≤ E := intervalMaxPressure_complete_cells hμ W K hW z
  have hpoint (x : IntervalRows W (K * densityCellSites W)) :
      |intervalMaxDegreeLog W (K * densityCellSites W) z x - F| ≤
        |intervalMaxDegreeLog W (K * densityCellSites W) z x - P| + E :=
    (abs_sub_le _ P F).trans (add_le_add le_rfl hmean)
  have hle := integral_mono ((hi.sub (integrable_const F)).abs)
    (((hi.sub (integrable_const P)).abs).add (integrable_const E)) hpoint
  simp only [Pi.add_apply] at hle
  rw [integral_add ((hi.sub (integrable_const P)).abs) (integrable_const E),
    integral_const] at hle
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hle
  have hconc := (intervalMaxDegreeLog_sub_maxPressure_integral_le hμ W
    (K * densityCellSites W) hW z).trans
      (intervalPressureConcentrationCost_le L W (K * densityCellSites W) hW)
  unfold stitchedPressureErrorBound
  dsimp only [P, F, E, Pi.sub_apply] at hle
  linarith only [hle, hconc]

theorem stitchedPressure_markov
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W K : ℕ) (hW : 0 < W) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (intervalRowsLaw W (K * densityCellSites W) μ).real
      {x | ε ≤ |intervalMaxDegreeLog W (K * densityCellSites W) z x -
        (K : ℝ) * densityMaxCorePressure μ W z|} ≤
      stitchedPressureErrorBound L W K z / ε := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W (K * densityCellSites W) μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  let X := fun x => intervalMaxDegreeLog W (K * densityCellSites W) z x -
    (K : ℝ) * densityMaxCorePressure μ W z
  have hi : Integrable (fun x => |X x|) (intervalRowsLaw W (K * densityCellSites W) μ) :=
    ((intervalMaxDegreeLog_integrable hμ W (K * densityCellSites W) hW z).sub
      (integrable_const _)).abs
  exact (measureReal_abs_ge_le_of_ae_bound _ X (fun x => |X x|)
    (Filter.Eventually.of_forall fun _ => le_rfl) hi
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) hε).trans
      (div_le_div_of_nonneg_right (stitchedPressure_L1_bound hμ W K hW z) hε.le)

end BernoulliSection10Complex
