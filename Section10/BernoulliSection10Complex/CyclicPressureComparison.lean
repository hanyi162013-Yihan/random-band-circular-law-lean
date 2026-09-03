import BernoulliSection10Complex.CyclicSeamAssembly
import BernoulliSection10Complex.ConcentrationScale
import BernoulliSection10Complex.PhysicalProbabilityInstances

/-! # The actual cyclic log determinant versus its deterministic outside pressure -/

open MeasureTheory

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

set_option backward.isDefEq.respectTransparency false

def cyclicPressureErrorBound (L : ℝ) (W s : ℕ) (z : ℂ) : ℝ :=
  physicalSeamConstant L z * W * densityLogScale W +
    densityConcentrationConstant L *
      Real.sqrt ((W : ℝ) * ((s * W : ℕ) : ℝ)) * densityLogScale W

theorem cyclicPressure_L1_bound
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫ x, |densityCyclicLogDet W s z x - intervalMaxPressure μ W s z|
      ∂intervalRowsLaw W (s + 3) μ) ≤ cyclicPressureErrorBound L W s z := by
  letI := hμ.toIsProbabilityMeasure
  let π := intervalRestriction (W := W) (s := s + 3) (Fin.castAddEmb 3)
  let P := intervalMaxPressure μ W s z
  let Z := fun x : IntervalRows W (s + 3) => intervalMaxDegreeLog W s z (π x)
  have hmp := intervalRestriction_measurePreserving hμ (W := W) (Fin.castAddEmb 3 (n := s))
  have hZi : Integrable Z (intervalRowsLaw W (s + 3) μ) :=
    hmp.integrable_comp_of_integrable (intervalMaxDegreeLog_integrable hμ W s hW z)
  have hLi := densityCyclicLogDet_integrable hμ W s hW z
  have hDi := (cyclicSeamDifference_integrable_and_L1_bound hμ W s hW z).1
  have hle := integral_mono ((hLi.sub (integrable_const P)).abs)
    (hDi.abs.add ((hZi.sub (integrable_const P)).abs))
      (fun x => abs_sub_le (densityCyclicLogDet W s z x) (Z x) P)
  simp only [Pi.add_apply] at hle
  rw [integral_add hDi.abs ((hZi.sub (integrable_const P)).abs)] at hle
  simp only [Pi.sub_apply] at hle
  have hmean : (∫ x, |Z x - P| ∂intervalRowsLaw W (s + 3) μ) =
      ∫ y, |intervalMaxDegreeLog W s z y - P| ∂intervalRowsLaw W s μ :=
    real_integral_comp_measurePreserving hmp
      ((measurable_finitePressureMax (fun r => measurable_intervalDegreeLog W s z r)).sub_const P).norm
  rw [hmean] at hle
  have hseam := (cyclicSeamDifference_integrable_and_L1_bound hμ W s hW z).2
  have hconc := (intervalMaxDegreeLog_sub_maxPressure_integral_le hμ W s hW z).trans
    (intervalPressureConcentrationCost_le L W s hW)
  exact hle.trans (add_le_add hseam hconc)

theorem cyclicPressure_normalized_L1_bound
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫ x, |densityCyclicLogDet W s z x / (((s + 3) * W : ℕ) : ℝ) -
      intervalMaxPressure μ W s z / (((s + 3) * W : ℕ) : ℝ)|
        ∂intervalRowsLaw W (s + 3) μ) ≤
      cyclicPressureErrorBound L W s z / (((s + 3) * W : ℕ) : ℝ) := by
  simp_rw [← sub_div, abs_div, abs_of_nonneg
    (Nat.cast_nonneg ((s + 3) * W) : (0 : ℝ) ≤ (((s + 3) * W : ℕ) : ℝ))]
  rw [integral_div]
  exact div_le_div_of_nonneg_right (cyclicPressure_L1_bound hμ W s hW z) (Nat.cast_nonneg _)

end BernoulliSection10Complex
