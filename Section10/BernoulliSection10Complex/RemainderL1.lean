import BernoulliSection10Complex.StitchedPressure
import BernoulliSection10Complex.PhysicalProbabilityInstances

/-! # Integrating the already proved, degree-uniform physical remainder estimate -/

open MeasureTheory

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

set_option backward.isDefEq.respectTransparency false

theorem intervalRemainderMaxDifference_integrable
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W p q : ℕ) (hW : 0 < W) (z : ℂ) :
    Integrable (intervalRemainderMaxDifference W p q z) (intervalRowsLaw W (p + q) μ) :=
  (intervalMaxDegreeLog_integrable hμ W (p + q) hW z).sub
    ((intervalRestriction_measurePreserving hμ (W := W) (Fin.castAddEmb q)).integrable_comp_of_integrable
      (intervalMaxDegreeLog_integrable hμ W p hW z))

theorem intervalRemainderMaxDifference_L1_bound
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W p q : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫ x, |intervalRemainderMaxDifference W p q z x| ∂intervalRowsLaw W (p + q) μ) ≤
      (q : ℝ) * remainderHodgeConstant L z * W * densityLogScale W := by
  have hm := intervalRestriction_measurePreserving hμ (W := W) (Fin.natAddEmb p (m := q))
  have hi := hm.integrable_comp_of_integrable (intervalMaxHodgeEnvelope_integrable hμ W q hW z)
  exact (integral_mono_ae (intervalRemainderMaxDifference_integrable hμ W p q hW z).abs hi
    (intervalRemainderMaxDifference_le_ae hμ W p q hW z)).trans
      (suffixHodgeEnvelope_integral_le hμ W p q hW z)

theorem stitchedPressure_with_remainder_L1_bound
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W K q : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫ x, |intervalMaxDegreeLog W (K * densityCellSites W + q) z x -
      (K : ℝ) * densityMaxCorePressure μ W z|
        ∂intervalRowsLaw W (K * densityCellSites W + q) μ) ≤
      (q : ℝ) * remainderHodgeConstant L z * W * densityLogScale W +
        stitchedPressureErrorBound L W K z := by
  letI := hμ.toIsProbabilityMeasure
  let p := K * densityCellSites W
  let M := (K : ℝ) * densityMaxCorePressure μ W z
  let Z := fun x : IntervalRows W (p + q) =>
    intervalMaxDegreeLog W p z (intervalRestriction (Fin.castAddEmb q) x)
  have hp := intervalRestriction_measurePreserving hμ (W := W) (Fin.castAddEmb q (n := p))
  have hZi : Integrable Z (intervalRowsLaw W (p + q) μ) :=
    hp.integrable_comp_of_integrable (intervalMaxDegreeLog_integrable hμ W p hW z)
  have hDi := intervalRemainderMaxDifference_integrable hμ W p q hW z
  have hXi := intervalMaxDegreeLog_integrable hμ W (p + q) hW z
  have hle := integral_mono ((hXi.sub (integrable_const M)).abs)
    (hDi.abs.add ((hZi.sub (integrable_const M)).abs))
      (fun x => abs_sub_le (intervalMaxDegreeLog W (p + q) z x) (Z x) M)
  simp only [Pi.add_apply] at hle
  rw [integral_add hDi.abs ((hZi.sub (integrable_const M)).abs)] at hle
  simp only [Pi.sub_apply] at hle
  have he : (∫ x, |Z x - M| ∂intervalRowsLaw W (p + q) μ) =
      ∫ x, |intervalMaxDegreeLog W p z x - M| ∂intervalRowsLaw W p μ :=
    real_integral_comp_measurePreserving hp
      ((measurable_finitePressureMax (fun r => measurable_intervalDegreeLog W p z r)).sub_const M).norm
  rw [he] at hle
  exact hle.trans (add_le_add
    (intervalRemainderMaxDifference_L1_bound hμ W p q hW z)
    (stitchedPressure_L1_bound hμ W K hW z))

end BernoulliSection10Complex

