import BernoulliSection10Complex.PhysicalSeam
import BernoulliSection10Complex.OutsidePressureIdentification
import BernoulliSection10Complex.ResetSandwichLaw

/-!
# The periodic seam on the actual cyclic probability space

The terminal packet and the outside interval are independent coordinates
of one literal matrix. The frozen seam bound is integrated by Fubini; no
conditional expectation or measurable singular-frame choice is assumed.
-/

open MeasureTheory
open scoped Matrix

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open BernoulliLinearAlgebra Matrix

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem measurable_densityCyclicLogDet (W s : ℕ) (z : ℂ) :
    Measurable (densityCyclicLogDet W s z) := by
  have heq : densityCyclicLogDet W s z = fun x =>
      Real.log ‖physicalBoundaryExpression W (s + 3) z x 1‖ := by
    funext x
    rw [densityCyclicLogDet_eq_polynomial_trace]
    simp only [physicalBoundaryExpression, polynomialClearedBoundaryTrace,
      polynomialClearedSignedCompoundTrace, compound_one, Matrix.mul_one]
  rw [heq]
  exact Real.measurable_log.comp
    (continuous_physicalBoundaryExpression W (s + 3) z 1).norm.measurable

/-- A nonnegative jointly measurable function with uniformly bounded
integrable fibers is integrable on the product probability space. -/
theorem integrable_prod_of_nonneg_fiber_bound
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} [IsProbabilityMeasure P] [SFinite Q]
    {F : Ω × Ξ → ℝ} (hFm : Measurable F) (hF0 : ∀ v, 0 ≤ F v)
    {C : ℝ} (hf : ∀ᵐ x ∂P, Integrable (fun y => F (x, y)) Q ∧
      (∫ y, F (x, y) ∂Q) ≤ C) :
    Integrable F (P.prod Q) ∧ (∫ v, F v ∂P.prod Q) ≤ C := by
  have hnorm (x : Ω) : (∫ y, ‖F (x, y)‖ ∂Q) = ∫ y, F (x, y) ∂Q := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => Real.norm_of_nonneg (hF0 (x, y))
  have hm : AEStronglyMeasurable (fun x => ∫ y, ‖F (x, y)‖ ∂Q) P :=
    hFm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
  have hi : Integrable (fun x => ∫ y, ‖F (x, y)‖ ∂Q) P := by
    apply (integrable_const C).mono' hm
    filter_upwards [hf] with x hx
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hnorm]
    exact hx.2
  have hFi := (integrable_prod_iff hFm.aestronglyMeasurable).2
    ⟨hf.mono fun _ hx => hx.1, hi⟩
  refine ⟨hFi, ?_⟩
  rw [integral_prod F hFi]
  have hle := integral_mono_ae hFi.integral_prod_left (integrable_const C)
    (hf.mono fun _ hx => hx.2)
  simpa only [integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul] using hle

def cyclicSeamDifference (W s : ℕ) (z : ℂ) (x : IntervalRows W (s + 3)) : ℝ :=
  densityCyclicLogDet W s z x -
    intervalMaxDegreeLog W s z (intervalRestriction (Fin.castAddEmb 3) x)

theorem measurable_cyclicSeamDifference (W s : ℕ) (z : ℂ) :
    Measurable (cyclicSeamDifference W s z) := by
  exact (measurable_densityCyclicLogDet W s z).sub
    ((measurable_finitePressureMax (fun r => measurable_intervalDegreeLog W s z r)).comp
      (by unfold intervalRestriction; fun_prop))

theorem cyclicSeamDifference_integrable_and_L1_bound
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    Integrable (cyclicSeamDifference W s z) (intervalRowsLaw W (s + 3) μ) ∧
      (∫ x, |cyclicSeamDifference W s z x| ∂intervalRowsLaw W (s + 3) μ) ≤
        physicalSeamConstant L z * W * densityLogScale W := by
  letI := hμ.toIsProbabilityMeasure
  letI (n : ℕ) : IsProbabilityMeasure (intervalRowsLaw W n μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  let F : IntervalRows W s × IntervalRows W 3 → ℝ :=
    fun v => |cyclicSeamDifference W s z (intervalConcat W s 3 v)|
  have hmp := intervalConcat_measurePreserving (μ := μ) W s 3
  have hFm : Measurable F :=
    ((measurable_cyclicSeamDifference W s z).comp hmp.measurable).norm
  have hf : ∀ᵐ outside ∂intervalRowsLaw W s μ,
      Integrable (fun packet => F (outside, packet)) (intervalRowsLaw W 3 μ) ∧
      (∫ packet, F (outside, packet) ∂intervalRowsLaw W 3 μ) ≤
        physicalSeamConstant L z * W * densityLogScale W := by
    filter_upwards [intervalInterfaceDets_isUnit_ae hμ W s hW z,
      intervalTransfer_representation_ae hμ W s hW z,
      intervalMaxDegreeLog_eq_outsidePressure_ae hμ W s hW z] with outside hblocks hrep hp
    have heq : (fun packet => F (outside, packet)) =
        physicalSeamLoss W z (intervalClearingFactor W s z outside)
          (intervalTransferProduct W s z outside) := by
      funext packet
      simp only [F, cyclicSeamDifference, physicalSeamLoss,
        intervalRestriction_concat_prefix,
        densityCyclicLogDet_terminalPacket W s z outside packet (fun j => (hblocks j).1), hp]
    rw [heq]
    exact ⟨physicalSeamLoss_integrable hμ W hW z _ hrep.1 _ hrep.2.1,
      physicalSeamLoss_integral_le hμ W hW z _ hrep.1 _ hrep.2.1⟩
  have hprod := integrable_prod_of_nonneg_fiber_bound hFm (fun _ => abs_nonneg _) hf
  have hm := (measurable_cyclicSeamDifference W s z).norm
  have hia : Integrable (fun x => |cyclicSeamDifference W s z x|)
      (intervalRowsLaw W (s + 3) μ) :=
    (hmp.integrable_comp hm.aestronglyMeasurable).mp hprod.1
  refine ⟨(integrable_norm_iff (measurable_cyclicSeamDifference W s z).aestronglyMeasurable).mp hia, ?_⟩
  have heq := real_integral_comp_measurePreserving hmp hm
  exact heq ▸ hprod.2

theorem densityCyclicLogDet_integrable
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    Integrable (densityCyclicLogDet W s z) (intervalRowsLaw W (s + 3) μ) := by
  letI := hμ.toIsProbabilityMeasure
  have hp := (intervalRestriction_measurePreserving hμ (W := W)
    (Fin.castAddEmb 3)).integrable_comp_of_integrable
      (intervalMaxDegreeLog_integrable hμ W s hW z)
  have hd := (cyclicSeamDifference_integrable_and_L1_bound hμ W s hW z).1
  have he : densityCyclicLogDet W s z = cyclicSeamDifference W s z +
      intervalMaxDegreeLog W s z ∘ intervalRestriction (Fin.castAddEmb 3) := by
    funext x
    simp only [Pi.add_apply, cyclicSeamDifference, Function.comp_apply, sub_add_cancel]
  rw [he]
  exact hd.add hp

end BernoulliSection10Complex

