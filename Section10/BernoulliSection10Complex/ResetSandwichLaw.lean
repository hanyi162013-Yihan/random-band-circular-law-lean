import BernoulliSection10Complex.IntervalConcatenation
import BernoulliSection10Complex.ConcretePressure
import Mathlib.MeasureTheory.Integral.Prod

/-! # The product-space law used by the mean-stitching integral -/

open MeasureTheory

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

/-- A measurable scalar observable can be integrated along a
measure-preserving map without assuming that the map is injective. -/
theorem real_integral_comp_measurePreserving
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y}
    (hf : MeasurePreserving f μ ν) {g : Y → ℝ} (hg : Measurable g) :
    (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  calc
    _ = ∫ y, g y ∂Measure.map f μ :=
      (integral_map_of_stronglyMeasurable hf.measurable hg.stronglyMeasurable).symm
    _ = _ := by rw [hf.map_eq]

def resetSandwichRows (W p q : ℕ)
    (v : IntervalRows W p × (IntervalRows W q × IntervalRows W 3)) :
    IntervalRows W (q + 3 + p) :=
  intervalConcat W (q + 3) p (intervalConcat W q 3 v.2, v.1)

/-- The order of integration is core, past, reset. The chronological
order of the physical interval is past, reset, core. -/
theorem resetSandwichRows_measurePreserving
    {μ : Measure ℂ} [IsProbabilityMeasure μ] (W p q : ℕ) :
    MeasurePreserving (resetSandwichRows W p q)
      ((intervalRowsLaw W p μ).prod
        ((intervalRowsLaw W q μ).prod (intervalRowsLaw W 3 μ)))
      (intervalRowsLaw W (q + 3 + p) μ) := by
  letI (s : ℕ) : IsProbabilityMeasure (intervalRowsLaw W s μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  have hjoin := (MeasurePreserving.id (intervalRowsLaw W p μ)).prod
    (intervalConcat_measurePreserving (μ := μ) W q 3)
  exact (intervalConcat_measurePreserving (μ := μ) W (q + 3) p).comp
    (Measure.measurePreserving_swap.comp hjoin)

theorem intervalClearedProduct_resetSandwichRows
    (W p q : ℕ) (z : ℂ)
    (v : IntervalRows W p × (IntervalRows W q × IntervalRows W 3))
    (r : Fin (2 * W + 1)) :
    intervalClearedProduct W (q + 3 + p) z (resetSandwichRows W p q v) r =
      intervalClearedProduct W p z v.1 r *
        intervalClearedProduct W 3 z v.2.2 r * intervalClearedProduct W q z v.2.1 r := by
  rcases v with ⟨core, past, reset⟩
  simp only [resetSandwichRows, intervalClearedProduct_concat, Matrix.mul_assoc]

def resetSandwichRowsFlat (W p q : ℕ)
    (v : (IntervalRows W p × IntervalRows W q) × IntervalRows W 3) :
    IntervalRows W (q + 3 + p) :=
  resetSandwichRows W p q (v.1.1, (v.1.2, v.2))

theorem resetSandwichRowsFlat_measurePreserving
    {μ : Measure ℂ} [IsProbabilityMeasure μ] (W p q : ℕ) :
    MeasurePreserving (resetSandwichRowsFlat W p q)
      (((intervalRowsLaw W p μ).prod (intervalRowsLaw W q μ)).prod
        (intervalRowsLaw W 3 μ))
      (intervalRowsLaw W (q + 3 + p) μ) := by
  letI (s : ℕ) : IsProbabilityMeasure (intervalRowsLaw W s μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  exact (resetSandwichRows_measurePreserving (μ := μ) W p q).comp
    (measurePreserving_prodAssoc _ _ _)

open scoped Matrix.Norms.L2Operator in
theorem resetSandwichLog_joint_integrable
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W p q : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1)) :
    Integrable (fun v : IntervalRows W p × (IntervalRows W q × IntervalRows W 3) =>
      Real.log ‖intervalClearedProduct W p z v.1 r *
        intervalClearedProduct W 3 z v.2.2 r * intervalClearedProduct W q z v.2.1 r‖)
      ((intervalRowsLaw W p μ).prod
        ((intervalRowsLaw W q μ).prod (intervalRowsLaw W 3 μ))) := by
  letI := hμ.toIsProbabilityMeasure
  have h := (resetSandwichRows_measurePreserving (μ := μ) W p q).integrable_comp_of_integrable
    (intervalDegreeLog_integrable hμ W (q + 3 + p) hW z r)
  simpa only [Function.comp_def, intervalDegreeLog, intervalClearedProduct_resetSandwichRows]
    using h

end BernoulliSection10Complex
