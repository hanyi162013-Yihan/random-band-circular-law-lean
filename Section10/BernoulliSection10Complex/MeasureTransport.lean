import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace BernoulliSection10Complex

/-- Integral transport also for complex-valued observables and noninjective
maps. This is a direct consequence of the mathlib pushforward identity. -/
theorem integral_comp_measurePreserving
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} {ν : Measure Y} {f : X → Y}
    (hf : MeasurePreserving f μ ν) {g : Y → E} (hg : StronglyMeasurable g) :
    (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  rw [← hf.map_eq]
  exact (integral_map_of_stronglyMeasurable hf.measurable hg).symm

end BernoulliSection10Complex
