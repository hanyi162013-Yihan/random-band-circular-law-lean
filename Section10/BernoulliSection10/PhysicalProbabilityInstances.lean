import BernoulliSection10.PhysicalModel

/-! # Probability normalization of the literal physical product laws -/

open MeasureTheory

namespace BernoulliSection10

instance physicalRowLaw_isProbabilityMeasure (W : ℕ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (physicalRowLaw W μ) := by
  unfold physicalRowLaw
  infer_instance

instance intervalRowsLaw_isProbabilityMeasure (W s : ℕ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (intervalRowsLaw W s μ) := by
  unfold intervalRowsLaw
  infer_instance

end BernoulliSection10
