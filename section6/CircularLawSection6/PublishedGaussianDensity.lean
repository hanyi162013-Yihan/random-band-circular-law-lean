import CircularLawSection6.PublishedGaussianModel

/-! # The actual Gaussian density in the published Section 3 interface

This concrete constructor also checks that the source bounded-density record
can be inhabited. The finite-density bound must refer to the ENNReal top.
-/

open MeasureTheory ShortRingAnchor
open CircularLawSections56.Section5
noncomputable section

namespace CircularLawSection6

def circularComplexGaussian_publishedDensity :
    HasBoundedDensityWithRespectTo (Measure.map id circularComplexGaussian) (volume : Measure ℂ) where
  density := circularGaussianDensity
  densityAEMeasurable := (Measure.measurable_rnDeriv circularComplexGaussian volume).aemeasurable
  bound := 2
  bound_lt_top := by norm_num
  density_le_bound := circularGaussianDensity_le_two
  law_eq_withDensity := by rw [Measure.map_id, circularGaussianDensity_withDensity]

theorem circularComplexGaussian_publishedDensityAlternative :
    AtomDensityAlternative21 circularComplexGaussian id :=
  .complex circularComplexGaussian_publishedDensity

end CircularLawSection6
