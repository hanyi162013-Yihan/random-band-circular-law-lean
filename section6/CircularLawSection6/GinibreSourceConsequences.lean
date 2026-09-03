import CircularLawSection6.GinibreNegativeSources

/-! # Proved Gaussian reference consequences for the Section 6 source records

The raw-log and spectral limits come from the verified Ginibre formulas.
Only the shifted negative moment uses the explicitly named BBV comparison.
These are consequences, not fields that a caller has to supply.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput)

noncomputable section

namespace CircularLawSection6

/-- Section 6 Gaussian reference step: the pointwise log-potential limit
implies the almost-everywhere source statement, with no external premise. -/
theorem ginibre_raw_verified_ae : ∀ᵐ z ∂(volume : Measure ℂ),
    TendstoInProbabilityTri (fun n => cyclicAtomLaw (n + 1) circularComplexGaussian)
      (fun n ω => matrixRawPotential (ginibreMatrix (n + 1) ω - z • 1))
      (circularRadialPotential ‖z‖) :=
  ae_of_all _ fun z => ginibre_raw_verified
    (fun n => n + 1) (tendsto_add_atTop_nat 1) z

/-- Section 6 logarithmic truncation: BBV and the proved Gaussian lower edge
give the required almost-everywhere negative moment at the fixed exponent. -/
theorem ginibre_negative_of_bbv_ae (hBBV : BBVComparisonInput) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∃ q : ℝ, 0 < q ∧
      BC12GinibreNegativeMomentTightnessTri (fun n => n + 1) z q :=
  ae_of_all _ fun z => ⟨1 / 128, by norm_num,
    ginibre_negative_of_bbv hBBV (fun n => n + 1) (tendsto_add_atTop_nat 1) z⟩

end CircularLawSection6
