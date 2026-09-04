import CircularLawSections56.Section5.VerifiedComplexSection5Endpoint

/-! Public-boundary regression: the complex-density endpoint is callable
without supplying either finite Section 4 pressure contract. -/

open MeasureTheory Filter Topology ShortRingAnchor
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete
open scoped ENNReal

noncomputable section
set_option autoImplicit false
set_option warningAsError true

example
    (hBBV : BBVComparisonInput)
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ L : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    (δ γ : ℝ) (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hcenter : ∀ n, (center n).val = W n)
    (hDensity : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L)
    (hMom : AtomMomentAssumption21 (volume.withDensity f) id) :
    LiteralSection5Conclusions d center (fun n => (profile n).b)
      (fun _ => volume.withDensity f) :=
  indicator_complex_full_of_bbv hBBV d W center profile f δ γ hc₀ hL
    hδ hδγ hγ hW hfit hwidth hcenter hDensity hMom

#check @indicator_complex_full_of_bbv
