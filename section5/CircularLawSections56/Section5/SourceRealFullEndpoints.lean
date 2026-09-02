import CircularLawSections56.Section5.SourceAtomMoments
import CircularLawSections56.Section5.OriginalRealFullEndpoints

/-! # Real Section 5 from the manuscript's original atom assumptions

The moment input is exactly the existing Section 3 Assumption 2.1 record,
including centering and finite third moment. Integrability and normalization
needed downstream are consequences of that record. All finite Section 4
inputs, Section 3 anchors, and final conclusions use original real arrays.
-/

open Filter MeasureTheory Topology
open scoped ENNReal
noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5
open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights ShortRingAnchor

theorem indicator_original_real_full_of_source_assumptions
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ L : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (f : ℕ → ℝ → ENNReal) [∀ n, IsProbabilityMeasure (volume.withDensity (f n))]
    (δ γ : ℝ) (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hDim : ∀ n, d n + 1 = 2 * W n) (hcenter : ∀ n, center n ≠ 0)
    (hDensity : ∀ n, ∀ᵐ x ∂(volume : Measure ℝ), f n x ≤ ENNReal.ofReal L)
    (hMom : ∀ n, AtomMomentAssumption21 (volume.withDensity (f n)) Complex.ofReal)
    (h34 : ∀ᵐ z ∂(volume : Measure ℂ), OriginalRealSection34Inputs
      d (paperBandCellLength W δ) center profile (fun n => volume.withDensity (f n))
      (paperNaturalShortBranch W γ) (literalLongActive (paperSafeShortBranch W δ γ)) L z) :
    RealLiteralSection5Conclusions d center (fun n => (profile n).b)
      (fun n => volume.withDensity (f n)) := by
  exact indicator_original_real_full_of_section34 d W center profile
    (fun n => volume.withDensity (f n)) δ γ hc₀ hL hδ hδγ hγ hW hfit hDim hcenter
    (fun n => real_source_density_interval_bound (f n) L (hDensity n))
    (fun n => real_source_moments_second_integrable _ (hMom n))
    (fun n => (real_source_moments_second_eq_one _ (hMom n)).le) h34

theorem tapered_original_real_full_of_source_assumptions
    (p : PolynomialTaperProfile) (W : ℕ → ℕ) (hWposAll : ∀ n, 0 < W n)
    (L : ℝ) (f : ℕ → ℝ → ENNReal)
    [∀ n, IsProbabilityMeasure (volume.withDensity (f n))]
    (δ γ : ℝ) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, 2 * W n + 1 ≤ n + 1)
    (hDensity : ∀ n, ∀ᵐ x ∂(volume : Measure ℝ), f n x ≤ ENNReal.ofReal L)
    (hMom : ∀ n, AtomMomentAssumption21 (volume.withDensity (f n)) Complex.ofReal)
    (h34 : ∀ᵐ z ∂(volume : Measure ℂ), OriginalRealSection34Inputs
      (PolynomialTaperProfile.dimensions W) (paperBandCellLength W δ)
      (PolynomialTaperProfile.centers W hWposAll) (p.profiles W hWposAll)
      (fun n => volume.withDensity (f n)) (paperNaturalShortBranch W γ)
      (literalLongActive (paperSafeShortBranch W δ γ)) L z) :
    RealLiteralSection5Conclusions (PolynomialTaperProfile.dimensions W)
      (PolynomialTaperProfile.centers W hWposAll) (fun n => ((p.profiles W hWposAll) n).b)
      (fun n => volume.withDensity (f n)) := by
  exact tapered_original_real_full_of_section34 p W hWposAll L
    (fun n => volume.withDensity (f n)) δ γ hL hδ hδγ hγ hW hfit
    (fun n => real_source_density_interval_bound (f n) L (hDensity n))
    (fun n => real_source_moments_second_integrable _ (hMom n))
    (fun n => (real_source_moments_second_eq_one _ (hMom n)).le) h34

end CircularLawSections56.Section5
