import CircularLawSections56.Section5.RealSection34Inputs
import CircularLawSections56.Section5.IndicatorFullEndpoints
import CircularLawSections56.Section5.TaperFullEndpoints

/-! # Complete real-atom indicator and taper theorems on original real arrays

Inputs and outputs now use the same original real probability spaces. The
complex notation only embeds each sampled real number into the matrix field.
There is no planar density assumption, sample-space identification assumption,
uniform taper constant assumption, or pre-assumed Section 5 limit.
-/

open Filter MeasureTheory Topology
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

theorem indicator_original_real_full_of_section34
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ L : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)]
    (δ γ : ℝ) (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hDim : ∀ n, d n + 1 = 2 * W n) (hcenter : ∀ n, center n ≠ 0)
    (hDensity : ∀ n, RealIntervalBound (ρ n) (ENNReal.ofReal L))
    (hInt : ∀ n, Integrable (fun u : ℝ => u ^ 2) (ρ n))
    (hSecond : ∀ n, ∫ u : ℝ, u ^ 2 ∂ρ n ≤ 1)
    (h34 : ∀ᵐ z ∂(volume : Measure ℂ), OriginalRealSection34Inputs
      d (paperBandCellLength W δ) center profile ρ (paperNaturalShortBranch W γ)
      (literalLongActive (paperSafeShortBranch W δ γ)) L z) :
    RealLiteralSection5Conclusions d center (fun n => (profile n).b) ρ := by
  exact indicator_real_full_of_quantitative_section34 d W center profile ρ δ γ
    hc₀ hL hδ hδγ hγ hW hfit hDim hcenter hDensity hInt hSecond
    (h34.mono (fun _ hz => hz.calibration_complexify))
    (h34.mono (fun _ hz => hz.finalSize_complexify))
    (h34.mono (fun _ hz => hz.anchors_complexify))

theorem tapered_original_real_full_of_section34
    (p : PolynomialTaperProfile) (W : ℕ → ℕ) (hWposAll : ∀ n, 0 < W n)
    (L : ℝ) (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)]
    (δ γ : ℝ) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, 2 * W n + 1 ≤ n + 1)
    (hDensity : ∀ n, RealIntervalBound (ρ n) (ENNReal.ofReal L))
    (hInt : ∀ n, Integrable (fun u : ℝ => u ^ 2) (ρ n))
    (hSecond : ∀ n, ∫ u : ℝ, u ^ 2 ∂ρ n ≤ 1)
    (h34 : ∀ᵐ z ∂(volume : Measure ℂ), OriginalRealSection34Inputs
      (PolynomialTaperProfile.dimensions W) (paperBandCellLength W δ)
      (PolynomialTaperProfile.centers W hWposAll) (p.profiles W hWposAll) ρ
      (paperNaturalShortBranch W γ) (literalLongActive (paperSafeShortBranch W δ γ)) L z) :
    RealLiteralSection5Conclusions (PolynomialTaperProfile.dimensions W)
      (PolynomialTaperProfile.centers W hWposAll) (fun n => ((p.profiles W hWposAll) n).b) ρ := by
  have hd (n : ℕ) : PolynomialTaperProfile.dimensions W n + 1 = 2 * W n :=
    taperStateDimension_succ (W n) (hWposAll n)
  apply tapered_real_full_of_quantitative_section34 p W hWposAll L ρ δ γ
    hL hδ hδγ hγ hW hfit hDensity hInt hSecond
  · filter_upwards [h34] with z hz
    simpa only [hd] using hz.calibration_complexify
  · filter_upwards [h34] with z hz
    simpa only [hd] using hz.finalSize_complexify
  · exact h34.mono (fun _ hz => hz.anchors_complexify)

end CircularLawSections56.Section5
