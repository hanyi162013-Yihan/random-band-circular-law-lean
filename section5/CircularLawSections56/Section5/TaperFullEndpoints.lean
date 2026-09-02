import CircularLawSections56.Section5.TaperCanonicalAtomEndpoints
import CircularLawSections56.Section5.QuantitativeSection4Inputs
import CircularLawSections56.Section5.Section5Conclusions

/-! # Full polynomial taper corollaries from the quantitative Section 3/4 inputs

These final entries return the logarithmic potential, bounded-continuous
spectral convergence, normalized Hilbert--Schmidt tightness, and almost-sure
nonvanishing. No cell geometry or uniform taper pressure constant is supplied.
The latter is derived from Section 4's explicit finite constants.
-/

open Filter MeasureTheory Topology
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option autoImplicit false
namespace CircularLawSections56.Section5
open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open TaoVuReplacement ShortRingAnchor

theorem tapered_real_full_of_quantitative_section34
    (p : PolynomialTaperProfile) (W : ℕ → ℕ) (hWposAll : ∀ n, 0 < W n)
    (L : ℝ)
    (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)]
    (δ γ : ℝ)
    (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, 2 * W n + 1 ≤ n + 1)
    (hDensity : ∀ n, RealIntervalBound (ρ n) (ENNReal.ofReal L))
    (hInt : ∀ n, Integrable (fun u : ℝ => u ^ 2) (ρ n))
    (hSecond : ∀ n, ∫ u : ℝ, u ^ 2 ∂ρ n ≤ 1)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), RealQuantitativeSection4PressureInput
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (PolynomialTaperProfile.dimensions W) (fun n => paperBandCellLength W δ n - 2 * W n)
      (fun n => literalModelCalibrationRaw n ((PolynomialTaperProfile.dimensions W) n) (paperBandCellLength W δ n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (paperBandCellLength W δ n) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      (fun n => p.lowerParameter (W n)) L z)
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), RealQuantitativeSection4PressureInput
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (PolynomialTaperProfile.dimensions W) (fun n => n + 1 - 2 * W n)
      (fun n => literalModelRawDeterminant n ((PolynomialTaperProfile.dimensions W) n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (n + 1) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      (fun n => p.lowerParameter (W n)) L z)
    (h3 :
      let : ∀ n, IsProbabilityMeasure
          (iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2))) :=
        fun n => iidMeasure_isProbability (realComplexAtomLaw (ρ n)) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
        (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
        (literalShortLogPotential (PolynomialTaperProfile.dimensions W) (PolynomialTaperProfile.centers W hWposAll) (fun n => ((p.profiles W hWposAll) n).b) (paperNaturalShortBranch W γ) z)
        (literalActiveNormalizedObservable (literalLongActive (paperSafeShortBranch W δ γ))
          (fun n => literalModelCalibrationRaw n ((PolynomialTaperProfile.dimensions W) n) (paperBandCellLength W δ n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
          (paperBandCellLength W δ) (circularLogPotential z)) (circularLogPotential z)) :
    RealLiteralSection5Conclusions (PolynomialTaperProfile.dimensions W)
      (PolynomialTaperProfile.centers W hWposAll) (fun n => ((p.profiles W hWposAll) n).b)
      ρ := by
  have hCal := hCalibration.mono (fun z hz =>
    RealQuantitativeSection4PressureInput.toCompleted hz (paperBandCellLength W δ) W
      p.logarithmicWeightConstant p.logarithmicWeightConstant_nonneg
      (fun n _ => hWposAll n) (fun n _ => taperStateDimension_succ (W n) (hWposAll n))
      (fun n _ => Nat.sub_le _ _) (fun n _ => p.lowerParameter_pos (W n))
      (fun n _ => p.literalWeights_logarithmic (W n) (hWposAll n)))
  have hFin := hFinal.mono (fun z hz =>
    RealQuantitativeSection4PressureInput.toCompleted hz (fun n => n + 1) W
      p.logarithmicWeightConstant p.logarithmicWeightConstant_nonneg
      (fun n _ => hWposAll n) (fun n _ => taperStateDimension_succ (W n) (hWposAll n))
      (fun n _ => Nat.sub_le _ _) (fun n _ => p.lowerParameter_pos (W n))
      (fun n _ => p.literalWeights_logarithmic (W n) (hWposAll n)))
  have h := tapered_canonical_real_endpoint_of_section34 p W hWposAll L
    (realLogarithmicSection4Constant p.logarithmicWeightConstant L) ρ δ γ
    hL hδ hδγ hγ hW hfit hDensity hInt hSecond hCal hFin h3
  apply realLiteralSection5Conclusions_of_limits (PolynomialTaperProfile.dimensions W)
    (PolynomialTaperProfile.centers W hWposAll) (p.profiles W hWposAll)
    (fun n => p.lowerParameter_pos (W n)) ρ
    hInt hSecond ?_ h.1 h.2
  filter_upwards [hfit] with n hn
  exact (PolynomialTaperProfile.literalMatrix_band_fits n (W n) (hWposAll n)).2 hn

theorem tapered_complex_full_of_quantitative_section34
    (p : PolynomialTaperProfile) (W : ℕ → ℕ) (hWposAll : ∀ n, 0 < W n)
    (L : ℝ)
    (f : ℕ → ℂ → ENNReal) [∀ n, IsProbabilityMeasure (volume.withDensity (f n))]
    (δ γ : ℝ)
    (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, 2 * W n + 1 ≤ n + 1)
    (hDensity : ∀ n, ∀ᵐ w ∂(volume : Measure ℂ), f n w ≤ ENNReal.ofReal L)
    (hInt : ∀ n, Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity (f n)))
    (hSecond : ∀ n, ∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity (f n) ≤ 1)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), ComplexQuantitativeSection4PressureInput
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (PolynomialTaperProfile.dimensions W) (fun n => paperBandCellLength W δ n - 2 * W n)
      (fun n => literalModelCalibrationRaw n ((PolynomialTaperProfile.dimensions W) n) (paperBandCellLength W δ n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (paperBandCellLength W δ n) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      (fun n => p.lowerParameter (W n)) L z)
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), ComplexQuantitativeSection4PressureInput
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (PolynomialTaperProfile.dimensions W) (fun n => n + 1 - 2 * W n)
      (fun n => literalModelRawDeterminant n ((PolynomialTaperProfile.dimensions W) n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (n + 1) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      (fun n => p.lowerParameter (W n)) L z)
    (h3 :
      let : ∀ n, IsProbabilityMeasure
          (iidMeasure (volume.withDensity (f n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2))) :=
        fun n => iidMeasure_isProbability (volume.withDensity (f n)) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
        (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
        (literalShortLogPotential (PolynomialTaperProfile.dimensions W) (PolynomialTaperProfile.centers W hWposAll) (fun n => ((p.profiles W hWposAll) n).b) (paperNaturalShortBranch W γ) z)
        (literalActiveNormalizedObservable (literalLongActive (paperSafeShortBranch W δ γ))
          (fun n => literalModelCalibrationRaw n ((PolynomialTaperProfile.dimensions W) n) (paperBandCellLength W δ n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
          (paperBandCellLength W δ) (circularLogPotential z)) (circularLogPotential z)) :
    LiteralSection5Conclusions (PolynomialTaperProfile.dimensions W)
      (PolynomialTaperProfile.centers W hWposAll) (fun n => ((p.profiles W hWposAll) n).b)
      (fun n => volume.withDensity (f n)) := by
  have hCal := hCalibration.mono (fun z hz =>
    ComplexQuantitativeSection4PressureInput.toCompleted hz (paperBandCellLength W δ) W
      p.logarithmicWeightConstant p.logarithmicWeightConstant_nonneg
      (fun n _ => hWposAll n) (fun n _ => taperStateDimension_succ (W n) (hWposAll n))
      (fun n _ => Nat.sub_le _ _) (fun n _ => p.lowerParameter_pos (W n))
      (fun n _ => p.literalWeights_logarithmic (W n) (hWposAll n)))
  have hFin := hFinal.mono (fun z hz =>
    ComplexQuantitativeSection4PressureInput.toCompleted hz (fun n => n + 1) W
      p.logarithmicWeightConstant p.logarithmicWeightConstant_nonneg
      (fun n _ => hWposAll n) (fun n _ => taperStateDimension_succ (W n) (hWposAll n))
      (fun n _ => Nat.sub_le _ _) (fun n _ => p.lowerParameter_pos (W n))
      (fun n _ => p.literalWeights_logarithmic (W n) (hWposAll n)))
  have h := tapered_canonical_complex_endpoint_of_section34 p W hWposAll L
    (complexLogarithmicSection4Constant p.logarithmicWeightConstant L) f δ γ
    hL hδ hδγ hγ hW hfit hDensity hInt hSecond hCal hFin h3
  apply literalSection5Conclusions_of_limits (PolynomialTaperProfile.dimensions W)
    (PolynomialTaperProfile.centers W hWposAll) (p.profiles W hWposAll)
    (fun n => p.lowerParameter_pos (W n)) (fun n => volume.withDensity (f n))
    hInt hSecond ?_ h.1 h.2
  filter_upwards [hfit] with n hn
  exact (PolynomialTaperProfile.literalMatrix_band_fits n (W n) (hWposAll n)).2 hn

end CircularLawSections56.Section5

