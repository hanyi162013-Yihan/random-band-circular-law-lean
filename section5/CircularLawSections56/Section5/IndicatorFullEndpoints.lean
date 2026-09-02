import CircularLawSections56.Section5.CanonicalSection5Endpoint
import CircularLawSections56.Section5.QuantitativeSection4Inputs
import CircularLawSections56.Section5.Section5Conclusions

/-! # Full real and complex indicator-profile lifting

Only the model's finite density/moment/bandwidth assumptions, the two
quantitative finite Section 4 estimates, and Section 3's masked short-ring
anchors are inputs. Every stated Section 5 conclusion is returned together.
-/

open Filter MeasureTheory Topology
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option autoImplicit false
namespace CircularLawSections56.Section5
open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open TaoVuReplacement ShortRingAnchor

theorem indicator_real_full_of_quantitative_section34
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ L : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)]
    (δ γ : ℝ)
    (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hDim : ∀ n, d n + 1 = 2 * W n)
    (hcenter : ∀ n, center n ≠ 0)
    (hDensity : ∀ n, RealIntervalBound (ρ n) (ENNReal.ofReal L))
    (hInt : ∀ n, Integrable (fun u : ℝ => u ^ 2) (ρ n))
    (hSecond : ∀ n, ∫ u : ℝ, u ^ 2 ∂ρ n ≤ 1)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), RealQuantitativeSection4PressureInput
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      d (fun n => paperBandCellLength W δ n - (d n + 1))
      (fun n => literalModelCalibrationRaw n (d n) ((paperBandCellLength W δ) n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) ((paperBandCellLength W δ) n) (profile n) (center n) z)
      (fun _ => c₀) L z)
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), RealQuantitativeSection4PressureInput
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      d (fun n => n + 1 - (d n + 1))
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (fun _ => c₀) L z)
    (h3 :
      let : ∀ n, IsProbabilityMeasure
          (iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (realComplexAtomLaw (ρ n)) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
        (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2)))
        (literalShortLogPotential d center (fun n => (profile n).b) (paperNaturalShortBranch W γ) z)
        (literalActiveNormalizedObservable (literalLongActive (paperSafeShortBranch W δ γ))
          (fun n => literalModelCalibrationRaw n (d n) ((paperBandCellLength W δ) n) (center n) (profile n).b z)
          (paperBandCellLength W δ) (circularLogPotential z)) (circularLogPotential z)) :
    RealLiteralSection5Conclusions d center (fun n => (profile n).b)
      ρ := by
  have hProfile (n : ℕ) : |Real.log c₀| ≤ |Real.log c₀| * dimensionLogScale (d n) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_dimensionLogScale (d n)) (abs_nonneg (Real.log c₀))
  have hCal := hCalibration.mono (fun z hz =>
    RealQuantitativeSection4PressureInput.toCompleted hz (paperBandCellLength W δ) W
      |Real.log c₀| (abs_nonneg _)
      (fun n hn => (paperSafeShortBranch_active W δ γ n hn).2.1)
      (fun n _ => hDim n) (fun n _ => Nat.sub_le _ _) (fun _ _ => hc₀)
      (fun n _ => hProfile n))
  have hFin := hFinal.mono (fun z hz =>
    RealQuantitativeSection4PressureInput.toCompleted hz (fun n => n + 1) W
      |Real.log c₀| (abs_nonneg _)
      (fun n hn => (paperSafeShortBranch_active W δ γ n hn).2.1)
      (fun n _ => hDim n) (fun n _ => Nat.sub_le _ _) (fun _ _ => hc₀)
      (fun n _ => hProfile n))
  have h := literal_canonical_profile_endpoint_of_section34 d W center profile
    |Real.log c₀| (realFreshLogConstant L) (Real.log (max 1 (2 * L)) + 1)
    (realLogarithmicSection4Constant |Real.log c₀| L)
    (fun n => realComplexAtomLaw (ρ n)) δ γ (fun _ => hc₀) (abs_nonneg _)
    (realFreshLogConstant_nonneg L)
    (by linarith [Real.log_nonneg (le_max_left 1 (2 * L))])
    hδ hδγ hγ hW hfit hDim hcenter hProfile
    (fun n => AtomTransferControl.real (ρ n) L hL (hDensity n) (hInt n) (hSecond n))
    hCal hFin h3
  have hReal := real_section5_original_samples d center (fun n => (profile n).b) ρ h.1 h.2
  exact realLiteralSection5Conclusions_of_limits d center profile (fun _ => hc₀)
    ρ hInt hSecond hfit hReal.1 hReal.2

theorem indicator_complex_full_of_quantitative_section34
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ L : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (f : ℕ → ℂ → ENNReal) [∀ n, IsProbabilityMeasure (volume.withDensity (f n))]
    (δ γ : ℝ)
    (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hDim : ∀ n, d n + 1 = 2 * W n)
    (hcenter : ∀ n, center n ≠ 0)
    (hDensity : ∀ n, ∀ᵐ w ∂(volume : Measure ℂ), f n w ≤ ENNReal.ofReal L)
    (hInt : ∀ n, Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity (f n)))
    (hSecond : ∀ n, ∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity (f n) ≤ 1)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), ComplexQuantitativeSection4PressureInput
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * (d n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      d (fun n => paperBandCellLength W δ n - (d n + 1))
      (fun n => literalModelCalibrationRaw n (d n) ((paperBandCellLength W δ) n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) ((paperBandCellLength W δ) n) (profile n) (center n) z)
      (fun _ => c₀) L z)
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), ComplexQuantitativeSection4PressureInput
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * (d n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      d (fun n => n + 1 - (d n + 1))
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (fun _ => c₀) L z)
    (h3 :
      let : ∀ n, IsProbabilityMeasure
          (iidMeasure (volume.withDensity (f n)) ((n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (volume.withDensity (f n)) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
        (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * (d n + 2)))
        (literalShortLogPotential d center (fun n => (profile n).b) (paperNaturalShortBranch W γ) z)
        (literalActiveNormalizedObservable (literalLongActive (paperSafeShortBranch W δ γ))
          (fun n => literalModelCalibrationRaw n (d n) ((paperBandCellLength W δ) n) (center n) (profile n).b z)
          (paperBandCellLength W δ) (circularLogPotential z)) (circularLogPotential z)) :
    LiteralSection5Conclusions d center (fun n => (profile n).b)
      (fun n => volume.withDensity (f n)) := by
  have hProfile (n : ℕ) : |Real.log c₀| ≤ |Real.log c₀| * dimensionLogScale (d n) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_dimensionLogScale (d n)) (abs_nonneg (Real.log c₀))
  have hCal := hCalibration.mono (fun z hz =>
    ComplexQuantitativeSection4PressureInput.toCompleted hz (paperBandCellLength W δ) W
      |Real.log c₀| (abs_nonneg _)
      (fun n hn => (paperSafeShortBranch_active W δ γ n hn).2.1)
      (fun n _ => hDim n) (fun n _ => Nat.sub_le _ _) (fun _ _ => hc₀)
      (fun n _ => hProfile n))
  have hFin := hFinal.mono (fun z hz =>
    ComplexQuantitativeSection4PressureInput.toCompleted hz (fun n => n + 1) W
      |Real.log c₀| (abs_nonneg _)
      (fun n hn => (paperSafeShortBranch_active W δ γ n hn).2.1)
      (fun n _ => hDim n) (fun n _ => Nat.sub_le _ _) (fun _ _ => hc₀)
      (fun n _ => hProfile n))
  have h := literal_canonical_profile_endpoint_of_section34 d W center profile
    |Real.log c₀| (uniformFreshNegativeConstant L) ((Real.log (max 1 (Real.pi * L)) + 1) / 2)
    (complexLogarithmicSection4Constant |Real.log c₀| L)
    (fun n => volume.withDensity (f n)) δ γ (fun _ => hc₀) (abs_nonneg _)
    (by unfold uniformFreshNegativeConstant; linarith [Real.log_nonneg (le_max_left 1 (Real.pi * L))])
    (by linarith [Real.log_nonneg (le_max_left 1 (Real.pi * L))])
    hδ hδγ hγ hW hfit hDim hcenter hProfile
    (fun n => AtomTransferControl.complex (f n) L hL (hDensity n) (hInt n) (hSecond n))
    hCal hFin h3
  exact literalSection5Conclusions_of_limits d center profile (fun _ => hc₀)
    (fun n => volume.withDensity (f n)) hInt hSecond hfit h.1 h.2

end CircularLawSections56.Section5

