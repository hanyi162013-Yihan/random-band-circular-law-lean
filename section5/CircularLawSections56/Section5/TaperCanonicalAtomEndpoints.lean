import CircularLawSections56.Section5.TaperCanonicalEndpoint
import CircularLawSections56.Section5.RealSampleTransport

/-! # Explicit real and complex taper corollaries with no cell-geometry premises

The real theorem lives on original real IID arrays. The complex theorem lives
on the density law itself. All finite atom controls and all cell bookkeeping
are discharged, leaving the accepted Section 3/4 results explicit.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open TaoVuReplacement ShortRingAnchor

theorem tapered_canonical_real_endpoint_of_section34
    (p : PolynomialTaperProfile) (W : ℕ → ℕ) (hWposAll : ∀ n, 0 < W n)
    (L : ℝ) (C4 : ℂ → ℝ)
    (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)]
    (δ γ : ℝ)
    (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, 2 * W n + 1 ≤ n + 1)
    (hDensity : ∀ n, RealIntervalBound (ρ n) (ENNReal.ofReal L))
    (hInt : ∀ n, Integrable (fun u : ℝ => u ^ 2) (ρ n))
    (hSecond : ∀ n, ∫ u : ℝ, u ^ 2 ∂ρ n ≤ 1)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (fun n => literalModelCalibrationRaw n ((PolynomialTaperProfile.dimensions W) n) (paperBandCellLength W δ n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (paperBandCellLength W δ n) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      (paperBandCellLength W δ) W (C4 z))
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (fun n => literalModelRawDeterminant n ((PolynomialTaperProfile.dimensions W) n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (n + 1) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      (fun n => n + 1) W (C4 z))
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
    (let : ∀ n, IsProbabilityMeasure (iidMeasure (ρ n) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2))) :=
      fun n => iidMeasure_isProbability (ρ n) _
     ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
      (fun n => iidMeasure (ρ n) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (fun n ω => physicalLogPotential
        (p.literalMatrix n (W n) (hWposAll n) (realSampleComplexify _ ω)) z)
      (circularLogPotential z)) ∧
    (∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure
        (Measure.infinitePi (fun n => iidMeasure (ρ n) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2))))
        (fun n ω => realEsdTest
          (p.literalMatrix n (W n) (hWposAll n) (realSampleComplexify _ (ω n))) g)
        atTop (fun _ => ∫ w, g w ∂circularMeasure)) := by
  have h := tapered_canonical_profile_endpoint_of_section34 p W hWposAll
    (realFreshLogConstant L) (Real.log (max 1 (2 * L)) + 1) C4
    (fun n => realComplexAtomLaw (ρ n)) δ γ
    (realFreshLogConstant_nonneg L)
    (by linarith [Real.log_nonneg (le_max_left 1 (2 * L))])
    hδ hδγ hγ hW hfit
    (fun n => AtomTransferControl.real (ρ n) L hL (hDensity n) (hInt n) (hSecond n))
    hCalibration hFinal h3
  exact real_section5_original_samples (PolynomialTaperProfile.dimensions W)
    (PolynomialTaperProfile.centers W hWposAll) (fun n => ((p.profiles W hWposAll) n).b)
    ρ h.1 h.2

theorem tapered_canonical_complex_endpoint_of_section34
    (p : PolynomialTaperProfile) (W : ℕ → ℕ) (hWposAll : ∀ n, 0 < W n)
    (L : ℝ) (C4 : ℂ → ℝ)
    (f : ℕ → ℂ → ENNReal) [∀ n, IsProbabilityMeasure (volume.withDensity (f n))]
    (δ γ : ℝ)
    (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, 2 * W n + 1 ≤ n + 1)
    (hDensity : ∀ n, ∀ᵐ w ∂(volume : Measure ℂ), f n w ≤ ENNReal.ofReal L)
    (hInt : ∀ n, Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity (f n)))
    (hSecond : ∀ n, ∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity (f n) ≤ 1)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (fun n => literalModelCalibrationRaw n ((PolynomialTaperProfile.dimensions W) n) (paperBandCellLength W δ n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (paperBandCellLength W δ n) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      (paperBandCellLength W δ) W (C4 z))
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (fun n => literalModelRawDeterminant n ((PolynomialTaperProfile.dimensions W) n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (n + 1) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      (fun n => n + 1) W (C4 z))
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
    (let : ∀ n, IsProbabilityMeasure (iidMeasure (volume.withDensity (f n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2))) :=
      fun n => iidMeasure_isProbability (volume.withDensity (f n)) _
     ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (fun n ω => physicalLogPotential
        (p.literalMatrix n (W n) (hWposAll n) ω) z)
      (circularLogPotential z)) ∧
    (∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure
        (Measure.infinitePi (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2))))
        (fun n ω => realEsdTest
          (p.literalMatrix n (W n) (hWposAll n) (ω n)) g)
        atTop (fun _ => ∫ w, g w ∂circularMeasure)) := by
  apply tapered_canonical_profile_endpoint_of_section34 p W hWposAll
    (uniformFreshNegativeConstant L) ((Real.log (max 1 (Real.pi * L)) + 1) / 2) C4
    (fun n => volume.withDensity (f n)) δ γ
    (by unfold uniformFreshNegativeConstant; linarith [Real.log_nonneg (le_max_left 1 (Real.pi * L))])
    (by linarith [Real.log_nonneg (le_max_left 1 (Real.pi * L))])
    hδ hδγ hγ hW hfit
    (fun n => AtomTransferControl.complex (f n) L hL (hDensity n) (hInt n) (hSecond n))
    hCalibration hFinal h3

end CircularLawSections56.Section5

