import CircularLawSections56.Section5.CanonicalSection5Endpoint
import CircularLawSections56.Section5.TaperLiteralProfile

/-! # Polynomial taper endpoint with canonical geometry

The sampled taper, all transfer constants, the cells, and the finite-prefix
safety branch are explicit. Only the accepted Section 3/4 inputs and the model's
finite density/moment and bandwidth hypotheses remain.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1800000
set_option autoImplicit false

namespace CircularLawSections56.Section5

open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open TaoVuReplacement ShortRingAnchor

theorem tapered_canonical_profile_endpoint_of_section34
    (p : PolynomialTaperProfile) (W : ℕ → ℕ) (hWposAll : ∀ n, 0 < W n)
    (J K : ℝ) (C4 : ℂ → ℝ)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (δ γ : ℝ)
    (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, 2 * W n + 1 ≤ n + 1)
    (hAtom : ∀ n, AtomTransferControl (ν n) J K)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (ν n) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (fun n => literalModelCalibrationRaw n ((PolynomialTaperProfile.dimensions W) n) (paperBandCellLength W δ n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (paperBandCellLength W δ n) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      (paperBandCellLength W δ) W (C4 z))
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (ν n) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (fun n => literalModelRawDeterminant n ((PolynomialTaperProfile.dimensions W) n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (n + 1) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      (fun n => n + 1) W (C4 z))
    (h3 :
      let : ∀ n, IsProbabilityMeasure
          (iidMeasure (ν n) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2))) :=
        fun n => iidMeasure_isProbability (ν n) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
        (fun n => iidMeasure (ν n) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
        (literalShortLogPotential (PolynomialTaperProfile.dimensions W) (PolynomialTaperProfile.centers W hWposAll) (fun n => ((p.profiles W hWposAll) n).b) (paperNaturalShortBranch W γ) z)
        (literalActiveNormalizedObservable (literalLongActive (paperSafeShortBranch W δ γ))
          (fun n => literalModelCalibrationRaw n ((PolynomialTaperProfile.dimensions W) n) (paperBandCellLength W δ n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
          (paperBandCellLength W δ) (circularLogPotential z)) (circularLogPotential z)) :
    (let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2))) :=
      fun n => iidMeasure_isProbability (ν n) _
     ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
      (fun n => iidMeasure (ν n) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (fun n ω => physicalLogPotential
        (p.literalMatrix n (W n) (hWposAll n) ω) z)
      (circularLogPotential z)) ∧
    (∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure
        (Measure.infinitePi (fun n => iidMeasure (ν n) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2))))
        (fun n ω => realEsdTest
          (p.literalMatrix n (W n) (hWposAll n) (ω n)) g)
        atTop (fun _ => ∫ w, g w ∂circularMeasure)) := by
  apply literal_canonical_profile_endpoint_of_section34
    (PolynomialTaperProfile.dimensions W) W
    (PolynomialTaperProfile.centers W hWposAll) (p.profiles W hWposAll)
    p.logarithmicWeightConstant J K C4 ν δ γ
    (fun n => p.lowerParameter_pos (W n)) p.logarithmicWeightConstant_nonneg hJ hK
    hδ hδγ hγ hW ?_
    (fun n => taperStateDimension_succ (W n) (hWposAll n))
    (fun n => taperCenter_ne_zero (W n) (hWposAll n))
    (fun n => p.literalWeights_logarithmic (W n) (hWposAll n))
    hAtom hCalibration hFinal h3
  filter_upwards [hfit] with n hn
  exact (PolynomialTaperProfile.literalMatrix_band_fits n (W n) (hWposAll n)).2 hn

end CircularLawSections56.Section5

