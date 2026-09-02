import CircularLawSections56.Section5.RealSection5Endpoint
import CircularLawSections56.Section5.TaperAtomEndpoints
import CircularLawSections56.Section5.RealSampleTransport

/-! # Public real-atom endpoints on original real IID arrays -/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5

open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open TaoVuReplacement ShortRingAnchor

theorem real_literal_indicator_original_samples_of_section34
    (d q m W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ L : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)]
    (C4 : ℂ → ℝ)
    (shortBranch : ℕ → Bool) (δ γ : ℝ)
    (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hLong : ∀ᶠ n in atTop, literalLongActive shortBranch n = true →
      (W n : ℝ) ^ (1 + γ) < (n + 1 : ℝ))
    (hsize : ∀ n, literalLongActive shortBranch n = true → d n + 2 ≤ n + 1)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hWpos : ∀ n, literalLongActive shortBranch n = true → 0 < W n)
    (hd : ∀ n, literalLongActive shortBranch n = true → d n + 1 = 2 * W n)
    (hm0 : ∀ n, literalLongActive shortBranch n = true → 0 < paperMesoscopicCellLength δ W n)
    (hReserve : ∀ n, literalLongActive shortBranch n = true → 2 * W n ≤ n + 1)
    (hFit : ∀ n, literalLongActive shortBranch n = true →
      2 * paperMesoscopicCellLength δ W n ≤ n + 1 - 2 * W n)
    (hCount : ∀ n, literalLongActive shortBranch n = true →
      q n = balancedCellCount (n + 1 - 2 * W n) (paperMesoscopicCellLength δ W n))
    (hLength : ∀ n, literalLongActive shortBranch n = true →
      m n = balancedCellLength (n + 1 - 2 * W n) (paperMesoscopicCellLength δ W n))
    (hWidth : ∀ n, literalLongActive shortBranch n = true → d n + 1 ≤ m n)
    (hmN : ∀ n, literalLongActive shortBranch n = true → m n ≤ n + 1)
    (hcenter : ∀ n, literalLongActive shortBranch n = true → center n ≠ 0)
    (hDensity : ∀ n, literalLongActive shortBranch n = true →
      RealIntervalBound (ρ n) (ENNReal.ofReal L))
    (hInt : ∀ n, Integrable (fun u : ℝ => u ^ 2) (ρ n))
    (hSecond : ∀ n, ∫ u : ℝ, u ^ 2 ∂ρ n ≤ 1)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2)))
      (literalLongActive shortBranch)
      (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
      m W (C4 z))
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2)))
      (literalLongActive shortBranch)
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (fun n => n + 1) W (C4 z))
    (h3 :
      let : ∀ n, IsProbabilityMeasure
          (iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (realComplexAtomLaw (ρ n)) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
        (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2)))
        (literalShortLogPotential d center (fun n => (profile n).b) shortBranch z)
        (literalActiveNormalizedObservable (literalLongActive shortBranch)
          (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
          m (circularLogPotential z)) (circularLogPotential z)) :
    (let : ∀ n, IsProbabilityMeasure (iidMeasure (ρ n) ((n + 1) * (d n + 2))) :=
      fun n => iidMeasure_isProbability (ρ n) _
     ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
      (fun n => iidMeasure (ρ n) ((n + 1) * (d n + 2)))
      (fun n ω => physicalLogPotential
        (literalIndicatorMatrix n (d n) (center n) (profile n).b (realSampleComplexify _ ω)) z)
      (circularLogPotential z)) ∧
    (∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure
        (Measure.infinitePi (fun n => iidMeasure (ρ n) ((n + 1) * (d n + 2))))
        (fun n ω => realEsdTest
          (literalIndicatorMatrix n (d n) (center n) (profile n).b (realSampleComplexify _ (ω n))) g)
        atTop (fun _ => ∫ w, g w ∂circularMeasure)) := by
  have h := real_literal_indicator_endpoint_of_section34 d q m W center profile ρ C4
    shortBranch δ γ hc₀ hL hδ hδγ hγ hW hLong hsize hfit hWpos hd hm0 hReserve hFit
    hCount hLength hWidth hmN hcenter hDensity hInt hSecond hCalibration hFinal h3
  exact real_section5_original_samples d center (fun n => (profile n).b) ρ h.1 h.2

theorem tapered_real_original_samples_of_section34
    (p : PolynomialTaperProfile) (W q m : ℕ → ℕ) (hWposAll : ∀ n, 0 < W n)
    (L : ℝ) (C4 : ℂ → ℝ)
    (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)]
    (shortBranch : ℕ → Bool) (δ γ : ℝ)
    (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hLong : ∀ᶠ n in atTop, literalLongActive shortBranch n = true →
      (W n : ℝ) ^ (1 + γ) < (n + 1 : ℝ))
    (hsize : ∀ n, literalLongActive shortBranch n = true → 2 * W n + 1 ≤ n + 1)
    (hfit : ∀ᶠ n in atTop, 2 * W n + 1 ≤ n + 1)
    (hm0 : ∀ n, literalLongActive shortBranch n = true → 0 < paperMesoscopicCellLength δ W n)
    (hReserve : ∀ n, literalLongActive shortBranch n = true → 2 * W n ≤ n + 1)
    (hFit : ∀ n, literalLongActive shortBranch n = true →
      2 * paperMesoscopicCellLength δ W n ≤ n + 1 - 2 * W n)
    (hCount : ∀ n, literalLongActive shortBranch n = true →
      q n = balancedCellCount (n + 1 - 2 * W n) (paperMesoscopicCellLength δ W n))
    (hLength : ∀ n, literalLongActive shortBranch n = true →
      m n = balancedCellLength (n + 1 - 2 * W n) (paperMesoscopicCellLength δ W n))
    (hWidth : ∀ n, literalLongActive shortBranch n = true → 2 * W n ≤ m n)
    (hmN : ∀ n, literalLongActive shortBranch n = true → m n ≤ n + 1)
    (hDensity : ∀ n, literalLongActive shortBranch n = true →
      RealIntervalBound (ρ n) (ENNReal.ofReal L))
    (hInt : ∀ n, Integrable (fun u : ℝ => u ^ 2) (ρ n))
    (hSecond : ∀ n, ∫ u : ℝ, u ^ 2 ∂ρ n ≤ 1)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive shortBranch)
      (fun n => literalModelCalibrationRaw n ((PolynomialTaperProfile.dimensions W) n) (m n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (m n) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      m W (C4 z))
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive shortBranch)
      (fun n => literalModelRawDeterminant n ((PolynomialTaperProfile.dimensions W) n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (n + 1) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      (fun n => n + 1) W (C4 z))
    (h3 :
      let : ∀ n, IsProbabilityMeasure
          (iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2))) :=
        fun n => iidMeasure_isProbability (realComplexAtomLaw (ρ n)) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
        (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
        (literalShortLogPotential (PolynomialTaperProfile.dimensions W) (PolynomialTaperProfile.centers W hWposAll) (fun n => ((p.profiles W hWposAll) n).b) shortBranch z)
        (literalActiveNormalizedObservable (literalLongActive shortBranch)
          (fun n => literalModelCalibrationRaw n ((PolynomialTaperProfile.dimensions W) n) (m n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
          m (circularLogPotential z)) (circularLogPotential z)) :
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
  have h := tapered_real_endpoint_of_section34 p W q m hWposAll L C4 ρ shortBranch δ γ
    hL hδ hδγ hγ hW hLong hsize hfit hm0 hReserve hFit hCount hLength hWidth hmN
    hDensity hInt hSecond hCalibration hFinal h3
  exact real_section5_original_samples (PolynomialTaperProfile.dimensions W)
    (PolynomialTaperProfile.centers W hWposAll) (fun n => ((p.profiles W hWposAll) n).b)
    ρ h.1 h.2

end CircularLawSections56.Section5
