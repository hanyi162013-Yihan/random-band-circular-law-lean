import CircularLawSections56.Section5.TaperSection5Endpoint

/-! # Explicit real- and complex-density instances of the taper corollary

Only density/moment assumptions, deterministic scale geometry, and the accepted
finite Section 3/4 inputs remain. The finite atom package is constructed here.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5

open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open TaoVuReplacement ShortRingAnchor

theorem tapered_real_endpoint_of_section34
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
    (let : ∀ n, IsProbabilityMeasure (iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2))) :=
      fun n => iidMeasure_isProbability (realComplexAtomLaw (ρ n)) _
     ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (fun n ω => physicalLogPotential
        (p.literalMatrix n (W n) (hWposAll n) ω) z)
      (circularLogPotential z)) ∧
    (∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure
        (Measure.infinitePi (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2))))
        (fun n ω => realEsdTest
          (p.literalMatrix n (W n) (hWposAll n) (ω n)) g)
        atTop (fun _ => ∫ w, g w ∂circularMeasure)) := by
  apply tapered_profile_endpoint_of_section34 p W q m hWposAll
    (realFreshLogConstant L) (Real.log (max 1 (2 * L)) + 1) C4
    (fun n => realComplexAtomLaw (ρ n)) shortBranch δ γ
    (realFreshLogConstant_nonneg L)
    (by linarith [Real.log_nonneg (le_max_left 1 (2 * L))])
    hδ hδγ hγ hW hLong hsize hfit hm0 hReserve hFit hCount hLength hWidth hmN
    ?_ ?_ ?_ hCalibration hFinal h3
  · intro n hn
    exact AtomTransferControl.real (ρ n) L hL (hDensity n hn) (hInt n) (hSecond n)
  · intro n
    exact (realComplexAtomLaw_secondMoment (ρ n) (hInt n)).1
  · intro n
    exact (realComplexAtomLaw_secondMoment (ρ n) (hInt n)).2.trans_le (hSecond n)

theorem tapered_complex_endpoint_of_section34
    (p : PolynomialTaperProfile) (W q m : ℕ → ℕ) (hWposAll : ∀ n, 0 < W n)
    (L : ℝ) (C4 : ℂ → ℝ)
    (f : ℕ → ℂ → ENNReal) [∀ n, IsProbabilityMeasure (volume.withDensity (f n))]
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
      ∀ᵐ w ∂(volume : Measure ℂ), f n w ≤ ENNReal.ofReal L)
    (hInt : ∀ n, Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity (f n)))
    (hSecond : ∀ n, ∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity (f n) ≤ 1)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive shortBranch)
      (fun n => literalModelCalibrationRaw n ((PolynomialTaperProfile.dimensions W) n) (m n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (m n) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      m W (C4 z))
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive shortBranch)
      (fun n => literalModelRawDeterminant n ((PolynomialTaperProfile.dimensions W) n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (n + 1) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      (fun n => n + 1) W (C4 z))
    (h3 :
      let : ∀ n, IsProbabilityMeasure
          (iidMeasure (volume.withDensity (f n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2))) :=
        fun n => iidMeasure_isProbability (volume.withDensity (f n)) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
        (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
        (literalShortLogPotential (PolynomialTaperProfile.dimensions W) (PolynomialTaperProfile.centers W hWposAll) (fun n => ((p.profiles W hWposAll) n).b) shortBranch z)
        (literalActiveNormalizedObservable (literalLongActive shortBranch)
          (fun n => literalModelCalibrationRaw n ((PolynomialTaperProfile.dimensions W) n) (m n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
          m (circularLogPotential z)) (circularLogPotential z)) :
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
  apply tapered_profile_endpoint_of_section34 p W q m hWposAll
    (uniformFreshNegativeConstant L) ((Real.log (max 1 (Real.pi * L)) + 1) / 2) C4
    (fun n => volume.withDensity (f n)) shortBranch δ γ
    (by unfold uniformFreshNegativeConstant; linarith [Real.log_nonneg (le_max_left 1 (Real.pi * L))])
    (by linarith [Real.log_nonneg (le_max_left 1 (Real.pi * L))])
    hδ hδγ hγ hW hLong hsize hfit hm0 hReserve hFit hCount hLength hWidth hmN
    ?_ hInt hSecond hCalibration hFinal h3
  intro n hn
  exact AtomTransferControl.complex (f n) L hL (hDensity n hn) (hInt n) (hSecond n)

end CircularLawSections56.Section5
