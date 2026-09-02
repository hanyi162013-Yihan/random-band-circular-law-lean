import CircularLawSections56.Section5.AtomSection5Endpoint
import CircularLawSections56.Section5.TaperLiteralProfile

/-! # Polynomial taper corollary, at the exact model and spectral level

The normalized sampled taper is used in the matrix itself. Its polynomially
small endpoint weights yield one fixed logarithmic transfer constant.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5

open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open TaoVuReplacement ShortRingAnchor

theorem tapered_profile_endpoint_of_section34
    (p : PolynomialTaperProfile) (W q m : ℕ → ℕ) (hWposAll : ∀ n, 0 < W n)
    (J K : ℝ) (C4 : ℂ → ℝ)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (shortBranch : ℕ → Bool) (δ γ : ℝ)
    (hJ : 0 ≤ J) (hK : 0 ≤ K)
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
    (hAtom : ∀ n, literalLongActive shortBranch n = true → AtomTransferControl (ν n) J K)
    (hInt : ∀ n, Integrable (fun u : ℂ => ‖u‖ ^ 2) (ν n))
    (hSecond : ∀ n, ∫ u : ℂ, ‖u‖ ^ 2 ∂ν n ≤ 1)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (ν n) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive shortBranch)
      (fun n => literalModelCalibrationRaw n ((PolynomialTaperProfile.dimensions W) n) (m n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (m n) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      m W (C4 z))
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (ν n) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
      (literalLongActive shortBranch)
      (fun n => literalModelRawDeterminant n ((PolynomialTaperProfile.dimensions W) n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
      (fun n => literalModelPressure n ((PolynomialTaperProfile.dimensions W) n) (n + 1) ((p.profiles W hWposAll) n) ((PolynomialTaperProfile.centers W hWposAll) n) z)
      (fun n => n + 1) W (C4 z))
    (h3 :
      let : ∀ n, IsProbabilityMeasure
          (iidMeasure (ν n) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2))) :=
        fun n => iidMeasure_isProbability (ν n) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
        (fun n => iidMeasure (ν n) ((n + 1) * ((PolynomialTaperProfile.dimensions W) n + 2)))
        (literalShortLogPotential (PolynomialTaperProfile.dimensions W) (PolynomialTaperProfile.centers W hWposAll) (fun n => ((p.profiles W hWposAll) n).b) shortBranch z)
        (literalActiveNormalizedObservable (literalLongActive shortBranch)
          (fun n => literalModelCalibrationRaw n ((PolynomialTaperProfile.dimensions W) n) (m n) ((PolynomialTaperProfile.centers W hWposAll) n) ((p.profiles W hWposAll) n).b z)
          m (circularLogPotential z)) (circularLogPotential z)) :
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
  apply literal_logarithmic_profile_endpoint_of_section34
    (PolynomialTaperProfile.dimensions W) q m W
    (PolynomialTaperProfile.centers W hWposAll) (p.profiles W hWposAll)
    p.logarithmicWeightConstant J K C4 ν shortBranch δ γ
    (fun n => p.lowerParameter_pos (W n)) p.logarithmicWeightConstant_nonneg hJ hK
    hδ hδγ hγ hW hLong ?_ ?_ (fun n _ => hWposAll n)
    (fun n _ => taperStateDimension_succ (W n) (hWposAll n))
    hm0 hReserve hFit hCount hLength ?_ hmN
    (fun n _ => taperCenter_ne_zero (W n) (hWposAll n))
    (fun n _ => p.literalWeights_logarithmic (W n) (hWposAll n))
    hAtom hInt hSecond hCalibration hFinal h3
  · intro n hn
    exact (PolynomialTaperProfile.literalMatrix_band_fits n (W n) (hWposAll n)).2 (hsize n hn)
  · filter_upwards [hfit] with n hn
    exact (PolynomialTaperProfile.literalMatrix_band_fits n (W n) (hWposAll n)).2 hn
  · intro n hn
    change taperStateDimension (W n) + 1 ≤ m n
    rw [taperStateDimension_succ (W n) (hWposAll n)]
    exact hWidth n hn

end CircularLawSections56.Section5
