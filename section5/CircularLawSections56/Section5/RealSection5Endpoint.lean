import CircularLawSections56.Section5.AtomSection5Endpoint

/-! # Full real-atom Section 5 branch

The real law is complexified by its exact pushforward; there is no planar
density assumption. Both logarithmic-potential and spectral conclusions are
proved from the two finite Section 4 estimates and the masked Section 3 anchors.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5

open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open TaoVuReplacement ShortRingAnchor

def realIndicatorTransferConstant (c₀ L : ℝ) (z : ℂ) : ℝ :=
  atomTransferConstant |Real.log c₀| (realFreshLogConstant L)
    (Real.log (max 1 (2 * L)) + 1) z

theorem real_literal_indicator_endpoint_of_section34
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
    (let : ∀ n, IsProbabilityMeasure (iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2))) :=
      fun n => iidMeasure_isProbability (realComplexAtomLaw (ρ n)) _
     ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2)))
      (fun n ω => physicalLogPotential
        (literalIndicatorMatrix n (d n) (center n) (profile n).b ω) z)
      (circularLogPotential z)) ∧
    (∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure
        (Measure.infinitePi (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2))))
        (fun n ω => realEsdTest
          (literalIndicatorMatrix n (d n) (center n) (profile n).b (ω n)) g)
        atTop (fun _ => ∫ w, g w ∂circularMeasure)) := by
  apply literal_logarithmic_profile_endpoint_of_section34 d q m W center profile
    |Real.log c₀| (realFreshLogConstant L) (Real.log (max 1 (2 * L)) + 1) C4
    (fun n => realComplexAtomLaw (ρ n)) shortBranch δ γ (fun _ => hc₀)
    (abs_nonneg _) (realFreshLogConstant_nonneg L)
    (by linarith [Real.log_nonneg (le_max_left 1 (2 * L))])
    hδ hδγ hγ hW hLong hsize hfit hWpos hd hm0 hReserve hFit hCount hLength hWidth hmN
    hcenter ?_ ?_ ?_ ?_ hCalibration hFinal h3
  · intro n _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_dimensionLogScale (d n)) (abs_nonneg (Real.log c₀))
  · intro n hn
    exact AtomTransferControl.real (ρ n) L hL (hDensity n hn) (hInt n) (hSecond n)
  · intro n
    exact (realComplexAtomLaw_secondMoment (ρ n) (hInt n)).1
  · intro n
    exact (realComplexAtomLaw_secondMoment (ρ n) (hInt n)).2.trans_le (hSecond n)

end CircularLawSections56.Section5
