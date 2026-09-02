import CircularLawSections56.Section5.LogarithmicProfileCircularLaw
import CircularLawSections56.Section5.Section4ConstantEnlargement

/-! # Full Section 5 endpoint from finite Section 3/4 inputs

Both the actual logarithmic potential limit and the actual empirical spectral
limit are returned. The finite atom package has real/complex constructors;
neither pressure convergence nor a comparison ensemble is an input.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5

open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open TaoVuReplacement ShortRingAnchor

theorem literal_logarithmic_profile_endpoint_of_section34
    (d q m W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (A J K : ℝ) (C4 : ℂ → ℝ)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (shortBranch : ℕ → Bool) (δ γ : ℝ)
    (hc₀ : ∀ n, 0 < c₀ n) (hA : 0 ≤ A) (hJ : 0 ≤ J) (hK : 0 ≤ K)
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
    (hProfile : ∀ n, literalLongActive shortBranch n = true →
      |Real.log (c₀ n)| ≤ A * dimensionLogScale (d n))
    (hAtom : ∀ n, literalLongActive shortBranch n = true → AtomTransferControl (ν n) J K)
    (hInt : ∀ n, Integrable (fun u : ℂ => ‖u‖ ^ 2) (ν n))
    (hSecond : ∀ n, ∫ u : ℂ, ‖u‖ ^ 2 ∂ν n ≤ 1)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (literalLongActive shortBranch)
      (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
      m W (C4 z))
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (literalLongActive shortBranch)
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (fun n => n + 1) W (C4 z))
    (h3 :
      let : ∀ n, IsProbabilityMeasure
          (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (ν n) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
        (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
        (literalShortLogPotential d center (fun n => (profile n).b) shortBranch z)
        (literalActiveNormalizedObservable (literalLongActive shortBranch)
          (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
          m (circularLogPotential z)) (circularLogPotential z)) :
    (let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
      fun n => iidMeasure_isProbability (ν n) _
     ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (fun n ω => physicalLogPotential
        (literalIndicatorMatrix n (d n) (center n) (profile n).b ω) z)
      (circularLogPotential z)) ∧
    (∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure
        (Measure.infinitePi (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))))
        (fun n ω => realEsdTest
          (literalIndicatorMatrix n (d n) (center n) (profile n).b (ω n)) g)
        atTop (fun _ => ∫ w, g w ∂circularMeasure)) := by
  have h4 : ∀ᵐ z ∂(volume : Measure ℂ), Nonempty (CompletedSection4LongBranchData
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))) (literalLongActive shortBranch)
      (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (logarithmicModelLiftedPressure d q m ν profile center z)
      q m (fun n => n + 1) W δ (max (C4 z) (atomTransferConstant A J K z))) := by
    filter_upwards [hCalibration, hFinal] with z hzCal hzFinal
    exact ⟨literalModel_completedSection4Data_of_atom_log (literalLongActive shortBranch)
      d q m W profile center z δ A J K (max (C4 z) (atomTransferConstant A J K z))
      (le_max_right _ _) ν hc₀ hA hJ hK hProfile hAtom
      hWpos hd hm0 hReserve hFit hCount hLength hWidth hmN hcenter
      (hzCal.mono (le_max_left _ _) hWpos) (hzFinal.mono (le_max_left _ _) hWpos)⟩
  exact ⟨logarithmic_profile_actual_logPotential_of_section34 d q m W center profile
      (fun z => max (C4 z) (atomTransferConstant A J K z)) ν shortBranch δ γ
      hδ hδγ hγ hW hLong hsize h4 h3 hfit,
    logarithmic_profile_circularLaw_of_section34 d q m W center profile
      (fun z => max (C4 z) (atomTransferConstant A J K z)) ν shortBranch δ γ
      hδ hδγ hγ hW hLong hsize h4 h3
      hc₀ hInt hSecond hfit⟩

end CircularLawSections56.Section5
