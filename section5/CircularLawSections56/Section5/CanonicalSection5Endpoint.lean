import CircularLawSections56.Section5.AtomSection5Endpoint
import CircularLawSections56.Section5.PaperLiteralGeometry

/-! # Section 5 endpoint with canonical cells and automatic finite geometry

No cell count, cell length, long-branch inequality, or finite fit certificate
is supplied. The short Section 3 anchor is restricted to the manuscript's
natural short branch; the finite safety filler is removed by eventual equality.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5

open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open TaoVuReplacement ShortRingAnchor

/-- Fixed-`z` canonical Section 5 log-potential endpoint.  All finite geometry,
the safe/natural branch reconciliation, and the Section 4 pressure lift are
performed without introducing a planar exceptional set. -/
theorem literal_canonical_profile_logPotential_at_of_section34
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (A J K : ℝ) (C4 : ℂ → ℝ)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (δ γ : ℝ)
    (hc₀ : ∀ n, 0 < c₀ n) (hA : 0 ≤ A) (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hDim : ∀ n, d n + 1 = 2 * W n)
    (hcenter : ∀ n, center n ≠ 0)
    (hProfile : ∀ n, |Real.log (c₀ n)| ≤ A * dimensionLogScale (d n))
    (hAtom : ∀ n, AtomTransferControl (ν n) J K)
    (z : ℂ)
    (hCalibration : CompletedSection4PressureInput
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (fun n => literalModelCalibrationRaw n (d n) (paperBandCellLength W δ n)
        (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (paperBandCellLength W δ n)
        (profile n) (center n) z)
      (paperBandCellLength W δ) W (C4 z))
    (hFinal : CompletedSection4PressureInput
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (fun n => n + 1) W (C4 z))
    (h3 :
      let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (ν n) _
      Section3IndicatorAnchorsTri
        (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
        (literalShortLogPotential d center (fun n => (profile n).b)
          (paperNaturalShortBranch W γ) z)
        (literalActiveNormalizedObservable
          (literalLongActive (paperSafeShortBranch W δ γ))
          (fun n => literalModelCalibrationRaw n (d n) (paperBandCellLength W δ n)
            (center n) (profile n).b z)
          (paperBandCellLength W δ) (circularLogPotential z))
        (circularLogPotential z)) :
    let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
      fun n => iidMeasure_isProbability (ν n) _
    TendstoInProbabilityTri
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (fun n ω => physicalLogPotential
        (literalIndicatorMatrix n (d n) (center n) (profile n).b ω) z)
      (circularLogPotential z) := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (ν n) _
  have hBranch := paperSafeShortBranch_eventually_eq_natural W δ γ hδ hδγ hW
  have h3safe : Section3IndicatorAnchorsTri
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (literalShortLogPotential d center (fun n => (profile n).b)
        (paperSafeShortBranch W δ γ) z)
      (literalActiveNormalizedObservable
        (literalLongActive (paperSafeShortBranch W δ γ))
        (fun n => literalModelCalibrationRaw n (d n) (paperBandCellLength W δ n)
          (center n) (profile n).b z)
        (paperBandCellLength W δ) (circularLogPotential z))
      (circularLogPotential z) := by
    refine ⟨?_, h3.mesoscopic⟩
    intro ε hε
    apply (h3.target_size ε hε).congr'
    filter_upwards [hBranch] with n hn
    simp only [literalShortLogPotential, hn]
  have hG := fun n hn => paperTransferReady_geometry W δ n
    (paperSafeShortBranch_active W δ γ n hn).2
  have h4 : Nonempty (CompletedSection4LongBranchData
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (fun n => literalModelCalibrationRaw n (d n) (paperBandCellLength W δ n)
        (center n) (profile n).b z)
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (paperBandCellLength W δ n)
        (profile n) (center n) z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (logarithmicModelLiftedPressure d (paperBandCellCount W δ)
        (paperBandCellLength W δ) ν profile center z)
      (paperBandCellCount W δ) (paperBandCellLength W δ) (fun n => n + 1) W δ
      (max (C4 z) (atomTransferConstant A J K z))) := by
    refine ⟨literalModel_completedSection4Data_of_atom_log
      (literalLongActive (paperSafeShortBranch W δ γ)) d
      (paperBandCellCount W δ) (paperBandCellLength W δ) W profile center z δ A J K
      (max (C4 z) (atomTransferConstant A J K z)) (le_max_right _ _) ν hc₀ hA hJ hK
      (fun n _ => hProfile n) (fun n _ => hAtom n)
      (fun n hn => (paperSafeShortBranch_active W δ γ n hn).2.1)
      (fun n hn => hDim n)
      (fun n hn => (hG n hn).1)
      (fun n hn => (Nat.le_succ (2 * W n)).trans (hG n hn).2.1)
      (fun n hn => (paperSafeShortBranch_active W δ γ n hn).2.2.2)
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun n hn => by
        rw [hDim n]
        exact (hG n hn).2.2.2.2.1)
      (fun n hn => (hG n hn).2.2.2.2.2)
      (fun n _ => hcenter n)
      (hCalibration.mono (le_max_left _ _)
        (fun n hn => (paperSafeShortBranch_active W δ γ n hn).2.1))
      (hFinal.mono (le_max_left _ _)
        (fun n hn => (paperSafeShortBranch_active W δ γ n hn).2.1))⟩
  exact logarithmic_profile_actual_logPotential_at_of_section34 d
    (paperBandCellCount W δ) (paperBandCellLength W δ) W center profile
    (fun z => max (C4 z) (atomTransferConstant A J K z)) ν
    (paperSafeShortBranch W δ γ) δ γ hδ hδγ hγ hW
    (Filter.Eventually.of_forall fun n hn =>
      (paperSafeShortBranch_active W δ γ n hn).1)
    (fun n hn => by
      have h := (hG n hn).2.1
      have hd := hDim n
      omega)
    z h4 h3safe hfit

theorem literal_canonical_profile_endpoint_of_section34
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (A J K : ℝ) (C4 : ℂ → ℝ)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (δ γ : ℝ)
    (hc₀ : ∀ n, 0 < c₀ n) (hA : 0 ≤ A) (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hDim : ∀ n, d n + 1 = 2 * W n)
    (hcenter : ∀ n, center n ≠ 0)
    (hProfile : ∀ n,
      |Real.log (c₀ n)| ≤ A * dimensionLogScale (d n))
    (hAtom : ∀ n, AtomTransferControl (ν n) J K)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (fun n => literalModelCalibrationRaw n (d n) ((paperBandCellLength W δ) n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) ((paperBandCellLength W δ) n) (profile n) (center n) z)
      (paperBandCellLength W δ) W (C4 z))
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (fun n => n + 1) W (C4 z))
    (h3 :
      let : ∀ n, IsProbabilityMeasure
          (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (ν n) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
        (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
        (literalShortLogPotential d center (fun n => (profile n).b) (paperNaturalShortBranch W γ) z)
        (literalActiveNormalizedObservable (literalLongActive (paperSafeShortBranch W δ γ))
          (fun n => literalModelCalibrationRaw n (d n) ((paperBandCellLength W δ) n) (center n) (profile n).b z)
          (paperBandCellLength W δ) (circularLogPotential z)) (circularLogPotential z)) :
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
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability _ _
  have hBranch := paperSafeShortBranch_eventually_eq_natural W δ γ hδ hδγ hW
  have h3safe : ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (literalShortLogPotential d center (fun n => (profile n).b) (paperSafeShortBranch W δ γ) z)
      (literalActiveNormalizedObservable (literalLongActive (paperSafeShortBranch W δ γ))
        (fun n => literalModelCalibrationRaw n (d n) (paperBandCellLength W δ n)
          (center n) (profile n).b z)
        (paperBandCellLength W δ) (circularLogPotential z)) (circularLogPotential z) := by
    filter_upwards [h3] with z hz
    refine ⟨?_, hz.mesoscopic⟩
    intro ε hε
    apply (hz.target_size ε hε).congr'
    filter_upwards [hBranch] with n hn
    simp only [literalShortLogPotential, hn]
  have hG := fun n hn => paperTransferReady_geometry W δ n
    (paperSafeShortBranch_active W δ γ n hn).2
  apply literal_logarithmic_profile_endpoint_of_section34 d
    (paperBandCellCount W δ) (paperBandCellLength W δ) W center profile A J K C4 ν
    (paperSafeShortBranch W δ γ) δ γ hc₀ hA hJ hK hδ hδγ hγ hW
    (Filter.Eventually.of_forall fun n hn => (paperSafeShortBranch_active W δ γ n hn).1)
    ?_ hfit (fun n hn => (paperSafeShortBranch_active W δ γ n hn).2.1)
    (fun n _ => hDim n) (fun n hn => (hG n hn).1) ?_
    (fun n hn => (paperSafeShortBranch_active W δ γ n hn).2.2.2)
    (fun _ _ => rfl) (fun _ _ => rfl) ?_ (fun n hn => (hG n hn).2.2.2.2.2)
    (fun n _ => hcenter n) (fun n _ => hProfile n) (fun n _ => hAtom n)
    (fun n => (hAtom n).logarithmic.second_integrable)
    (fun n => (hAtom n).logarithmic.second_le_one) hCalibration hFinal h3safe
  · intro n hn
    have h := (hG n hn).2.1
    have hd := hDim n
    omega
  · intro n hn
    have h := (hG n hn).2.1
    omega
  · intro n hn
    rw [hDim n]
    exact (hG n hn).2.2.2.2.1

end CircularLawSections56.Section5
