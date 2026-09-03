import CircularLawSections56.Section5.CanonicalSection5Endpoint
import CircularLawSections56.Section5.PublishedSection3Transport

/-! # Section 5 with the checked Section 3 theorem called internally

The two masked anchor limits are now conclusions of the published Section 3
proof. The caller supplies only its explicit literature/ensemble premises and
the finite sample/model transport. The more general receiver endpoint remains
available separately.
-/

open Filter MeasureTheory Topology
open scoped ENNReal
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5
open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open TaoVuReplacement ShortRingAnchor

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {νA νG : Measure ℂ}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure νA] [IsProbabilityMeasure νG]

theorem literal_canonical_profile_endpoint_of_published_section3
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
      ∀ᵐ z ∂(volume : Measure ℂ), PublishedSection3AnchorsTri μ νA νG
        (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
        (literalShortLogPotential d center (fun n => (profile n).b) (paperNaturalShortBranch W γ) z)
        (literalActiveNormalizedObservable (literalLongActive (paperSafeShortBranch W δ γ))
          (fun n => literalModelCalibrationRaw n (d n) ((paperBandCellLength W δ) n) (center n) (profile n).b z)
          (paperBandCellLength W δ) (circularLogPotential z)) z) :
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
  apply literal_canonical_profile_endpoint_of_section34 d W center profile A J K C4 ν
    δ γ hc₀ hA hJ hK hδ hδγ hγ hW hfit hDim hcenter hProfile hAtom hCalibration hFinal
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (ν n) _
  filter_upwards [h3] with z hz
  exact PublishedSection3AnchorsTri.toAnchors hz

end CircularLawSections56.Section5
