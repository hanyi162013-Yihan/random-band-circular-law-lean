import CircularLawSection6.ClampedSection5Source
import CircularLawSections56.Section5.PublishedSection3Endpoint

/-! # Clamped-core Section 5 input from the checked Section 3 theorem

The two Section 3 probability limits are derived from its published density
theorems and finite sample/model transports. No short-ring or core probability
limit is an input. External literature hypotheses remain inside the source data.
-/

open MeasureTheory Filter Topology ShortRingAnchor TaoVuReplacement
open CircularLawSection4
open CircularLawSections56.Section5 CircularLawSections56.Section6
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CircularLawSection6.CoreRadiusBounds
variable {p : NoncompactProfile} {R : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} {νA νG : Measure ℂ}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure νA] [IsProbabilityMeasure νG]

structure PublishedSection34Input (B : CoreRadiusBounds p R)
    (μ : Measure Ω) (νA νG : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure νA] [IsProbabilityMeasure νG]
    (W : ℕ → ℝ) : Prop where
  calibration : ∀ᵐ z ∂(volume : Measure ℂ), ComplexQuantitativeSection4PressureInput
    (clampedCoreSampleLaw R W)
    (literalLongActive (paperSafeShortBranch (fun n => clampedCoreHalfWidth R (W n) n)
      coreSection5Delta coreSection5Gamma))
    (clampedCoreBand R W)
    (fun n => paperBandCellLength (fun k => clampedCoreHalfWidth R (W k) k) coreSection5Delta n -
      (clampedCoreBand R W n + 1))
    (fun n => literalModelCalibrationRaw n (clampedCoreBand R W n)
      (paperBandCellLength (fun k => clampedCoreHalfWidth R (W k) k) coreSection5Delta n)
      (clampedCoreCenter R W n) (B.clampedWeights (W n) n).b z)
    (fun n => literalModelPressure n (clampedCoreBand R W n)
      (paperBandCellLength (fun k => clampedCoreHalfWidth R (W k) k) coreSection5Delta n)
      (B.clampedWeights (W n) n) (clampedCoreCenter R W n) z)
    (fun _ => B.lower / B.upper) 2 z
  finalPressure : ∀ᵐ z ∂(volume : Measure ℂ), ComplexQuantitativeSection4PressureInput
    (clampedCoreSampleLaw R W)
    (literalLongActive (paperSafeShortBranch (fun n => clampedCoreHalfWidth R (W n) n)
      coreSection5Delta coreSection5Gamma))
    (clampedCoreBand R W) (fun n => n + 1 - (clampedCoreBand R W n + 1))
    (fun n => literalModelRawDeterminant n (clampedCoreBand R W n)
      (clampedCoreCenter R W n) (B.clampedWeights (W n) n).b z)
    (fun n => literalModelPressure n (clampedCoreBand R W n) (n + 1)
      (B.clampedWeights (W n) n) (clampedCoreCenter R W n) z)
    (fun _ => B.lower / B.upper) 2 z
  anchors : ∀ᵐ z ∂(volume : Measure ℂ), PublishedSection3AnchorsTri μ νA νG
    (clampedCoreSampleLaw R W)
    (literalShortLogPotential (clampedCoreBand R W) (clampedCoreCenter R W)
      (fun n => (B.clampedWeights (W n) n).b)
      (paperNaturalShortBranch (fun n => clampedCoreHalfWidth R (W n) n) coreSection5Gamma) z)
    (literalActiveNormalizedObservable
      (literalLongActive (paperSafeShortBranch (fun n => clampedCoreHalfWidth R (W n) n)
        coreSection5Delta coreSection5Gamma))
      (fun n => literalModelCalibrationRaw n (clampedCoreBand R W n)
        (paperBandCellLength (fun k => clampedCoreHalfWidth R (W k) k) coreSection5Delta n)
        (clampedCoreCenter R W n) (B.clampedWeights (W n) n).b z)
      (paperBandCellLength (fun n => clampedCoreHalfWidth R (W n) n) coreSection5Delta)
      (circularLogPotential z)) z


theorem PublishedSection34Input.toSection34
    (B : CoreRadiusBounds p R) (W : ℕ → ℝ)
    (h : B.PublishedSection34Input μ νA νG W) : B.Section34Input W where
  calibration := h.calibration
  finalPressure := h.finalPressure
  anchors := h.anchors.mono (fun _ hz => PublishedSection3AnchorsTri.toAnchors hz)

theorem PublishedSection34Input.logPotential
    (B : CoreRadiusBounds p R) (W : ℕ → ℝ)
    (hR : 0 < R) (hW : Tendsto W atTop atTop)
    (h : B.PublishedSection34Input μ νA νG W) :
    ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri (clampedCoreSampleLaw R W)
      (fun n ω => physicalLogPotential (literalIndicatorMatrix n (clampedCoreBand R W n)
        (clampedCoreCenter R W n) (B.clampedWeights (W n) n).b ω) z)
      (circularRadialPotential ‖z‖) :=
  Section34Input.logPotential B W hR hW (PublishedSection34Input.toSection34 B W h)

end CircularLawSection6.CoreRadiusBounds
