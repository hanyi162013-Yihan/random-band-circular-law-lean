import CircularLawSections56.Section5.RealSection3Transport

/-! # Literal Section 3/4 hypotheses entirely on real sample arrays

This is a packaging of the permitted upstream inputs, not an assumption of a
Section 5 conclusion. The two Section 4 fields are finite quantitative bounds;
the Section 3 field contains only the two branch-restricted short-ring anchors.
Both pressure functions and determinant functions are the actual model ones.
-/

open Filter MeasureTheory Topology
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights ShortRingAnchor

structure OriginalRealSection34Inputs
    (d m : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)]
    (shortBranch active : ℕ → Bool) (L : ℝ) (z : ℂ) : Prop where
  calibration : RealQuantitativeSection4PressureInput
    (fun n => iidMeasure (ρ n) ((n + 1) * (d n + 2))) active d
    (fun n => m n - (d n + 1))
    (fun n ω => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z
      (realSampleComplexify _ ω))
    (fun n r ω => literalModelPressure n (d n) (m n) (profile n) (center n) z r
      (realSampleComplexify _ ω)) c₀ L z
  finalSize : RealQuantitativeSection4PressureInput
    (fun n => iidMeasure (ρ n) ((n + 1) * (d n + 2))) active d
    (fun n => n + 1 - (d n + 1))
    (fun n ω => literalModelRawDeterminant n (d n) (center n) (profile n).b z
      (realSampleComplexify _ ω))
    (fun n r ω => literalModelPressure n (d n) (n + 1) (profile n) (center n) z r
      (realSampleComplexify _ ω)) c₀ L z
  anchors :
    let : ∀ n, IsProbabilityMeasure (iidMeasure (ρ n) ((n + 1) * (d n + 2))) :=
      fun n => iidMeasure_isProbability (ρ n) _
    Section3IndicatorAnchorsTri (fun n => iidMeasure (ρ n) ((n + 1) * (d n + 2)))
      (fun n ω => literalShortLogPotential d center (fun n => (profile n).b) shortBranch z n
        (realSampleComplexify _ ω))
      (fun n ω => literalActiveNormalizedObservable active
        (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
        m (circularLogPotential z) n (realSampleComplexify _ ω)) (circularLogPotential z)

namespace OriginalRealSection34Inputs
variable {d m : ℕ → ℕ} {center : ∀ n, Fin (d n + 1)}
    {c₀ C₀ : ℕ → ℝ} {profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n)}
    {ρ : ℕ → Measure ℝ} [∀ n, IsProbabilityMeasure (ρ n)]
    {shortBranch active : ℕ → Bool} {L : ℝ} {z : ℂ}

theorem calibration_complexify
    (h : OriginalRealSection34Inputs d m center profile ρ shortBranch active L z) :
    RealQuantitativeSection4PressureInput
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2))) active d
      (fun n => m n - (d n + 1))
      (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z) c₀ L z := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ρ n) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (ρ n) _
  let : ∀ n, IsProbabilityMeasure
      (iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (realComplexAtomLaw (ρ n)) _
  exact QuantitativeSection4PressureInput.of_measurePreserving _ _
    (fun n => realSampleComplexify ((n + 1) * (d n + 2)))
    (fun n => realSampleComplexify_measurePreserving _ (ρ n)) active d _ _ _ _ _ _ z
    (fun n => measurable_literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
    (fun n r => measurable_literalModelPressure n (d n) (m n) (profile n) (center n) z r)
    h.calibration

theorem finalSize_complexify
    (h : OriginalRealSection34Inputs d m center profile ρ shortBranch active L z) :
    RealQuantitativeSection4PressureInput
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2))) active d
      (fun n => n + 1 - (d n + 1))
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z) c₀ L z := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ρ n) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (ρ n) _
  let : ∀ n, IsProbabilityMeasure
      (iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (realComplexAtomLaw (ρ n)) _
  exact QuantitativeSection4PressureInput.of_measurePreserving _ _
    (fun n => realSampleComplexify ((n + 1) * (d n + 2)))
    (fun n => realSampleComplexify_measurePreserving _ (ρ n)) active d _ _ _ _ _ _ z
    (fun n => measurable_literalModelRawDeterminant n (d n) (center n) (profile n).b z)
    (fun n r => measurable_literalModelPressure n (d n) (n + 1) (profile n) (center n) z r)
    h.finalSize

theorem anchors_complexify
    (h : OriginalRealSection34Inputs d m center profile ρ shortBranch active L z) :
    let : ∀ n, IsProbabilityMeasure
        (iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2))) :=
      fun n => iidMeasure_isProbability (realComplexAtomLaw (ρ n)) _
    Section3IndicatorAnchorsTri
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2)))
      (literalShortLogPotential d center (fun n => (profile n).b) shortBranch z)
      (literalActiveNormalizedObservable active
        (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
        m (circularLogPotential z)) (circularLogPotential z) :=
  realLiteralSection3Inputs_complexify d m center (fun n => (profile n).b) ρ shortBranch active z
    h.anchors

end OriginalRealSection34Inputs
end CircularLawSections56.Section5
