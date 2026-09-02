import CircularLawSections56.Section5.RealUpstreamTransport

/-! # The accepted Section 3 anchors on the original real probability space

The branch masks and normalization commute with complexification. This adapter
proves measurability of the actual observables, so the original real Section 3
limits can be supplied directly, without a complex probability-space premise.
-/

open Filter MeasureTheory Topology
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1400000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open Section6 CircularLawSection4 ShortRingAnchor

theorem measurable_literalShortLogPotential
    (d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) (b : ∀ n, Fin (d n + 2) → ℂ)
    (shortBranch : ℕ → Bool) (z : ℂ) (n : ℕ) :
    Measurable (literalShortLogPotential d center b shortBranch z n) := by
  unfold literalShortLogPotential
  cases shortBranch n
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact measurable_const
  · simp only [↓reduceIte]
    exact measurable_physicalLogPotential _
      (filledLiteralIndicatorMatrix_measurable n (d n) (center n) (b n)) z

theorem measurable_literalActiveNormalizedObservable
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (active : ℕ → Bool) (raw : ∀ n, Ω n → ℝ) (scale : ℕ → ℕ) (target : ℝ)
    (hraw : ∀ n, Measurable (raw n)) (n : ℕ) :
    Measurable (literalActiveNormalizedObservable active raw scale target n) := by
  unfold literalActiveNormalizedObservable
  cases active n
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact measurable_const
  · simp only [↓reduceIte]
    exact (hraw n).div_const _

theorem Section3IndicatorAnchorsTri.of_measurePreserving
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (μ : ∀ n, Measure (Ω n)) (ν : ∀ n, Measure (Ξ n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (F : ∀ n, Ω n → Ξ n) (hF : ∀ n, MeasurePreserving (F n) (μ n) (ν n))
    (short calibration : ∀ n, Ξ n → ℝ) (target : ℝ)
    (hshort : ∀ n, Measurable (short n)) (hcal : ∀ n, Measurable (calibration n))
    (h3 : Section3IndicatorAnchorsTri μ (fun n ω => short n (F n ω))
      (fun n ω => calibration n (F n ω)) target) :
    Section3IndicatorAnchorsTri ν short calibration target :=
  ⟨tendstoInProbabilityTri_pushforward_measurePreserving μ ν F hF short hshort target
      h3.target_size,
    tendstoInProbabilityTri_pushforward_measurePreserving μ ν F hF calibration hcal target
      h3.mesoscopic⟩

theorem realLiteralSection3Inputs_complexify
    (d m : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) (b : ∀ n, Fin (d n + 2) → ℂ)
    (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)]
    (shortBranch active : ℕ → Bool) (z : ℂ)
    (h3 :
      let : ∀ n, IsProbabilityMeasure (iidMeasure (ρ n) ((n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (ρ n) _
      Section3IndicatorAnchorsTri (fun n => iidMeasure (ρ n) ((n + 1) * (d n + 2)))
        (fun n ω => literalShortLogPotential d center b shortBranch z n (realSampleComplexify _ ω))
        (fun n ω => literalActiveNormalizedObservable active
          (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (b n) z)
          m (circularLogPotential z) n (realSampleComplexify _ ω)) (circularLogPotential z)) :
    let : ∀ n, IsProbabilityMeasure
        (iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2))) :=
      fun n => iidMeasure_isProbability (realComplexAtomLaw (ρ n)) _
    Section3IndicatorAnchorsTri
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2)))
      (literalShortLogPotential d center b shortBranch z)
      (literalActiveNormalizedObservable active
        (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (b n) z)
        m (circularLogPotential z)) (circularLogPotential z) := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ρ n) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (ρ n) _
  let : ∀ n, IsProbabilityMeasure
      (iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (realComplexAtomLaw (ρ n)) _
  exact Section3IndicatorAnchorsTri.of_measurePreserving
    (fun n => iidMeasure (ρ n) ((n + 1) * (d n + 2)))
    (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2)))
    (fun n => realSampleComplexify ((n + 1) * (d n + 2)))
    (fun n => realSampleComplexify_measurePreserving _ (ρ n)) _ _ _
    (measurable_literalShortLogPotential d center b shortBranch z)
    (measurable_literalActiveNormalizedObservable active _ m _
      (fun n => measurable_literalModelCalibrationRaw n (d n) (m n) (center n) (b n) z)) h3

end CircularLawSections56.Section5
