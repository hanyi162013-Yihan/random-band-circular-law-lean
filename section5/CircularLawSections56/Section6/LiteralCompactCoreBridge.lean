import CircularLawSections56.Section5.LiteralNearEndToEndAssembly
import CircularLawSections56.Section6.Section5LongBranchBridge

/-!
# Literal Section 5 certificates into compact-core expectations

`literalNearEndToEndCertificate` constructs the certificate consumed here from the
finite physical estimates and the known Section 3 anchors.  Its deterministic mean
limit and final two-step comparison are reused directly, so no second pressure limit
or long-expectation error is assumed.  Only active-index measurability of the raw
observable and the physical raw-expectation identification remain at this boundary.
-/

open Filter MeasureTheory Topology

namespace CircularLawSections56.Section6

open CircularLawSections56.Section5

universe u

variable {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]

/-- The literal assembly certificate gives actual `L¹` convergence of its normalized
long observable.  Inactive raw observables need not be measurable. -/
theorem literalFinalClosure_l1_tendsto_zero
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (active : ℕ → Bool) (raw : ∀ n, Ω n → ℝ) (scale : ℕ → ℕ)
    (meanPressure : ℕ → ℝ) (target : ℝ)
    (hCertificate : LiteralFinalClosureCertificateTri μ
      (literalActiveNormalizedObservable active raw scale target) meanPressure target)
    (hRawMeasurable : ∀ n, active n = true → AEStronglyMeasurable (raw n) (μ n)) :
    Tendsto (fun n => ∫ ω,
      |literalActiveNormalizedObservable active raw scale target n ω - target| ∂μ n)
      atTop (𝓝 0) :=
  section5_long_l1_tendsto_zero μ
    (literalActiveNormalizedObservable active raw scale target) meanPressure target
    hCertificate.finalClosure
    (literalActiveNormalizedObservable_aestronglyMeasurable μ active raw scale target
      hRawMeasurable) hCertificate.meanPressure_tendsto

/-- Expectation convergence obtained directly from the literal Section 5 certificate,
not from its weaker convergence-in-probability projection. -/
theorem literalFinalClosure_expectation_tendsto
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (active : ℕ → Bool) (raw : ∀ n, Ω n → ℝ) (scale : ℕ → ℕ)
    (meanPressure : ℕ → ℝ) (target : ℝ)
    (hCertificate : LiteralFinalClosureCertificateTri μ
      (literalActiveNormalizedObservable active raw scale target) meanPressure target)
    (hRawMeasurable : ∀ n, active n = true → AEStronglyMeasurable (raw n) (μ n)) :
    Tendsto (section5TriangularExpectation μ
      (literalActiveNormalizedObservable active raw scale target)) atTop (𝓝 target) := by
  have hBound := section5_long_expectation_integrable_and_bound μ
    (literalActiveNormalizedObservable active raw scale target) meanPressure target
    hCertificate.finalClosure
    (literalActiveNormalizedObservable_aestronglyMeasurable μ active raw scale target
      hRawMeasurable)
  have hRate := section5LongExpectationError_tendsto_zero μ
    (literalActiveNormalizedObservable active raw scale target) meanPressure
    hCertificate.finalClosure target hCertificate.meanPressure_tendsto
  apply tendsto_iff_dist_tendsto_zero.2
  simpa only [Real.dist_eq] using squeeze_zero
    (fun n => abs_nonneg (section5TriangularExpectation μ
      (literalActiveNormalizedObservable active raw scale target) n - target))
    (fun n => (hBound n).2) hRate

/-- The literal Section 5 constructor can be fed straight into the raw compact-core
branch, including the constant `log r` shift of a fixed-scale application. -/
theorem compactCore_raw_expectation_tendsto_of_literalCertificate
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (active : ℕ → Bool) (raw : ∀ n, Ω n → ℝ) (scale : ℕ → ℕ)
    (meanPressure : ℕ → ℝ) (target shift : ℝ)
    (hCertificate : LiteralFinalClosureCertificateTri μ
      (literalActiveNormalizedObservable active raw scale target) meanPressure target)
    (hRawMeasurable : ∀ n, active n = true → AEStronglyMeasurable (raw n) (μ n))
    (directHighBand : ℕ → Prop) (rawExpectation : ℕ → ℝ)
    (section3AnchorError directCenteringError : ℕ → ℝ)
    (hSection3AnchorError : ∀ n, 0 ≤ section3AnchorError n)
    (hDirectCenteringError : ∀ n, 0 ≤ directCenteringError n)
    (hDirect : ∀ n, directHighBand n →
      |rawExpectation n - (shift + target)| ≤
        section3AnchorError n + directCenteringError n)
    (hSection3AnchorZero : Tendsto section3AnchorError atTop (𝓝 0))
    (hDirectCenteringZero : Tendsto directCenteringError atTop (𝓝 0))
    (hRawLongIdentification : ∀ n, ¬ directHighBand n →
      rawExpectation n = shift + section5TriangularExpectation μ
        (literalActiveNormalizedObservable active raw scale target) n) :
    Tendsto rawExpectation atTop (𝓝 (shift + target)) :=
  compactCore_raw_expectation_tendsto_of_section5_finalClosure μ
    (literalActiveNormalizedObservable active raw scale target) meanPressure target shift
    hCertificate.finalClosure
    (literalActiveNormalizedObservable_aestronglyMeasurable μ active raw scale target
      hRawMeasurable) hCertificate.meanPressure_tendsto
    directHighBand rawExpectation section3AnchorError directCenteringError
    hSection3AnchorError hDirectCenteringError hDirect hSection3AnchorZero
    hDirectCenteringZero hRawLongIdentification

/-- Full raw/cutoff compact-core assembly from the literal Section 5 certificate.
The direct raw estimates and both cutoff comparison estimates remain explicit. -/
theorem compact_gaussian_core_of_literalCertificate
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (active : ℕ → Bool) (raw : ∀ n, Ω n → ℝ) (scale : ℕ → ℕ)
    (meanPressure : ℕ → ℝ) (target shift cutoffTarget : ℝ)
    (hCertificate : LiteralFinalClosureCertificateTri μ
      (literalActiveNormalizedObservable active raw scale target) meanPressure target)
    (hRawMeasurable : ∀ n, active n = true → AEStronglyMeasurable (raw n) (μ n))
    (directHighBand : ℕ → Prop) (rawExpectation cutoffExpectation : ℕ → ℝ)
    (section3AnchorError directCenteringError : ℕ → ℝ)
    (directComparisonError longPeriodicizationError : ℕ → ℝ)
    (hSection3AnchorError : ∀ n, 0 ≤ section3AnchorError n)
    (hDirectCenteringError : ∀ n, 0 ≤ directCenteringError n)
    (hDirectComparisonError : ∀ n, 0 ≤ directComparisonError n)
    (hLongPeriodicizationError : ∀ n, 0 ≤ longPeriodicizationError n)
    (hRawDirect : ∀ n, directHighBand n →
      |rawExpectation n - (shift + target)| ≤
        section3AnchorError n + directCenteringError n)
    (hRawLongIdentification : ∀ n, ¬ directHighBand n →
      rawExpectation n = shift + section5TriangularExpectation μ
        (literalActiveNormalizedObservable active raw scale target) n)
    (hCutoffDirect : ∀ n, directHighBand n →
      |cutoffExpectation n - cutoffTarget| ≤ directComparisonError n)
    (hCutoffLong : ∀ n, ¬ directHighBand n →
      |cutoffExpectation n - cutoffTarget| ≤ longPeriodicizationError n)
    (hSection3AnchorZero : Tendsto section3AnchorError atTop (𝓝 0))
    (hDirectCenteringZero : Tendsto directCenteringError atTop (𝓝 0))
    (hDirectComparisonZero : Tendsto directComparisonError atTop (𝓝 0))
    (hLongPeriodicizationZero : Tendsto longPeriodicizationError atTop (𝓝 0)) :
    Tendsto rawExpectation atTop (𝓝 (shift + target)) ∧
      Tendsto cutoffExpectation atTop (𝓝 cutoffTarget) :=
  compact_gaussian_core_of_section5_finalClosure μ
    (literalActiveNormalizedObservable active raw scale target) meanPressure
    target shift cutoffTarget hCertificate.finalClosure
    (literalActiveNormalizedObservable_aestronglyMeasurable μ active raw scale target
      hRawMeasurable) hCertificate.meanPressure_tendsto
    directHighBand rawExpectation cutoffExpectation section3AnchorError directCenteringError
    directComparisonError longPeriodicizationError hSection3AnchorError hDirectCenteringError
    hDirectComparisonError hLongPeriodicizationError hRawDirect hRawLongIdentification
    hCutoffDirect hCutoffLong hSection3AnchorZero hDirectCenteringZero hDirectComparisonZero
    hLongPeriodicizationZero

end CircularLawSections56.Section6
