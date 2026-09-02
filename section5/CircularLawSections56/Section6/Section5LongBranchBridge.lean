import CircularLawSections56.Section5.NearEndToEnd
import CircularLawSections56.Section6.CompactCoreAssembly

/-!
# Section 5 expectation strength into the Section 6 long branch

Section 5 exports the long logarithmic observable through two quantitative `L¹`
comparisons: first to a random pressure, then to its deterministic mean pressure.
This file converts those comparisons into the deterministic expectation estimate used
by the long branch of `compactCore_raw_expectation_tendsto`.

The bridge does not assume the long-branch scalar conclusion.  Its only additional
analytic input is almost-everywhere strong measurability of the long observable.
Its integrability follows from the two absolute-difference bounds; no measurability
or integrability premise for the intermediate is needed.  The application-facing
wrapper leaves visible only measurability and the concrete
identification of the physical raw expectation with the integral of the Section 5
observable on long-branch indices.
-/

open Filter MeasureTheory Topology

namespace CircularLawSections56.Section6

open CircularLawSections56.Section5

universe u v

variable {Omega : Nat -> Type u} [forall n, MeasurableSpace (Omega n)]

/-- Expectation of a triangular-array observable on its index-dependent probability
space. -/
noncomputable def section5TriangularExpectation
    (mu : forall n, Measure (Omega n))
    (observable : forall n, Omega n -> Real) (n : Nat) : Real :=
  integral (mu n) (observable n)

/-- The explicit deterministic error obtained from Section 5's two `L¹` seams and the
remaining deterministic mean-pressure error. -/
def section5LongExpectationError
    (seamError fluctuationError meanPressure : Nat -> Real)
    (target : Real) (n : Nat) : Real :=
  seamError n + fluctuationError n + abs (meanPressure n - target)

/-- The deterministic whole-pressure limit that is proved internally in Section 5's
near-end-to-end theorem, exposed here for expectation-strength consumers.

The Section 3 calibration anchor remains a named ordinary premise.  The remaining
arguments are precisely Section 5's pressure lift and the Section 4-to-Section 5
quantitative certificate. -/
theorem section5_wholeMeanPressure_tendsto
    {index : Type v}
    (mu : forall n, Measure (Omega n))
    [forall n, IsProbabilityMeasure (mu n)]
    (degrees : Nat -> Finset index)
    (hdegrees : forall n, (degrees n).Nonempty)
    (shortLogPotential calibrationLogPotential longLogPotential :
      forall n, Omega n -> Real)
    (target : Real)
    (base lifted : Nat -> index -> Real) (cellCount cellLength : Nat -> Nat)
    (cellError wholeMeanPressure cellLengthRatio : Nat -> Real)
    (remainderError lengthRatioError : Nat -> Real)
    (hSection3 : Section3IndicatorAnchorsTri mu
      shortLogPotential calibrationLogPotential target)
    (hPressure : PressureLiftToTargetInputVarying degrees hdegrees
      base lifted cellCount cellLength cellError wholeMeanPressure cellLengthRatio
      remainderError lengthRatioError)
    (hSection4 : Section4LongBranchQuantitativeInputTri mu
      calibrationLogPotential longLogPotential
      (baseNormalizedPressureVarying degrees hdegrees base cellLength)
      wholeMeanPressure) :
    Tendsto wholeMeanPressure atTop (nhds target) := by
  have hBaseTarget : Tendsto
      (baseNormalizedPressureVarying degrees hdegrees base cellLength)
      atTop (nhds target) := by
    exact deterministic_center_tendsto_of_tri_anchor_and_two_L1_seams
      mu calibrationLogPotential hSection4.calibration.intermediate
      (baseNormalizedPressureVarying degrees hdegrees base cellLength)
      hSection4.calibration.seamError
      hSection4.calibration.fluctuationError target hSection3.mesoscopic
      hSection4.calibration.seamIntegrable
      hSection4.calibration.seamIntegral_le
      hSection4.calibration.fluctuationIntegrable
      hSection4.calibration.fluctuationIntegral_le
      hSection4.calibration.seamError_tendsto_zero
      hSection4.calibration.fluctuationError_tendsto_zero
  have hCellTarget : Tendsto
      (cellNormalizedPressureVarying degrees hdegrees lifted cellCount cellLength)
      atTop (nhds target) := by
    apply global_pressure_on_cell_multiples_varyingDegrees_eventually
      degrees hdegrees base lifted cellCount cellLength cellError target
      hPressure.lifting_eventually hPressure.normalized_cell_error_zero
    exact hBaseTarget
  have hCellErrorZero : Tendsto
      (fun n => abs
        (cellNormalizedPressureVarying degrees hdegrees lifted
          cellCount cellLength n - target)) atTop (nhds 0) := by
    simpa using (hCellTarget.sub_const target).abs
  exact target_pressure_tendsto
    wholeMeanPressure
    (cellNormalizedPressureVarying degrees hdegrees lifted cellCount cellLength)
    cellLengthRatio target remainderError
    (fun n => abs
      (cellNormalizedPressureVarying degrees hdegrees lifted
        cellCount cellLength n - target))
    lengthRatioError hPressure.ratio_nonneg hPressure.ratio_le_one
    hPressure.remainder_bound (fun _ => le_rfl) hPressure.ratio_bound
    hPressure.remainder_zero hCellErrorZero hPressure.ratio_error_zero

/-- The final Section 5 certificate bounds the actual `L¹` error.  The two absolute
differences dominate the measurable long observable directly, so the intermediate
need not be assumed measurable or integrable. -/
theorem section5_long_l1_integrable_and_bound
    (mu : forall n, Measure (Omega n))
    [forall n, IsProbabilityMeasure (mu n)]
    (observable : forall n, Omega n -> Real)
    (meanPressure : Nat -> Real) (target : Real)
    (hFinal : TwoStepL1ApproximationTri mu observable meanPressure)
    (hLongMeasurable : forall n,
      AEStronglyMeasurable (observable n) (mu n)) :
    forall n,
      Integrable (observable n) (mu n) /\
        (∫ omega, abs (observable n omega - target) ∂mu n) <=
          section5LongExpectationError hFinal.seamError
            hFinal.fluctuationError meanPressure target n := by
  intro n
  let envelope : Omega n -> Real := fun omega =>
    abs (observable n omega - hFinal.intermediate n omega) +
      abs (hFinal.intermediate n omega - meanPressure n) +
        abs (meanPressure n - target)
  have hConstant : Integrable (fun _ : Omega n => abs (meanPressure n - target))
      (mu n) := integrable_const _
  have hEnvelope : Integrable envelope (mu n) :=
    ((hFinal.seamIntegrable n).add (hFinal.fluctuationIntegrable n)).add hConstant
  have hPointwise : forall omega, abs (observable n omega - target) <= envelope omega := by
    intro omega
    dsimp [envelope]
    have hFirst := abs_sub_le (observable n omega) (hFinal.intermediate n omega) target
    have hSecond := abs_sub_le (hFinal.intermediate n omega) (meanPressure n) target
    linarith
  have hDifference : Integrable (fun omega => observable n omega - target) (mu n) := by
    apply hEnvelope.mono' ((hLongMeasurable n).sub aestronglyMeasurable_const)
    filter_upwards with omega
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using hPointwise omega
  have hObservable : Integrable (observable n) (mu n) := by
    apply (hDifference.add (integrable_const target)).congr
    filter_upwards with omega
    simp
  refine ⟨hObservable, ?_⟩
  have hAbsolute : Integrable (fun omega => abs (observable n omega - target)) (mu n) := by
    simpa only [Real.norm_eq_abs] using hDifference.norm
  calc
    (∫ omega, abs (observable n omega - target) ∂mu n) <=
        ∫ omega, envelope omega ∂mu n := integral_mono hAbsolute hEnvelope hPointwise
    _ = (∫ omega, abs (observable n omega - hFinal.intermediate n omega) ∂mu n) +
        (∫ omega, abs (hFinal.intermediate n omega - meanPressure n) ∂mu n) +
          abs (meanPressure n - target) := by
      dsimp only [envelope]
      have hSumInt : Integrable (fun omega =>
          abs (observable n omega - hFinal.intermediate n omega) +
            abs (hFinal.intermediate n omega - meanPressure n)) (mu n) := by
        apply ((hFinal.seamIntegrable n).add (hFinal.fluctuationIntegrable n)).congr
        filter_upwards with omega
        rfl
      rw [integral_add hSumInt hConstant,
        integral_add (hFinal.seamIntegrable n) (hFinal.fluctuationIntegrable n)]
      simp
    _ <= section5LongExpectationError hFinal.seamError hFinal.fluctuationError
        meanPressure target n := by
      unfold section5LongExpectationError
      linarith [hFinal.seamIntegral_le n, hFinal.fluctuationIntegral_le n]

/-- Expectation-strength consequence of the actual Section 5 `L¹` bound.  This does
not infer convergence of expectations from convergence in probability. -/
theorem section5_long_expectation_integrable_and_bound
    (mu : forall n, Measure (Omega n))
    [forall n, IsProbabilityMeasure (mu n)]
    (observable : forall n, Omega n -> Real)
    (meanPressure : Nat -> Real) (target : Real)
    (hFinal : TwoStepL1ApproximationTri mu observable meanPressure)
    (hLongMeasurable : forall n,
      AEStronglyMeasurable (observable n) (mu n)) :
    forall n,
      Integrable (observable n) (mu n) /\
        abs (section5TriangularExpectation mu observable n - target) <=
          section5LongExpectationError hFinal.seamError
            hFinal.fluctuationError meanPressure target n := by
  intro n
  have hL1 := section5_long_l1_integrable_and_bound mu observable meanPressure target
    hFinal hLongMeasurable n
  have hTargetInt : Integrable (fun _ : Omega n => target) (mu n) :=
    integrable_const _
  have hNorm := abs_integral_le_integral_abs
    (μ := mu n) (f := fun omega => observable n omega - target)
  have hExpected : abs (section5TriangularExpectation mu observable n - target) <=
      ∫ omega, abs (observable n omega - target) ∂mu n := by
    simpa [section5TriangularExpectation, integral_sub hL1.1 hTargetInt] using hNorm
  exact ⟨hL1.1, hExpected.trans hL1.2⟩

/-- The explicit Section 5 long-expectation envelope is nonnegative at every index. -/
theorem section5LongExpectationError_nonneg
    (mu : forall n, Measure (Omega n))
    (observable : forall n, Omega n -> Real)
    (meanPressure : Nat -> Real)
    (hFinal : TwoStepL1ApproximationTri mu observable meanPressure)
    (target : Real) (n : Nat) :
    0 <= section5LongExpectationError hFinal.seamError
      hFinal.fluctuationError meanPressure target n := by
  have hSeam : 0 <= hFinal.seamError n :=
    (integral_nonneg (fun omega => abs_nonneg
      (observable n omega - hFinal.intermediate n omega))).trans
      (hFinal.seamIntegral_le n)
  have hFluctuation : 0 <= hFinal.fluctuationError n :=
    (integral_nonneg (fun omega => abs_nonneg
      (hFinal.intermediate n omega - meanPressure n))).trans
      (hFinal.fluctuationIntegral_le n)
  exact add_nonneg (add_nonneg hSeam hFluctuation) (abs_nonneg _)

/-- If the deterministic mean pressure has the Section 5 target limit, then the concrete
long-expectation envelope vanishes. -/
theorem section5LongExpectationError_tendsto_zero
    (mu : forall n, Measure (Omega n))
    (observable : forall n, Omega n -> Real)
    (meanPressure : Nat -> Real)
    (hFinal : TwoStepL1ApproximationTri mu observable meanPressure)
    (target : Real) (hMean : Tendsto meanPressure atTop (nhds target)) :
    Tendsto (section5LongExpectationError hFinal.seamError
      hFinal.fluctuationError meanPressure target) atTop (nhds 0) := by
  have hMeanError : Tendsto (fun n => abs (meanPressure n - target))
      atTop (nhds 0) := by
    simpa using (hMean.sub_const target).abs
  change Tendsto (fun n => hFinal.seamError n + hFinal.fluctuationError n +
    abs (meanPressure n - target)) atTop (nhds 0)
  simpa only [zero_add] using
    (hFinal.seamError_tendsto_zero.add
      hFinal.fluctuationError_tendsto_zero).add hMeanError

/-- The actual Section 5 long observable has a quantitative `L¹` approximation to
the target, not merely a convergence-in-probability conclusion. -/
theorem section5_long_l1Approximation
    (mu : forall n, Measure (Omega n))
    [forall n, IsProbabilityMeasure (mu n)]
    (observable : forall n, Omega n -> Real)
    (meanPressure : Nat -> Real) (target : Real)
    (hFinal : TwoStepL1ApproximationTri mu observable meanPressure)
    (hLongMeasurable : forall n,
      AEStronglyMeasurable (observable n) (mu n))
    (hMean : Tendsto meanPressure atTop (nhds target)) :
    L1ApproximationTri mu observable (fun _ => target)
      (section5LongExpectationError hFinal.seamError
        hFinal.fluctuationError meanPressure target) := by
  have hBound := section5_long_l1_integrable_and_bound
    mu observable meanPressure target hFinal hLongMeasurable
  refine ⟨?_, fun n => (hBound n).2, ?_⟩
  · intro n
    have h := ((hBound n).1.sub (integrable_const target)).norm
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using h
  · exact section5LongExpectationError_tendsto_zero
      mu observable meanPressure hFinal target hMean

/-- Convergence of the actual `L¹` errors exported by Section 5. -/
theorem section5_long_l1_tendsto_zero
    (mu : forall n, Measure (Omega n))
    [forall n, IsProbabilityMeasure (mu n)]
    (observable : forall n, Omega n -> Real)
    (meanPressure : Nat -> Real) (target : Real)
    (hFinal : TwoStepL1ApproximationTri mu observable meanPressure)
    (hLongMeasurable : forall n,
      AEStronglyMeasurable (observable n) (mu n))
    (hMean : Tendsto meanPressure atTop (nhds target)) :
    Tendsto (fun n => ∫ omega, abs (observable n omega - target) ∂mu n)
      atTop (nhds 0) := by
  have h := section5_long_l1Approximation
    mu observable meanPressure target hFinal hLongMeasurable hMean
  exact squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _))
    h.integral_le h.rate_tendsto_zero

/-- Direct expectation-strength output of the full Section 5 long branch. -/
theorem section5_long_expectation_tendsto
    {index : Type v}
    (mu : forall n, Measure (Omega n))
    [forall n, IsProbabilityMeasure (mu n)]
    (degrees : Nat -> Finset index)
    (hdegrees : forall n, (degrees n).Nonempty)
    (shortLogPotential calibrationLogPotential longLogPotential :
      forall n, Omega n -> Real)
    (target : Real)
    (base lifted : Nat -> index -> Real) (cellCount cellLength : Nat -> Nat)
    (cellError wholeMeanPressure cellLengthRatio : Nat -> Real)
    (remainderError lengthRatioError : Nat -> Real)
    (hSection3 : Section3IndicatorAnchorsTri mu
      shortLogPotential calibrationLogPotential target)
    (hPressure : PressureLiftToTargetInputVarying degrees hdegrees
      base lifted cellCount cellLength cellError wholeMeanPressure cellLengthRatio
      remainderError lengthRatioError)
    (hSection4 : Section4LongBranchQuantitativeInputTri mu
      calibrationLogPotential longLogPotential
      (baseNormalizedPressureVarying degrees hdegrees base cellLength)
      wholeMeanPressure)
    (hLongMeasurable : forall n,
      AEStronglyMeasurable (longLogPotential n) (mu n)) :
    Tendsto (section5TriangularExpectation mu longLogPotential)
      atTop (nhds target) := by
  have hMean := section5_wholeMeanPressure_tendsto mu degrees hdegrees
    shortLogPotential calibrationLogPotential longLogPotential target
    base lifted cellCount cellLength cellError wholeMeanPressure cellLengthRatio
    remainderError lengthRatioError hSection3 hPressure hSection4
  have hBound := section5_long_expectation_integrable_and_bound
    mu longLogPotential wholeMeanPressure target hSection4.finalClosure
    hLongMeasurable
  have hErrorZero := section5LongExpectationError_tendsto_zero
    mu longLogPotential wholeMeanPressure hSection4.finalClosure target hMean
  have hAbs : Tendsto
      (fun n => abs (section5TriangularExpectation mu longLogPotential n - target))
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun n => abs_nonneg
        (section5TriangularExpectation mu longLogPotential n - target))
      (fun n => (hBound n).2) hErrorZero
  exact tendsto_iff_dist_tendsto_zero.2 (by
    simpa [Real.dist_eq] using hAbs)

/-- Section 6 raw compact-core closure with its abstract long-branch scalar premise
replaced by Section 5's concrete pressure lift and two `L¹` certificates.

`hRawLongIdentification` is the remaining model-level boundary: only on long-branch
indices, the physical raw expectation must be identified with the integral of the
Section 5 long observable.  It is an equality of the two concrete observables, not an
assumption of the desired limit or error estimate. -/
theorem compactCore_raw_expectation_tendsto_of_section5_longBranch
    {index : Type v}
    (mu : forall n, Measure (Omega n))
    [forall n, IsProbabilityMeasure (mu n)]
    (degrees : Nat -> Finset index)
    (hdegrees : forall n, (degrees n).Nonempty)
    (directHighBand : Nat -> Prop) (rawExpectation : Nat -> Real)
    (shortLogPotential calibrationLogPotential longLogPotential :
      forall n, Omega n -> Real)
    (target : Real)
    (base lifted : Nat -> index -> Real) (cellCount cellLength : Nat -> Nat)
    (cellError wholeMeanPressure cellLengthRatio : Nat -> Real)
    (remainderError lengthRatioError : Nat -> Real)
    (section3AnchorError directCenteringError : Nat -> Real)
    (hSection3AnchorError : forall n, 0 <= section3AnchorError n)
    (hDirectCenteringError : forall n, 0 <= directCenteringError n)
    (hDirect : forall n, directHighBand n ->
      abs (rawExpectation n - target) <=
        section3AnchorError n + directCenteringError n)
    (hSection3AnchorZero : Tendsto section3AnchorError atTop (nhds 0))
    (hDirectCenteringZero : Tendsto directCenteringError atTop (nhds 0))
    (hSection3 : Section3IndicatorAnchorsTri mu
      shortLogPotential calibrationLogPotential target)
    (hPressure : PressureLiftToTargetInputVarying degrees hdegrees
      base lifted cellCount cellLength cellError wholeMeanPressure cellLengthRatio
      remainderError lengthRatioError)
    (hSection4 : Section4LongBranchQuantitativeInputTri mu
      calibrationLogPotential longLogPotential
      (baseNormalizedPressureVarying degrees hdegrees base cellLength)
      wholeMeanPressure)
    (hLongMeasurable : forall n,
      AEStronglyMeasurable (longLogPotential n) (mu n))
    (hRawLongIdentification : forall n, ¬ directHighBand n ->
      rawExpectation n = section5TriangularExpectation mu longLogPotential n) :
    Tendsto rawExpectation atTop (nhds target) := by
  have hMean := section5_wholeMeanPressure_tendsto mu degrees hdegrees
    shortLogPotential calibrationLogPotential longLogPotential target
    base lifted cellCount cellLength cellError wholeMeanPressure cellLengthRatio
    remainderError lengthRatioError hSection3 hPressure hSection4
  have hExpectationBound := section5_long_expectation_integrable_and_bound
    mu longLogPotential wholeMeanPressure target hSection4.finalClosure
    hLongMeasurable
  apply compactCore_raw_expectation_tendsto directHighBand rawExpectation target
    section3AnchorError directCenteringError
    (section5LongExpectationError hSection4.finalClosure.seamError
      hSection4.finalClosure.fluctuationError wholeMeanPressure target)
  · exact hSection3AnchorError
  · exact hDirectCenteringError
  · intro n
    exact section5LongExpectationError_nonneg mu longLogPotential wholeMeanPressure
      hSection4.finalClosure target n
  · exact hDirect
  · intro n hn
    rw [hRawLongIdentification n hn]
    exact (hExpectationBound n).2
  · exact hSection3AnchorZero
  · exact hDirectCenteringZero
  · exact section5LongExpectationError_tendsto_zero
      mu longLogPotential wholeMeanPressure hSection4.finalClosure target hMean

/-- Fixed-scale compact-core raw closure.  The shift may be `log r` in the physical
identity for `r A - z I`; Section 5 is then applied at the spectral parameter `z / r`.
The long error is constructed from the Section 5 certificate, not supplied anew. -/
theorem compactCore_raw_expectation_tendsto_of_section5_finalClosure
    (mu : forall n, Measure (Omega n))
    [forall n, IsProbabilityMeasure (mu n)]
    (observable : forall n, Omega n -> Real)
    (meanPressure : Nat -> Real) (target shift : Real)
    (hFinal : TwoStepL1ApproximationTri mu observable meanPressure)
    (hLongMeasurable : forall n,
      AEStronglyMeasurable (observable n) (mu n))
    (hMean : Tendsto meanPressure atTop (nhds target))
    (directHighBand : Nat -> Prop) (rawExpectation : Nat -> Real)
    (section3AnchorError directCenteringError : Nat -> Real)
    (hSection3AnchorError : forall n, 0 <= section3AnchorError n)
    (hDirectCenteringError : forall n, 0 <= directCenteringError n)
    (hDirect : forall n, directHighBand n ->
      abs (rawExpectation n - (shift + target)) <=
        section3AnchorError n + directCenteringError n)
    (hSection3AnchorZero : Tendsto section3AnchorError atTop (nhds 0))
    (hDirectCenteringZero : Tendsto directCenteringError atTop (nhds 0))
    (hRawLongIdentification : forall n, ¬ directHighBand n ->
      rawExpectation n = shift + section5TriangularExpectation mu observable n) :
    Tendsto rawExpectation atTop (nhds (shift + target)) := by
  have hBound := section5_long_expectation_integrable_and_bound
    mu observable meanPressure target hFinal hLongMeasurable
  apply compactCore_raw_expectation_tendsto directHighBand rawExpectation (shift + target)
    section3AnchorError directCenteringError
    (section5LongExpectationError hFinal.seamError hFinal.fluctuationError
      meanPressure target)
    hSection3AnchorError hDirectCenteringError
    (section5LongExpectationError_nonneg mu observable meanPressure hFinal target)
    hDirect
  · intro n hn
    rw [hRawLongIdentification n hn]
    simpa only [add_sub_add_left_eq_sub] using (hBound n).2
  · exact hSection3AnchorZero
  · exact hDirectCenteringZero
  · exact section5LongExpectationError_tendsto_zero
      mu observable meanPressure hFinal target hMean

/-- Raw and fixed-cutoff compact-core conclusions with the long raw branch supplied
by Section 5.  The direct raw anchor/centering and the separate cutoff
comparison/periodicization estimates remain explicit inputs. -/
theorem compact_gaussian_core_of_section5_finalClosure
    (mu : forall n, Measure (Omega n))
    [forall n, IsProbabilityMeasure (mu n)]
    (observable : forall n, Omega n -> Real)
    (meanPressure : Nat -> Real) (target shift cutoffTarget : Real)
    (hFinal : TwoStepL1ApproximationTri mu observable meanPressure)
    (hLongMeasurable : forall n,
      AEStronglyMeasurable (observable n) (mu n))
    (hMean : Tendsto meanPressure atTop (nhds target))
    (directHighBand : Nat -> Prop)
    (rawExpectation cutoffExpectation : Nat -> Real)
    (section3AnchorError directCenteringError : Nat -> Real)
    (directComparisonError longPeriodicizationError : Nat -> Real)
    (hSection3AnchorError : forall n, 0 <= section3AnchorError n)
    (hDirectCenteringError : forall n, 0 <= directCenteringError n)
    (hDirectComparisonError : forall n, 0 <= directComparisonError n)
    (hLongPeriodicizationError : forall n, 0 <= longPeriodicizationError n)
    (hRawDirect : forall n, directHighBand n ->
      abs (rawExpectation n - (shift + target)) <=
        section3AnchorError n + directCenteringError n)
    (hRawLongIdentification : forall n, ¬ directHighBand n ->
      rawExpectation n = shift + section5TriangularExpectation mu observable n)
    (hCutoffDirect : forall n, directHighBand n ->
      abs (cutoffExpectation n - cutoffTarget) <= directComparisonError n)
    (hCutoffLong : forall n, ¬ directHighBand n ->
      abs (cutoffExpectation n - cutoffTarget) <= longPeriodicizationError n)
    (hSection3AnchorZero : Tendsto section3AnchorError atTop (nhds 0))
    (hDirectCenteringZero : Tendsto directCenteringError atTop (nhds 0))
    (hDirectComparisonZero : Tendsto directComparisonError atTop (nhds 0))
    (hLongPeriodicizationZero : Tendsto longPeriodicizationError atTop (nhds 0)) :
    Tendsto rawExpectation atTop (nhds (shift + target)) ∧
      Tendsto cutoffExpectation atTop (nhds cutoffTarget) := by
  constructor
  · exact compactCore_raw_expectation_tendsto_of_section5_finalClosure
      mu observable meanPressure target shift hFinal hLongMeasurable hMean
      directHighBand rawExpectation section3AnchorError directCenteringError
      hSection3AnchorError hDirectCenteringError hRawDirect hSection3AnchorZero
      hDirectCenteringZero hRawLongIdentification
  · exact compactCore_cutoff_expectation_tendsto directHighBand cutoffExpectation
      cutoffTarget directComparisonError longPeriodicizationError
      hDirectComparisonError hLongPeriodicizationError hCutoffDirect hCutoffLong
      hDirectComparisonZero hLongPeriodicizationZero

end CircularLawSections56.Section6
