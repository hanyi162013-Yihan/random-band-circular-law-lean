import CircularLawSections56.Section5.IndicatorClosure
import CircularLawSections56.Section5.PressureAsymptotics
import CircularLawSections56.Section5.TargetPressure
import CircularLawSections56.Section5.TriangularProbability

/-!
# Near-end-to-end assembly of Section 5

This file joins the proved deterministic Section 5 spine once explicit adapters supply
the quantitative endpoints associated with Sections 3 and 4.  It intentionally uses a
triangular-array probability space, which can represent the literal finite matrix models
after their auxiliary and target rings are transported to a common per-index law.

The Section 4 boundary is quantitative rather than an opaque proposition: it records
integrability, the actual `L¹` inequalities, and the vanishing rates.  The literal
adapters collected by the Section 5 umbrella now invoke the periodic determinant/
fresh-closure and maximal-pressure concentration families, notably

* `complex_paperIndicatorFlatFreshZ_joint_absLog_condExp_withDensity` (or the real
  analogue), and
* `integral_max_complex_paperIndicatorFlatOpenPressure_le_auto` (or the real analogue).

The companion adapter files prove the arbitrary-start cleared-trace-to-FreshZ identity, exact
fresh/nonfresh product-law transport, random/mean maximum identification and literal
maximal concentration, two-sided iid FreshZ cell bounds and their telescope,
normalization, and inactive-branch completion.  They also identify the start-zero outside
family with the suffix open-pressure observable and prove a genuine iid matrix-product
expected-log telescope.  The norm-attaining adapted direction and its lower-algebra
certificate are constructed automatically, and the start-zero outside positivity and
flat-pressure identity are available almost everywhere under the bounded-density input.
The complex and real full-law matrix-cell packages, almost-sure cell invertibility,
all-length product integrability, and the literal finite-cell telescopes are instantiated.
The paper-centered random-outside telescope retains the base pressure separately from
the error, and the concrete mesoscopic scale limits are proved in companion modules.
This assembly module deliberately stays phrased through receiver structures; the lower-level
literal assembly module constructs those receivers from finite model estimates and explicit
physical identifications rather than treating a long-branch limit as a premise.
The one-row inverse-cost estimate likewise remains upstream of the remainder fields below;
the scalar remainder transport itself is proved in this project.
-/

open Filter MeasureTheory Topology

namespace CircularLawSections56.Section5

universe u v

variable {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]

/-- A quantitative `L¹` approximation on varying probability spaces.  This is a receiver
shape for an adapter after all matrix identifications and length normalizations have been
proved. -/
structure L1ApproximationTri
    (μ : ∀ n, Measure (Ω n)) (observable : ∀ n, Ω n → ℝ)
    (center rate : ℕ → ℝ) : Prop where
  integrable : ∀ n,
    Integrable (fun ω => |observable n ω - center n|) (μ n)
  integral_le : ∀ n,
    ∫ ω, |observable n ω - center n| ∂μ n ≤ rate n
  rate_tendsto_zero : Tendsto rate atTop (𝓝 0)

/-- A two-step `L¹` comparison through a random intermediate observable.  This is the
target receiver shape of the Section 4 adapter: fresh closure is intended to control
`observable - intermediate`, while pressure concentration is intended to control
`intermediate - center`. -/
structure TwoStepL1ApproximationTri
    (μ : ∀ n, Measure (Ω n)) (observable : ∀ n, Ω n → ℝ)
    (center : ℕ → ℝ) where
  intermediate : ∀ n, Ω n → ℝ
  seamError : ℕ → ℝ
  fluctuationError : ℕ → ℝ
  seamIntegrable : ∀ n,
    Integrable (fun ω => |observable n ω - intermediate n ω|) (μ n)
  seamIntegral_le : ∀ n,
    ∫ ω, |observable n ω - intermediate n ω| ∂μ n ≤ seamError n
  fluctuationIntegrable : ∀ n,
    Integrable (fun ω => |intermediate n ω - center n|) (μ n)
  fluctuationIntegral_le : ∀ n,
    ∫ ω, |intermediate n ω - center n| ∂μ n ≤ fluctuationError n
  seamError_tendsto_zero : Tendsto seamError atTop (𝓝 0)
  fluctuationError_tendsto_zero : Tendsto fluctuationError atTop (𝓝 0)

/-- The two uses of the known Section 3 result in the indicator proof: once at the
target size for the short branch and once on auxiliary mesoscopic rings for calibration.
They are explicit ordinary inputs because the local Section 3 project exposes this
endpoint but does not prove it internally. -/
structure Section3IndicatorAnchorsTri
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (shortLogPotential calibrationLogPotential : ∀ n, Ω n → ℝ)
    (target : ℝ) : Prop where
  target_size : TendstoInProbabilityTri μ shortLogPotential target
  mesoscopic : TendstoInProbabilityTri μ calibrationLogPotential target

/-- The normalized high-level contract expected from the Section 4-to-Section 5 adapter.

`calibration` receives the auxiliary periodic determinant seam and maximal-pressure
fluctuation after their sample-space transport and normalization.  `finalClosure`
receives the corresponding two estimates at the target length.  Each field exposes its
rate and integral inequality through `TwoStepL1ApproximationTri`; no random-matrix
conclusion or missing adapter is hidden as an axiom. -/
structure Section4LongBranchQuantitativeInputTri
    (μ : ∀ n, Measure (Ω n))
    (calibrationLogPotential longLogPotential : ∀ n, Ω n → ℝ)
    (baseMeanPressure wholeMeanPressure : ℕ → ℝ) where
  calibration : TwoStepL1ApproximationTri μ calibrationLogPotential
    baseMeanPressure
  finalClosure : TwoStepL1ApproximationTri μ longLogPotential
    wholeMeanPressure

variable {ι : Type v}

/-- Normalized maximal pressure on one mesoscopic cell. -/
noncomputable def baseNormalizedPressureVarying
    (degrees : ℕ → Finset ι) (hdegrees : ∀ n, (degrees n).Nonempty)
    (base : ℕ → ι → ℝ) (m : ℕ → ℕ) (n : ℕ) : ℝ :=
  finiteSignedMax (degrees n) (hdegrees n) (base n) / (m n : ℝ)

/-- Normalized maximal pressure on the complete-cell multiple `qₙ mₙ`. -/
noncomputable def cellNormalizedPressureVarying
    (degrees : ℕ → Finset ι) (hdegrees : ∀ n, (degrees n).Nonempty)
    (lifted : ℕ → ι → ℝ) (q m : ℕ → ℕ) (n : ℕ) : ℝ :=
  finiteSignedMax (degrees n) (hdegrees n) (lifted n) /
    ((q n : ℝ) * (m n : ℝ))

/-- The receiver interface for the proved pressure-lifting and target-remainder spine.

The complex literal cell telescope now supplies the finite-cell estimate behind
`lifting_eventually`; converting its explicit error and expected open pressure into the
manuscript's varying asymptotic pressure statement remains an application-level step.
Balanced division, the one-row forward/inverse cost, and the scalar lemmas
in `InverseAndRemainder.lean` feed `remainder_bound`; scale arithmetic supplies the three
vanishing fields. -/
structure PressureLiftToTargetInputVarying
    (degrees : ℕ → Finset ι) (hdegrees : ∀ n, (degrees n).Nonempty)
    (base lifted : ℕ → ι → ℝ) (q m : ℕ → ℕ) (cellError : ℕ → ℝ)
    (wholeNormalizedPressure cellLengthRatio : ℕ → ℝ)
    (remainderError lengthRatioError : ℕ → ℝ) : Prop where
  lifting_eventually : ∀ᶠ n in atTop,
    0 < q n ∧ 0 < m n ∧ ∀ r, r ∈ degrees n →
      (q n : ℝ) * (base n r - cellError n) ≤ lifted n r ∧
        lifted n r ≤ (q n : ℝ) * (base n r + cellError n)
  normalized_cell_error_zero :
    Tendsto (fun n => cellError n / (m n : ℝ)) atTop (𝓝 0)
  ratio_nonneg : ∀ n, 0 ≤ cellLengthRatio n
  ratio_le_one : ∀ n, cellLengthRatio n ≤ 1
  remainder_bound : ∀ n,
    |wholeNormalizedPressure n -
      cellLengthRatio n *
        cellNormalizedPressureVarying degrees hdegrees lifted q m n| ≤
      remainderError n
  remainder_zero : Tendsto remainderError atTop (𝓝 0)
  ratio_bound : ∀ n, |cellLengthRatio n - 1| ≤ lengthRatioError n
  ratio_error_zero : Tendsto lengthRatioError atTop (𝓝 0)

/-- Fixed-spectral-parameter near-end-to-end logarithmic-potential theorem for the
indicator profile.

The proof invokes, in order, the Section 3 calibration anchor, the supplied normalized
two-step calibration certificate, the varying-degree pressure lift, the target remainder
closure, the supplied normalized final certificate, and branch selection.

The short and long observables and all quantitative data are full sequences.  A literal
application must canonically fill inactive branch indices (normally with the target and
zero errors) before constructing the input structures.  In contrast, pressure lifting is
required only eventually, so floor-based cell counts need no positivity filler on a finite
prefix. -/
theorem indicator_logPotential_nearEndToEnd_tri
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (degrees : ℕ → Finset ι) (hdegrees : ∀ n, (degrees n).Nonempty)
    (shortBranch : ℕ → Bool)
    (shortLogPotential calibrationLogPotential longLogPotential :
      ∀ n, Ω n → ℝ)
    (target : ℝ)
    (base lifted : ℕ → ι → ℝ) (q m : ℕ → ℕ) (cellError : ℕ → ℝ)
    (wholeNormalizedPressure cellLengthRatio : ℕ → ℝ)
    (remainderError lengthRatioError : ℕ → ℝ)
    (hSection3 : Section3IndicatorAnchorsTri μ
      shortLogPotential calibrationLogPotential target)
    (hPressure : PressureLiftToTargetInputVarying degrees hdegrees
      base lifted q m cellError wholeNormalizedPressure cellLengthRatio
      remainderError lengthRatioError)
    (hSection4 : Section4LongBranchQuantitativeInputTri μ
      calibrationLogPotential longLogPotential
      (baseNormalizedPressureVarying degrees hdegrees base m)
      wholeNormalizedPressure) :
    TendstoInProbabilityTri μ
      (branchSelectedTri shortBranch shortLogPotential longLogPotential) target := by
  have hBaseTarget : Tendsto
      (baseNormalizedPressureVarying degrees hdegrees base m)
      atTop (𝓝 target) := by
    exact deterministic_center_tendsto_of_tri_anchor_and_two_L1_seams
      μ calibrationLogPotential hSection4.calibration.intermediate
      (baseNormalizedPressureVarying degrees hdegrees base m)
      hSection4.calibration.seamError
      hSection4.calibration.fluctuationError target hSection3.mesoscopic
      hSection4.calibration.seamIntegrable
      hSection4.calibration.seamIntegral_le
      hSection4.calibration.fluctuationIntegrable
      hSection4.calibration.fluctuationIntegral_le
      hSection4.calibration.seamError_tendsto_zero
      hSection4.calibration.fluctuationError_tendsto_zero
  have hCellTarget : Tendsto
      (cellNormalizedPressureVarying degrees hdegrees lifted q m)
      atTop (𝓝 target) := by
    change Tendsto
      (fun n => finiteSignedMax (degrees n) (hdegrees n) (lifted n) /
        ((q n : ℝ) * (m n : ℝ))) atTop (𝓝 target)
    apply global_pressure_on_cell_multiples_varyingDegrees_eventually
      degrees hdegrees base lifted q m cellError target
      hPressure.lifting_eventually
      hPressure.normalized_cell_error_zero
    change Tendsto
      (baseNormalizedPressureVarying degrees hdegrees base m)
      atTop (𝓝 target)
    exact hBaseTarget
  have hCellErrorZero : Tendsto
      (fun n =>
        |cellNormalizedPressureVarying degrees hdegrees lifted q m n - target|)
      atTop (𝓝 0) := by
    have hSub : Tendsto
        (fun n =>
          cellNormalizedPressureVarying degrees hdegrees lifted q m n - target)
        atTop (𝓝 0) := by
      simpa using hCellTarget.sub_const target
    simpa using hSub.abs
  have hWholeTarget : Tendsto wholeNormalizedPressure atTop (𝓝 target) := by
    apply target_pressure_tendsto
      wholeNormalizedPressure
      (cellNormalizedPressureVarying degrees hdegrees lifted q m)
      cellLengthRatio target remainderError
      (fun n =>
        |cellNormalizedPressureVarying degrees hdegrees lifted q m n - target|)
      lengthRatioError
    · exact hPressure.ratio_nonneg
    · exact hPressure.ratio_le_one
    · exact hPressure.remainder_bound
    · intro n
      exact le_rfl
    · exact hPressure.ratio_bound
    · exact hPressure.remainder_zero
    · exact hCellErrorZero
    · exact hPressure.ratio_error_zero
  have hLong : TendstoInProbabilityTri μ longLogPotential target := by
    exact longBranch_tendstoInProbabilityTri_of_L1_seams
      μ longLogPotential hSection4.finalClosure.intermediate
      wholeNormalizedPressure hSection4.finalClosure.seamError
      hSection4.finalClosure.fluctuationError target
      hSection4.finalClosure.seamIntegrable
      hSection4.finalClosure.seamIntegral_le
      hSection4.finalClosure.fluctuationIntegrable
      hSection4.finalClosure.fluctuationIntegral_le
      hSection4.finalClosure.seamError_tendsto_zero
      hSection4.finalClosure.fluctuationError_tendsto_zero hWholeTarget
  exact tendstoInProbabilityTri_branchSelected μ shortBranch
    shortLogPotential longLogPotential target hSection3.target_size hLong

/-- Circular-law wrapper for `indicator_logPotential_nearEndToEnd_tri`.

This is a fixed-spectral-parameter application wrapper, not the a.e.-`z` replacement
theorem itself.  The replacement principle remains an explicit theorem parameter, while
an explicitly assumed normalized Hilbert--Schmidt identity is converted internally to
the required scalar uniform bound.  `hActual` ensures that replacement is applied to the
physical observable, not merely to the two auxiliary branch-filled sequences. -/
theorem indicator_circularLaw_nearEndToEnd_tri_of_replacement
    {CircularLawConclusion : Prop}
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (degrees : ℕ → Finset ι) (hdegrees : ∀ n, (degrees n).Nonempty)
    (shortBranch : ℕ → Bool)
    (shortLogPotential calibrationLogPotential longLogPotential actualLogPotential :
      ∀ n, Ω n → ℝ)
    (target : ℝ)
    (base lifted : ℕ → ι → ℝ) (q m : ℕ → ℕ) (cellError : ℕ → ℝ)
    (wholeNormalizedPressure cellLengthRatio : ℕ → ℝ)
    (remainderError lengthRatioError normalizedExpectedHSSquare : ℕ → ℝ)
    (hSection3 : Section3IndicatorAnchorsTri μ
      shortLogPotential calibrationLogPotential target)
    (hPressure : PressureLiftToTargetInputVarying degrees hdegrees
      base lifted q m cellError wholeNormalizedPressure cellLengthRatio
      remainderError lengthRatioError)
    (hSection4 : Section4LongBranchQuantitativeInputTri μ
      calibrationLogPotential longLogPotential
      (baseNormalizedPressureVarying degrees hdegrees base m)
      wholeNormalizedPressure)
    (hActual : ∀ n ω, actualLogPotential n ω =
      branchSelectedTri shortBranch shortLogPotential longLogPotential n ω)
    (hHSIdentity : ∀ n, normalizedExpectedHSSquare n = 1)
    (hReplacement :
      TendstoInProbabilityTri μ actualLogPotential target →
        (∃ C : ℝ, 0 ≤ C ∧ ∀ n, normalizedExpectedHSSquare n ≤ C) →
        CircularLawConclusion) :
    CircularLawConclusion := by
  have hSelected := indicator_logPotential_nearEndToEnd_tri
    μ degrees hdegrees shortBranch shortLogPotential calibrationLogPotential
    longLogPotential target base lifted q m cellError wholeNormalizedPressure
    cellLengthRatio remainderError lengthRatioError hSection3 hPressure hSection4
  have hActualProbability :
      TendstoInProbabilityTri μ actualLogPotential target := by
    apply hSelected.congr
    · intro n ω
      exact (hActual n ω).symm
    · rfl
  exact hReplacement hActualProbability
    (uniform_hs_square_bound_of_eq_one normalizedExpectedHSSquare hHSIdentity)

end CircularLawSections56.Section5
