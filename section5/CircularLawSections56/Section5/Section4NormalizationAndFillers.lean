import CircularLawSections56.Section5.NearEndToEnd

/-!
# Section 4 normalization and inactive-branch fillers

This file supplies two deterministic adapters needed between the existing Section 4
estimates and `TwoStepL1ApproximationTri`.

First, raw two-step `L¹` bounds are divided by a positive deterministic scale.  Second,
an arbitrary Boolean active branch is completed canonically: at inactive indices both
random observables are replaced by the deterministic center and both error rates are set
to zero.  Consequently the resulting certificate asks for analytic estimates only when
the branch is active.

These lemmas do **not** identify any literal Section 4 expression with the raw observable,
intermediate pressure, or deterministic center used below.  In particular, determinant/
cleared-trace identities, product-space transport, equality with the random finite maximum,
equality with its mean, and the manuscript's concrete length scale remain explicit caller
obligations.  The results here only transport already-established scalar integral bounds.
-/

open Filter MeasureTheory Topology

namespace CircularLawSections56.Section5

universe u

variable {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]

/-- Divide every member of a triangular random observable by its deterministic scale. -/
noncomputable def normalizedTriObservable (scale : ℕ → ℝ)
    (observable : ∀ n, Ω n → ℝ) :
    ∀ n, Ω n → ℝ :=
  fun n ω => observable n ω / scale n

/-- Divide a deterministic center sequence by the same scale as its observables. -/
noncomputable def normalizedTriCenter (scale center : ℕ → ℝ) : ℕ → ℝ :=
  fun n => center n / scale n

/-- At an inactive Boolean index, replace a random observable by the exact center. -/
def inactiveFilledTriObservable (active : ℕ → Bool)
    (observable : ∀ n, Ω n → ℝ) (center : ℕ → ℝ) : ∀ n, Ω n → ℝ :=
  fun n ω => if active n then observable n ω else center n

/-- At an inactive Boolean index, replace an error rate by zero. -/
def inactiveFilledTriRate (active : ℕ → Bool) (rate : ℕ → ℝ) : ℕ → ℝ :=
  fun n => if active n then rate n else 0

/-- Fill an ordinary sequence by a canonical value whenever its Boolean branch is
inactive.  This generic form is used for scalar pressures, natural cell counts, ratios,
and finite degree families below. -/
def inactiveFilledTriValue {α : Type*} (active : ℕ → Bool)
    (value filler : ℕ → α) : ℕ → α :=
  fun n => if active n then value n else filler n

/-- Dividing two real observables by the same positive scalar preserves integrability of
their absolute difference. -/
theorem integrable_abs_div_sub_div
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (X Y : α → ℝ) (scale : ℝ) (hScale : 0 < scale)
    (hIntegrable : Integrable (fun ω => |X ω - Y ω|) μ) :
    Integrable (fun ω => |X ω / scale - Y ω / scale|) μ := by
  have hScaled := hIntegrable.const_mul (scale⁻¹)
  convert hScaled using 1
  funext ω
  rw [← sub_div, abs_div, abs_of_pos hScale, div_eq_mul_inv, mul_comm]

/-- A raw absolute-difference integral bound scales by exactly the reciprocal positive
normalization. -/
theorem integral_abs_div_sub_div_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (X Y : α → ℝ) (scale error : ℝ) (hScale : 0 < scale)
    (hIntegral : (∫ ω, |X ω - Y ω| ∂μ) ≤ error) :
    (∫ ω, |X ω / scale - Y ω / scale| ∂μ) ≤ error / scale := by
  have hInvNonneg : 0 ≤ scale⁻¹ := inv_nonneg.mpr hScale.le
  calc
    (∫ ω, |X ω / scale - Y ω / scale| ∂μ) =
        scale⁻¹ * ∫ ω, |X ω - Y ω| ∂μ := by
      have hFunction :
          (fun ω => |X ω / scale - Y ω / scale|) =
            fun ω => scale⁻¹ * |X ω - Y ω| := by
        funext ω
        rw [← sub_div, abs_div, abs_of_pos hScale, div_eq_mul_inv, mul_comm]
      rw [hFunction, integral_const_mul]
    _ ≤ scale⁻¹ * error := mul_le_mul_of_nonneg_left hIntegral hInvNonneg
    _ = error / scale := by rw [div_eq_mul_inv, mul_comm]

/-- Raw two-step `L¹` bounds divided by a positive scale give the normalized receiver
certificate used by `NearEndToEnd.lean`.

The hypotheses deliberately start after literal matrix identification and measure
transport: `rawObservable`, `rawIntermediate`, and `rawCenter` must already denote the
three scalar quantities on the common triangular probability space. -/
noncomputable def twoStepL1ApproximationTri_of_raw_div_scale
    (μ : ∀ n, Measure (Ω n))
    (rawObservable rawIntermediate : ∀ n, Ω n → ℝ)
    (rawCenter scale rawSeamError rawFluctuationError : ℕ → ℝ)
    (hScale : ∀ n, 0 < scale n)
    (hSeamIntegrable : ∀ n,
      Integrable (fun ω => |rawObservable n ω - rawIntermediate n ω|) (μ n))
    (hSeamIntegral : ∀ n,
      ∫ ω, |rawObservable n ω - rawIntermediate n ω| ∂μ n ≤ rawSeamError n)
    (hFluctuationIntegrable : ∀ n,
      Integrable (fun ω => |rawIntermediate n ω - rawCenter n|) (μ n))
    (hFluctuationIntegral : ∀ n,
      ∫ ω, |rawIntermediate n ω - rawCenter n| ∂μ n ≤ rawFluctuationError n)
    (hSeamErrorZero : Tendsto (fun n => rawSeamError n / scale n) atTop (𝓝 0))
    (hFluctuationErrorZero :
      Tendsto (fun n => rawFluctuationError n / scale n) atTop (𝓝 0)) :
    TwoStepL1ApproximationTri μ
      (normalizedTriObservable scale rawObservable)
      (normalizedTriCenter scale rawCenter) := by
  refine
    { intermediate := normalizedTriObservable scale rawIntermediate
      seamError := fun n => rawSeamError n / scale n
      fluctuationError := fun n => rawFluctuationError n / scale n
      seamIntegrable := ?_
      seamIntegral_le := ?_
      fluctuationIntegrable := ?_
      fluctuationIntegral_le := ?_
      seamError_tendsto_zero := hSeamErrorZero
      fluctuationError_tendsto_zero := hFluctuationErrorZero }
  · intro n
    exact integrable_abs_div_sub_div (μ n) (rawObservable n) (rawIntermediate n)
      (scale n) (hScale n) (hSeamIntegrable n)
  · intro n
    exact integral_abs_div_sub_div_le (μ n) (rawObservable n) (rawIntermediate n)
      (scale n) (rawSeamError n) (hScale n) (hSeamIntegral n)
  · intro n
    exact integrable_abs_div_sub_div (μ n) (rawIntermediate n)
      (fun _ => rawCenter n) (scale n) (hScale n) (hFluctuationIntegrable n)
  · intro n
    exact integral_abs_div_sub_div_le (μ n) (rawIntermediate n)
      (fun _ => rawCenter n) (scale n) (rawFluctuationError n)
      (hScale n) (hFluctuationIntegral n)

/-- A rate which becomes small whenever its Boolean branch is active has a zero-filled
extension tending to zero along the full sequence. -/
theorem inactiveFilledTriRate_tendsto_zero
    (active : ℕ → Bool) (rate : ℕ → ℝ)
    (hActiveZero : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, active n = true → |rate n| < ε) :
    Tendsto (inactiveFilledTriRate active rate) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hActiveZero ε hε)
  refine ⟨N, fun n hnN => ?_⟩
  cases h : active n with
  | false => simp [inactiveFilledTriRate, h, hε]
  | true =>
      have hn := hN n hnN h
      simpa [inactiveFilledTriRate, h, Real.dist_eq] using hn

/-- Canonical inactive completion of a one-step `L¹` certificate.

Only active indices require integrability and an integral estimate.  The inactive
observable is definitionally the center, so its absolute error and rate are both zero. -/
theorem l1ApproximationTri_inactiveFill
    (μ : ∀ n, Measure (Ω n)) (active : ℕ → Bool)
    (observable : ∀ n, Ω n → ℝ) (center rate : ℕ → ℝ)
    (hIntegrable : ∀ n, active n = true →
      Integrable (fun ω => |observable n ω - center n|) (μ n))
    (hIntegral : ∀ n, active n = true →
      ∫ ω, |observable n ω - center n| ∂μ n ≤ rate n)
    (hRateZero : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, active n = true → |rate n| < ε) :
    L1ApproximationTri μ
      (inactiveFilledTriObservable active observable center) center
      (inactiveFilledTriRate active rate) := by
  refine
    { integrable := ?_
      integral_le := ?_
      rate_tendsto_zero := inactiveFilledTriRate_tendsto_zero active rate hRateZero }
  · intro n
    cases h : active n with
    | false => simp [inactiveFilledTriObservable, h]
    | true =>
        simpa [inactiveFilledTriObservable, h] using hIntegrable n h
  · intro n
    cases h : active n with
    | false => simp [inactiveFilledTriObservable, inactiveFilledTriRate, h]
    | true =>
        simpa [inactiveFilledTriObservable, inactiveFilledTriRate, h] using hIntegral n h

/-- Canonical inactive completion of a two-step `L¹` certificate.

At inactive indices the observable and intermediate are both filled by `center`; hence no
Section 4 seam, concentration, measurability, or integrability estimate is requested there.
At active indices the supplied quantities are preserved exactly. -/
noncomputable def twoStepL1ApproximationTri_inactiveFill
    (μ : ∀ n, Measure (Ω n)) (active : ℕ → Bool)
    (observable intermediate : ∀ n, Ω n → ℝ)
    (center seamError fluctuationError : ℕ → ℝ)
    (hSeamIntegrable : ∀ n, active n = true →
      Integrable (fun ω => |observable n ω - intermediate n ω|) (μ n))
    (hSeamIntegral : ∀ n, active n = true →
      ∫ ω, |observable n ω - intermediate n ω| ∂μ n ≤ seamError n)
    (hFluctuationIntegrable : ∀ n, active n = true →
      Integrable (fun ω => |intermediate n ω - center n|) (μ n))
    (hFluctuationIntegral : ∀ n, active n = true →
      ∫ ω, |intermediate n ω - center n| ∂μ n ≤ fluctuationError n)
    (hSeamErrorZero : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, active n = true → |seamError n| < ε)
    (hFluctuationErrorZero : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, active n = true → |fluctuationError n| < ε) :
    TwoStepL1ApproximationTri μ
      (inactiveFilledTriObservable active observable center) center := by
  refine
    { intermediate := inactiveFilledTriObservable active intermediate center
      seamError := inactiveFilledTriRate active seamError
      fluctuationError := inactiveFilledTriRate active fluctuationError
      seamIntegrable := ?_
      seamIntegral_le := ?_
      fluctuationIntegrable := ?_
      fluctuationIntegral_le := ?_
      seamError_tendsto_zero :=
        inactiveFilledTriRate_tendsto_zero active seamError hSeamErrorZero
      fluctuationError_tendsto_zero :=
        inactiveFilledTriRate_tendsto_zero active fluctuationError hFluctuationErrorZero }
  · intro n
    cases h : active n with
    | false => simp [inactiveFilledTriObservable, h]
    | true =>
        simpa [inactiveFilledTriObservable, h] using hSeamIntegrable n h
  · intro n
    cases h : active n with
    | false => simp [inactiveFilledTriObservable, inactiveFilledTriRate, h]
    | true =>
        simpa [inactiveFilledTriObservable, inactiveFilledTriRate, h] using hSeamIntegral n h
  · intro n
    cases h : active n with
    | false => simp [inactiveFilledTriObservable, h]
    | true =>
        simpa [inactiveFilledTriObservable, h] using hFluctuationIntegrable n h
  · intro n
    cases h : active n with
    | false => simp [inactiveFilledTriObservable, inactiveFilledTriRate, h]
    | true =>
        simpa [inactiveFilledTriObservable, inactiveFilledTriRate, h] using
          hFluctuationIntegral n h

/-- Combined Section 4 adapter: normalize raw bounds only on active indices, and fill every
inactive index canonically.

Positivity of `scale` and all raw Section 4 estimates are required only under
`active n = true`.  The two final hypotheses are precisely the normalized active-branch
rate estimates; they impose no condition on inactive raw errors or scales.  Literal
determinant, pressure, expectation, and sample-space identifications remain premises of
the raw bounds and are not proved here. -/
noncomputable def twoStepL1ApproximationTri_of_raw_div_scale_inactiveFill
    (μ : ∀ n, Measure (Ω n)) (active : ℕ → Bool)
    (rawObservable rawIntermediate : ∀ n, Ω n → ℝ)
    (rawCenter scale rawSeamError rawFluctuationError : ℕ → ℝ)
    (hScale : ∀ n, active n = true → 0 < scale n)
    (hSeamIntegrable : ∀ n, active n = true →
      Integrable (fun ω => |rawObservable n ω - rawIntermediate n ω|) (μ n))
    (hSeamIntegral : ∀ n, active n = true →
      ∫ ω, |rawObservable n ω - rawIntermediate n ω| ∂μ n ≤ rawSeamError n)
    (hFluctuationIntegrable : ∀ n, active n = true →
      Integrable (fun ω => |rawIntermediate n ω - rawCenter n|) (μ n))
    (hFluctuationIntegral : ∀ n, active n = true →
      ∫ ω, |rawIntermediate n ω - rawCenter n| ∂μ n ≤ rawFluctuationError n)
    (hSeamErrorZero : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, active n = true → |rawSeamError n / scale n| < ε)
    (hFluctuationErrorZero : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, active n = true → |rawFluctuationError n / scale n| < ε) :
    TwoStepL1ApproximationTri μ
      (inactiveFilledTriObservable active
        (normalizedTriObservable scale rawObservable)
        (normalizedTriCenter scale rawCenter))
      (normalizedTriCenter scale rawCenter) := by
  apply twoStepL1ApproximationTri_inactiveFill μ active
    (normalizedTriObservable scale rawObservable)
    (normalizedTriObservable scale rawIntermediate)
    (normalizedTriCenter scale rawCenter)
    (fun n => rawSeamError n / scale n)
    (fun n => rawFluctuationError n / scale n)
  · intro n hn
    exact integrable_abs_div_sub_div (μ n) (rawObservable n) (rawIntermediate n)
      (scale n) (hScale n hn) (hSeamIntegrable n hn)
  · intro n hn
    exact integral_abs_div_sub_div_le (μ n) (rawObservable n) (rawIntermediate n)
      (scale n) (rawSeamError n) (hScale n hn) (hSeamIntegral n hn)
  · intro n hn
    exact integrable_abs_div_sub_div (μ n) (rawIntermediate n)
      (fun _ => rawCenter n) (scale n) (hScale n hn)
      (hFluctuationIntegrable n hn)
  · intro n hn
    exact integral_abs_div_sub_div_le (μ n) (rawIntermediate n)
      (fun _ => rawCenter n) (scale n) (rawFluctuationError n)
      (hScale n hn) (hFluctuationIntegral n hn)
  · exact hSeamErrorZero
  · exact hFluctuationErrorZero

/-- A finite signed maximum of a constant family is that constant. -/
theorem finiteSignedMax_const
    {ι : Type*} (degrees : Finset ι) (hdegrees : degrees.Nonempty) (c : ℝ) :
    finiteSignedMax degrees hdegrees (fun _ => c) = c := by
  apply le_antisymm
  · exact finiteSignedMax_le hdegrees (fun _ => c) (fun _ _ => le_rfl)
  · exact le_finiteSignedMax hdegrees (fun _ => c) hdegrees.choose_spec

/-- Canonical inactive completion of the pressure-lifting certificate.

On an inactive index this constructor uses one cell of length one, constant base and
lifted degree pressures equal to `inactivePressure`, cell/remainder/ratio errors equal to
zero, whole pressure equal to `inactivePressure`, and length ratio one.  All pressure
identities then hold exactly.  Thus projective cell estimates, inverse-row estimates, and
the literal pressure identifications are required only at active indices.

The active hypotheses remain scalar receiver assumptions: this theorem does not derive
them from Section 4 matrices or prove the required active-branch scale limits. -/
theorem pressureLiftToTargetInputVarying_inactiveFill
    {ι : Type*}
    (degrees : ℕ → Finset ι) (hdegrees : ∀ n, (degrees n).Nonempty)
    (active : ℕ → Bool)
    (base lifted : ℕ → ι → ℝ) (q m : ℕ → ℕ) (cellError : ℕ → ℝ)
    (wholeNormalizedPressure cellLengthRatio : ℕ → ℝ)
    (remainderError lengthRatioError inactivePressure : ℕ → ℝ)
    (hLifting : ∀ᶠ n in atTop, active n = true →
      0 < q n ∧ 0 < m n ∧ ∀ r, r ∈ degrees n →
        (q n : ℝ) * (base n r - cellError n) ≤ lifted n r ∧
          lifted n r ≤ (q n : ℝ) * (base n r + cellError n))
    (hNormalizedCellErrorZero : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, active n = true → |cellError n / (m n : ℝ)| < ε)
    (hRatioNonneg : ∀ n, active n = true → 0 ≤ cellLengthRatio n)
    (hRatioLeOne : ∀ n, active n = true → cellLengthRatio n ≤ 1)
    (hRemainder : ∀ n, active n = true →
      |wholeNormalizedPressure n -
        cellLengthRatio n *
          cellNormalizedPressureVarying degrees hdegrees lifted q m n| ≤
        remainderError n)
    (hRemainderZero : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, active n = true → |remainderError n| < ε)
    (hRatioBound : ∀ n, active n = true →
      |cellLengthRatio n - 1| ≤ lengthRatioError n)
    (hRatioErrorZero : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, active n = true → |lengthRatioError n| < ε) :
    PressureLiftToTargetInputVarying degrees hdegrees
      (inactiveFilledTriValue active base (fun n _ => inactivePressure n))
      (inactiveFilledTriValue active lifted (fun n _ => inactivePressure n))
      (inactiveFilledTriValue active q (fun _ => 1))
      (inactiveFilledTriValue active m (fun _ => 1))
      (inactiveFilledTriRate active cellError)
      (inactiveFilledTriValue active wholeNormalizedPressure inactivePressure)
      (inactiveFilledTriValue active cellLengthRatio (fun _ => 1))
      (inactiveFilledTriRate active remainderError)
      (inactiveFilledTriRate active lengthRatioError) := by
  refine
    { lifting_eventually := ?_
      normalized_cell_error_zero := ?_
      ratio_nonneg := ?_
      ratio_le_one := ?_
      remainder_bound := ?_
      remainder_zero := inactiveFilledTriRate_tendsto_zero
        active remainderError hRemainderZero
      ratio_bound := ?_
      ratio_error_zero := inactiveFilledTriRate_tendsto_zero
        active lengthRatioError hRatioErrorZero }
  · filter_upwards [hLifting] with n hn
    cases h : active n with
    | false =>
        simp [inactiveFilledTriValue, inactiveFilledTriRate, h]
    | true =>
        simpa [inactiveFilledTriValue, inactiveFilledTriRate, h] using hn h
  · have hSelected := inactiveFilledTriRate_tendsto_zero active
      (fun n => cellError n / (m n : ℝ)) hNormalizedCellErrorZero
    convert hSelected using 1
    funext n
    cases h : active n <;>
      simp [inactiveFilledTriValue, inactiveFilledTriRate, h]
  · intro n
    cases h : active n with
    | false => simp [inactiveFilledTriValue, h]
    | true => simpa [inactiveFilledTriValue, h] using hRatioNonneg n h
  · intro n
    cases h : active n with
    | false => simp [inactiveFilledTriValue, h]
    | true => simpa [inactiveFilledTriValue, h] using hRatioLeOne n h
  · intro n
    cases h : active n with
    | false =>
        simp [inactiveFilledTriValue, inactiveFilledTriRate,
          cellNormalizedPressureVarying, finiteSignedMax_const, h]
    | true =>
        simpa [inactiveFilledTriValue, inactiveFilledTriRate,
          cellNormalizedPressureVarying, h] using hRemainder n h
  · intro n
    cases h : active n with
    | false => simp [inactiveFilledTriValue, inactiveFilledTriRate, h]
    | true =>
        simpa [inactiveFilledTriValue, inactiveFilledTriRate, h] using hRatioBound n h

end CircularLawSections56.Section5
