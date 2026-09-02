import CircularLawSections56.Section5.LiteralPressureAdapter
import CircularLawSections56.Section5.PaperMesoscopicScaleLimits
import CircularLawSections56.Section5.Section4NormalizationAndFillers

/-!
# Literal Section 4--5 near-end-to-end assembly

This module specializes `NearEndToEnd.lean` to the quantities occurring in the
indicator proof.  It performs the bookkeeping which is independent of the concrete
matrix-row realization:

* normalize the determinant/FreshZ seam and the random-pressure fluctuation;
* fill every inactive (short-branch) index by the deterministic target;
* identify the deterministic centers with maxima of coordinate expectations;
* pass centered cell-product bounds to the finite-maximum pressure receiver; and
* discharge every asymptotic field from the paper's concrete mesoscopic scales.

The remaining `PhysicalLiteralLongBranchInputTri` fields are deliberately finite,
model-level statements.  They are the exact landing points for the literal row
reassembly: the two raw determinant/FreshZ seams, the centered `B * Q` cell-product bounds,
and the terminal inverse-row/length comparisons.  In particular, the structure does not
assume a pressure limit, a long-branch convergence statement, or the final conclusion.
Section 3 remains the named `Section3IndicatorAnchorsTri` premise.
-/

open Filter MeasureTheory Topology

namespace CircularLawSections56.Section5

universe u v

variable {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]

/-- The indices on which the Section 4--5 long argument is used. -/
def literalLongActive (shortBranch : ℕ → Bool) (n : ℕ) : Bool :=
  !shortBranch n

/-- A raw observable divided by its physical length on the long branch and filled by
the deterministic target on the short branch. -/
noncomputable def literalActiveNormalizedObservable
    (active : ℕ → Bool) (rawObservable : ∀ n, Ω n → ℝ)
    (scale : ℕ → ℕ) (target : ℝ) : ∀ n, Ω n → ℝ :=
  fun n ω => if active n then rawObservable n ω / (scale n : ℝ) else target

/-- Active-only measurability of the raw determinant observable is enough for the
normalized, inactive-filled observable.  This is the measurability input consumed by
the expectation-strength Section 6 bridge; inactive raw observables are unrestricted. -/
theorem literalActiveNormalizedObservable_aestronglyMeasurable
    (μ : ∀ n, Measure (Ω n))
    (active : ℕ → Bool) (rawObservable : ∀ n, Ω n → ℝ)
    (scale : ℕ → ℕ) (target : ℝ)
    (hRaw : ∀ n, active n = true → AEStronglyMeasurable (rawObservable n) (μ n)) :
    ∀ n, AEStronglyMeasurable
      (literalActiveNormalizedObservable active rawObservable scale target n) (μ n) := by
  intro n
  change AEStronglyMeasurable
    (fun ω : Ω n => if active n then rawObservable n ω / (scale n : ℝ) else target) (μ n)
  cases hActive : active n with
  | false =>
      simpa [hActive] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω n => target) (μ n))
  | true =>
      simpa [hActive, div_eq_mul_inv] using
        (hRaw n hActive).mul_const ((scale n : ℝ)⁻¹)

/-- Coordinatewise expected pressure. -/
noncomputable def literalCoordinateMeanPressure
    (μ : ∀ n, Measure (Ω n)) {ι : ℕ → Type v}
    (Y : ∀ n, ι n → Ω n → ℝ) : ∀ n, ι n → ℝ :=
  fun n r => ∫ ω, Y n r ω ∂μ n

/-- Finite maximum of the complete-cell pressures at one triangular index.  The degree
type may vary with `n`, in particular as `ExteriorDegree (2 * W n)`. -/
noncomputable def literalLiftedPressureMaximum
    {ι : ℕ → Type v} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (lifted : ∀ n, ι n → ℝ) (n : ℕ) : ℝ :=
  finiteSignedMax Finset.univ Finset.univ_nonempty (lifted n)

/-- The deterministic maximum of coordinate expectations, normalized by the physical
length and filled by the target off the long branch. -/
noncomputable def literalActiveNormalizedMeanPressure
    (μ : ∀ n, Measure (Ω n)) {ι : ℕ → Type v}
    [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (active : ℕ → Bool) (Y : ∀ n, ι n → Ω n → ℝ)
    (scale : ℕ → ℕ) (target : ℝ) : ℕ → ℝ :=
  fun n => if active n then
    coordinateMeanFiniteSignedMaxTri μ Y n / (scale n : ℝ)
  else target

/-- The random maximum pressure, normalized and inactive-filled. -/
noncomputable def literalActiveNormalizedRandomPressure
    {ι : ℕ → Type v} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (active : ℕ → Bool) (Y : ∀ n, ι n → Ω n → ℝ)
    (scale : ℕ → ℕ) (target : ℝ) : ∀ n, Ω n → ℝ :=
  fun n ω => if active n then
    randomFiniteSignedMaxTri Y n ω / (scale n : ℝ)
  else target

/-- Inactive-filled coordinate pressure.  The filler is the unnormalized pressure
`target` because the corresponding inactive cell length is one. -/
def literalActivePressureFamily {ι : Type v}
    (active : ℕ → Bool) (pressure : ℕ → ι → ℝ) (target : ℝ) :
    ℕ → ι → ℝ :=
  inactiveFilledTriValue active pressure (fun _ _ => target)

/-- Inactive-filled positive natural parameter used for cell counts and lengths. -/
def literalActiveNat (active : ℕ → Bool) (value : ℕ → ℕ) : ℕ → ℕ :=
  inactiveFilledTriValue active value (fun _ => 1)

/-- A rate is required to vanish only along the active branch. -/
def ActiveRateTendstoZero (active : ℕ → Bool) (rate : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, active n = true → |rate n| < ε

theorem activeRateTendstoZero_of_tendsto
    (active : ℕ → Bool) (rate : ℕ → ℝ)
    (hRate : Tendsto rate atTop (𝓝 0)) : ActiveRateTendstoZero active rate := by
  intro ε hε
  exact hRate.eventually (Metric.ball_mem_nhds 0 hε) |>.mono (by
    intro n hn _
    simpa [Real.dist_eq] using hn)

theorem ActiveRateTendstoZero.const_mul
    {active : ℕ → Bool} {rate : ℕ → ℝ}
    (hRate : ActiveRateTendstoZero active rate) (C : ℝ) :
    ActiveRateTendstoZero active (fun n => C * rate n) := by
  have hFilled := inactiveFilledTriRate_tendsto_zero active rate hRate
  have hZero : Tendsto (fun n => C * inactiveFilledTriRate active rate n)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hFilled
  intro ε hε
  filter_upwards [hZero.eventually (Metric.ball_mem_nhds 0 hε)] with n hn
  intro hActive
  simpa [inactiveFilledTriRate, hActive, Real.dist_eq] using hn

theorem ActiveRateTendstoZero.add
    {active : ℕ → Bool} {rate₁ rate₂ : ℕ → ℝ}
    (h₁ : ActiveRateTendstoZero active rate₁)
    (h₂ : ActiveRateTendstoZero active rate₂) :
    ActiveRateTendstoZero active (fun n => rate₁ n + rate₂ n) := by
  have hZero := (inactiveFilledTriRate_tendsto_zero active rate₁ h₁).add
    (inactiveFilledTriRate_tendsto_zero active rate₂ h₂)
  intro ε hε
  filter_upwards [hZero.eventually (Metric.ball_mem_nhds (0 + 0) hε)] with n hn
  intro hActive
  simpa [inactiveFilledTriRate, hActive, Real.dist_eq] using hn

/-- The calibration seam rate `W log(eW) / m₀(W)`. -/
noncomputable def paperCalibrationSeamRate
    (δ : ℝ) (W : ℕ → ℕ) (n : ℕ) : ℝ :=
  paperCellErrorScale W n / (paperMesoscopicCellLength δ W n : ℝ)

/-- A convenient sharp envelope for the normalized calibration pressure fluctuation.
The manuscript bound `sqrt(W/m) log(eW)` is at most a constant multiple of this rate
when `m ≥ m₀(W)`. -/
noncomputable def paperCalibrationPressureRate
    (δ : ℝ) (W : ℕ → ℕ) (n : ℕ) : ℝ :=
  paperLogEW W n / (W n : ℝ) ^ (δ / 2)

/-- Concrete envelope for the fraction of rows not covered by complete cells.  The
first summand pays for the reserved `2W` rows and the second for the balanced terminal
remainder. -/
noncomputable def paperPhysicalLengthRatioError
    (δ : ℝ) (W N : ℕ → ℕ) (n : ℕ) : ℝ :=
  2 * paperFinalSeamRate W N n + paperBalancedRemainderRate δ W n

theorem paperCalibrationSeamRate_tendsto_zero
    (δ γ : ℝ) (W N : ℕ → ℕ)
    (hScale : PaperMesoscopicScaleChoice δ γ W N) :
    Tendsto (paperCalibrationSeamRate δ W) atTop (𝓝 0) := by
  exact hScale.cell_error_rate_zero

theorem paperCalibrationPressureRate_tendsto_zero
    (δ γ : ℝ) (W N : ℕ → ℕ)
    (hScale : PaperMesoscopicScaleChoice δ γ W N) :
    Tendsto (paperCalibrationPressureRate δ W) atTop (𝓝 0) := by
  exact paperLogEW_div_rpow_tendsto_zero W hScale.bandwidth_tendsto
    (half_pos hScale.delta_pos)

theorem paperPhysicalLengthRatioError_tendsto_zero
    (δ γ : ℝ) (W N : ℕ → ℕ)
    (hScale : PaperMesoscopicScaleChoice δ γ W N) :
    Tendsto (paperPhysicalLengthRatioError δ W N) atTop (𝓝 0) := by
  change Tendsto (fun n =>
    2 * paperFinalSeamRate W N n + paperBalancedRemainderRate δ W n) atTop (𝓝 0)
  simpa only [mul_zero, zero_add] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
      hScale.final_seam_rate_zero).add
      hScale.balanced_remainder_rate_zero

/-- The final paper rate vanishes on the long branch even when short and long indices
interleave infinitely often.  An inactive auxiliary dimension is used only in the proof;
the physical dimension `N` is unchanged on every active index. -/
theorem paperFinalSeamRate_tendsto_zero_on_active
    (active : ℕ → Bool) (γ : ℝ) (W N : ℕ → ℕ)
    (hγ : 0 < γ) (hW : Tendsto W atTop atTop)
    (hLong : ∀ᶠ n in atTop, active n = true →
      (W n : ℝ) ^ (1 + γ) < (N n : ℝ)) :
    ActiveRateTendstoZero active (paperFinalSeamRate W N) := by
  let N' : ℕ → ℕ := fun n =>
    if active n then N n else ⌈(W n : ℝ) ^ (1 + γ)⌉₊ + 1
  have hLong' : ∀ᶠ n in atTop, (W n : ℝ) ^ (1 + γ) < (N' n : ℝ) := by
    filter_upwards [hLong] with n hn
    cases hActive : active n with
    | true => simpa [N', hActive] using hn hActive
    | false =>
        have hceil := Nat.le_ceil ((W n : ℝ) ^ (1 + γ))
        simp only [N', hActive, Bool.false_eq_true, ↓reduceIte, Nat.cast_add,
          Nat.cast_one]
        linarith
  have hRate := paperFinalSeamRate_tendsto_zero γ W N' hγ hW hLong'
  intro ε hε
  filter_upwards [hRate.eventually (Metric.ball_mem_nhds 0 hε)] with n hn
  intro hActive
  simpa [paperFinalSeamRate, N', hActive, Real.dist_eq] using hn

/-- The paper `O(W log(eW))` cell bound implies the required active normalized error
limit for every physical cell length at least `m₀(W)`.  No cell-error limit is supplied
by the caller. -/
theorem active_cell_error_normalized_zero_of_paper_bound
    (active : ℕ → Bool) (δ : ℝ) (W m : ℕ → ℕ)
    (error : ℕ → ℝ) (C : ℝ)
    (hδ : 0 < δ) (hW : Tendsto W atTop atTop)
    (hLength : ∀ᶠ n in atTop, active n = true →
      paperMesoscopicCellLength δ W n ≤ m n)
    (hNonneg : ∀ᶠ n in atTop, active n = true → 0 ≤ error n)
    (hBound : ∀ᶠ n in atTop, active n = true →
      error n ≤ C * paperCellErrorScale W n) :
    ActiveRateTendstoZero active (fun n => error n / (m n : ℝ)) := by
  have hUpper : Tendsto (fun n => C * paperCalibrationSeamRate δ W n)
      atTop (𝓝 0) := by
    exact_mod_cast (show Tendsto
      (fun n => C * (paperCellErrorScale W n /
        (paperMesoscopicCellLength δ W n : ℝ))) atTop (𝓝 0) by
      simpa using tendsto_const_nhds.mul
        (paperCellErrorScale_div_mesoscopicLength_tendsto_zero δ W hδ hW))
  have hWpos : ∀ᶠ n in atTop, 0 < (W n : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hW).eventually_gt_atTop 0
  intro ε hε
  filter_upwards [hLength, hNonneg, hBound, hWpos,
    hUpper.eventually (Metric.ball_mem_nhds 0 hε)] with n hLen hErr hBnd hPos hSmall
  intro hActive
  have hm₀ : 0 < (paperMesoscopicCellLength δ W n : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hPos (1 + δ)))
  have hm : (paperMesoscopicCellLength δ W n : ℝ) ≤ (m n : ℝ) :=
    Nat.cast_le.mpr (hLen hActive)
  rw [abs_of_nonneg (div_nonneg (hErr hActive) (Nat.cast_nonneg _))]
  calc
    error n / (m n : ℝ) ≤
        error n / (paperMesoscopicCellLength δ W n : ℝ) :=
      div_le_div_of_nonneg_left (hErr hActive) hm₀ hm
    _ ≤ (C * paperCellErrorScale W n) /
        (paperMesoscopicCellLength δ W n : ℝ) :=
      div_le_div_of_nonneg_right (hBnd hActive) hm₀.le
    _ = C * paperCalibrationSeamRate δ W n := by
      unfold paperCalibrationSeamRate
      ring
    _ ≤ |C * paperCalibrationSeamRate δ W n| := le_abs_self _
    _ < ε := by simpa [Real.dist_eq] using hSmall

/-- Direct constructor from the literal Section 4 seam and maximal-pressure estimate to
the exact normalized, inactive-filled two-step receiver used by `NearEndToEnd`.

Unlike the generic receiver constructor, the fluctuation integrability and integral
bound are not hypotheses: they are obtained from `MemLp` and the Section 4
`maxCenteredAbs` bound. -/
noncomputable def literalTwoStepL1ApproximationTri_of_pressure_bound
    {ι : ℕ → Type v} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (active : ℕ → Bool) (rawObservable : ∀ n, Ω n → ℝ)
    (Y : ∀ n, ι n → Ω n → ℝ) (scale : ℕ → ℕ) (target : ℝ)
    (seamRate fluctuationRate : ℕ → ℝ)
    (hScale : ∀ n, active n = true → 0 < scale n)
    (hSeamIntegrable : ∀ n, active n = true →
      Integrable (fun ω =>
        |rawObservable n ω - randomFiniteSignedMaxTri Y n ω|) (μ n))
    (hSeamIntegral : ∀ n, active n = true →
      (∫ ω, |rawObservable n ω - randomFiniteSignedMaxTri Y n ω| ∂μ n) ≤
        (scale n : ℝ) * seamRate n)
    (hY : ∀ n, active n = true → ∀ r, MemLp (Y n r) 2 (μ n))
    (hPressureBound : ∀ n, active n = true →
      (∫ ω, CircularLawSection4.maxCenteredAbs (μ n) (Y n) ω ∂μ n) ≤
        (scale n : ℝ) * fluctuationRate n)
    (hSeamRateZero : ActiveRateTendstoZero active seamRate)
    (hFluctuationRateZero : ActiveRateTendstoZero active fluctuationRate) :
    TwoStepL1ApproximationTri μ
      (literalActiveNormalizedObservable active rawObservable scale target)
      (literalActiveNormalizedMeanPressure μ active Y scale target) := by
  have hObservable :
      literalActiveNormalizedObservable active rawObservable scale target =
        inactiveFilledTriObservable active
          (fun n ω => rawObservable n ω / (scale n : ℝ))
          (literalActiveNormalizedMeanPressure μ active Y scale target) := by
    funext n ω
    cases hn : active n <;>
      simp [literalActiveNormalizedObservable, inactiveFilledTriObservable,
        literalActiveNormalizedMeanPressure, hn]
  rw [hObservable]
  apply twoStepL1ApproximationTri_inactiveFill μ active
    (fun n ω => rawObservable n ω / (scale n : ℝ))
    (fun n ω => randomFiniteSignedMaxTri Y n ω / (scale n : ℝ))
    (literalActiveNormalizedMeanPressure μ active Y scale target)
    seamRate fluctuationRate
  · intro n hn
    exact integrable_abs_div_sub_div (μ n) (rawObservable n)
      (randomFiniteSignedMaxTri Y n) (scale n : ℝ)
      (by exact_mod_cast hScale n hn) (hSeamIntegrable n hn)
  · intro n hn
    have h := integral_abs_div_sub_div_le (μ n) (rawObservable n)
      (randomFiniteSignedMaxTri Y n) (scale n : ℝ)
      ((scale n : ℝ) * seamRate n) (by exact_mod_cast hScale n hn)
      (hSeamIntegral n hn)
    simpa [literalActiveNormalizedMeanPressure, hn,
      Nat.cast_ne_zero.mpr (hScale n hn).ne'] using h
  · intro n hn
    have hRaw := integrable_abs_randomFiniteSignedMax_sub_mean
      (μ n) (Y n) (hY n hn)
    have hDiv := integrable_abs_div_sub_div (μ n)
      (randomFiniteSignedMaxTri Y n)
      (fun _ => coordinateMeanFiniteSignedMaxTri μ Y n)
      (scale n : ℝ) (by exact_mod_cast hScale n hn) hRaw
    simpa [literalActiveNormalizedMeanPressure, hn] using hDiv
  · intro n hn
    have hRaw :=
      (integral_abs_randomFiniteSignedMax_sub_mean_le_maxCenteredAbs
        (μ n) (Y n) (hY n hn)).trans (hPressureBound n hn)
    have h := integral_abs_div_sub_div_le (μ n)
      (randomFiniteSignedMaxTri Y n)
      (fun _ => coordinateMeanFiniteSignedMaxTri μ Y n)
      (scale n : ℝ) ((scale n : ℝ) * fluctuationRate n)
      (by exact_mod_cast hScale n hn) hRaw
    simpa [literalActiveNormalizedMeanPressure, hn,
      Nat.cast_ne_zero.mpr (hScale n hn).ne'] using h
  · exact hSeamRateZero
  · exact hFluctuationRateZero

/-- The finite physical statements which remain after all deterministic and asymptotic
bookkeeping is factored out.

The two `Y` families are the literal outside open pressures at calibration and target
length.  `cell_bounds` is the cumulative output of the centered literal `B * Q`
cell-product telescope, not the stronger assertion that every expected increment has
the same lower bound.
`inverse_row_remainder` is the sole analytical use of the one-row forward/inverse cost.
-/
structure PhysicalLiteralLongBranchInputTri
    {ι : ℕ → Type v} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (μ : ∀ n, Measure (Ω n))
    (active : ℕ → Bool)
    (calibrationRaw finalRaw : ∀ n, Ω n → ℝ)
    (calibrationY finalY : ∀ n, ι n → Ω n → ℝ)
    (lifted : ∀ n, ι n → ℝ) (q m N : ℕ → ℕ)
    (cellError cellLengthRatio : ℕ → ℝ)
    (δ : ℝ) (W : ℕ → ℕ) (Ccell : ℝ)
    (calibrationSeamRate calibrationFluctuationRate
      finalSeamRate finalFluctuationRate remainderRate
      lengthRatioRate : ℕ → ℝ) : Prop where
  calibration_scale_pos : ∀ n, active n = true → 0 < m n
  final_scale_pos : ∀ n, active n = true → 0 < N n
  calibration_seam_integrable : ∀ n, active n = true →
    Integrable (fun ω =>
      |calibrationRaw n ω - randomFiniteSignedMaxTri calibrationY n ω|) (μ n)
  calibration_seam_bound : ∀ n, active n = true →
    (∫ ω, |calibrationRaw n ω -
      randomFiniteSignedMaxTri calibrationY n ω| ∂μ n) ≤
      (m n : ℝ) * calibrationSeamRate n
  calibration_pressure_memLp : ∀ n, active n = true → ∀ r,
    MemLp (calibrationY n r) 2 (μ n)
  calibration_pressure_bound : ∀ n, active n = true →
    (∫ ω, CircularLawSection4.maxCenteredAbs (μ n)
      (calibrationY n) ω ∂μ n) ≤
      (m n : ℝ) * calibrationFluctuationRate n
  final_seam_integrable : ∀ n, active n = true →
    Integrable (fun ω =>
      |finalRaw n ω - randomFiniteSignedMaxTri finalY n ω|) (μ n)
  final_seam_bound : ∀ n, active n = true →
    (∫ ω, |finalRaw n ω - randomFiniteSignedMaxTri finalY n ω| ∂μ n) ≤
      (N n : ℝ) * finalSeamRate n
  final_pressure_memLp : ∀ n, active n = true → ∀ r,
    MemLp (finalY n r) 2 (μ n)
  final_pressure_bound : ∀ n, active n = true →
    (∫ ω, CircularLawSection4.maxCenteredAbs (μ n) (finalY n) ω ∂μ n) ≤
      (N n : ℝ) * finalFluctuationRate n
  cell_scale : ∀ᶠ n in atTop, active n = true → 0 < q n ∧ 0 < m n
  cell_bounds : ∀ n, active n = true → ∀ r,
    (q n : ℝ) *
        (literalCoordinateMeanPressure μ calibrationY n r - cellError n) ≤
      lifted n r ∧
    lifted n r ≤ (q n : ℝ) *
        (literalCoordinateMeanPressure μ calibrationY n r + cellError n)
  cell_length_lower : ∀ᶠ n in atTop, active n = true →
    paperMesoscopicCellLength δ W n ≤ m n
  cell_error_nonneg : ∀ᶠ n in atTop, active n = true → 0 ≤ cellError n
  cell_error_bound : ∀ᶠ n in atTop, active n = true →
    cellError n ≤ Ccell * paperCellErrorScale W n
  ratio_nonneg : ∀ n, active n = true → 0 ≤ cellLengthRatio n
  ratio_le_one : ∀ n, active n = true → cellLengthRatio n ≤ 1
  inverse_row_remainder : ∀ n, active n = true →
    |coordinateMeanFiniteSignedMaxTri μ finalY n / (N n : ℝ) -
      cellLengthRatio n *
        cellNormalizedPressureVarying scalarPressureDegrees
          scalarPressureDegrees_nonempty
          (scalarPressureFamily (literalLiftedPressureMaximum lifted)) q m n| ≤
      remainderRate n
  length_ratio_bound : ∀ n, active n = true →
    |cellLengthRatio n - 1| ≤ lengthRatioRate n

/-- Optional adapter for a model exposing centered increments instead of a cumulative
cell-product estimate.  The physical input itself only requires the weaker cumulative
output, matching the public literal `B * Q` telescope. -/
theorem literal_cell_bounds_of_increments
    {ι : ℕ → Type v} (active : ℕ → Bool)
    (base lifted : ∀ n, ι n → ℝ) (cellPressure : ∀ n, ι n → ℕ → ℝ)
    (q : ℕ → ℕ) (cellError : ℕ → ℝ)
    (hZero : ∀ n, active n = true → ∀ r, cellPressure n r 0 = 0)
    (hLifted : ∀ n, active n = true → ∀ r,
      lifted n r = cellPressure n r (q n))
    (hIncrement : ∀ n, active n = true → ∀ r, ∀ j < q n,
      base n r - cellError n ≤ cellPressure n r (j + 1) - cellPressure n r j ∧
        cellPressure n r (j + 1) - cellPressure n r j ≤ base n r + cellError n) :
    ∀ n, active n = true → ∀ r,
      (q n : ℝ) * (base n r - cellError n) ≤ lifted n r ∧
        lifted n r ≤ (q n : ℝ) * (base n r + cellError n) := by
  intro n hn r
  rw [hLifted n hn r]
  exact pressure_lift_degree (cellPressure n r) (base n r) (cellError n) (q n)
    (hZero n hn r) (hIncrement n hn r)

/-- Concrete-rate specialization of the physical input.  Only finite literal estimates
are fields; all six rate limits are fixed by the paper scales and proved below. -/
abbrev PaperPhysicalLiteralLongBranchInputTri
    {ι : ℕ → Type v} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (μ : ∀ n, Measure (Ω n))
    (active : ℕ → Bool)
    (calibrationRaw finalRaw : ∀ n, Ω n → ℝ)
    (calibrationY finalY : ∀ n, ι n → Ω n → ℝ)
    (lifted : ∀ n, ι n → ℝ) (q m N : ℕ → ℕ)
    (cellError cellLengthRatio : ℕ → ℝ)
    (δ : ℝ) (W : ℕ → ℕ)
    (CcalSeam CcalFluct CfinalSeam CfinalFluct Ccell Crow : ℝ) : Prop :=
  PhysicalLiteralLongBranchInputTri μ active calibrationRaw finalRaw
    calibrationY finalY lifted q m N cellError cellLengthRatio δ W Ccell
    (fun n => CcalSeam * paperCalibrationSeamRate δ W n)
    (fun n => CcalFluct * paperCalibrationPressureRate δ W n)
    (fun n => CfinalSeam * paperFinalSeamRate W N n)
    (fun n => CfinalFluct * paperFinalSeamRate W N n)
    (fun n => Crow * paperBalancedRemainderRate δ W n)
    (paperPhysicalLengthRatioError δ W N)

/-- Expectation-strength endpoint of the literal long branch.  Keeping the two-step
`L¹` certificate as data, rather than only its probability consequence, lets Section 6
reuse the actual expected absolute error and the deterministic mean-pressure limit. -/
structure LiteralFinalClosureCertificateTri
    (μ : ∀ n, Measure (Ω n))
    (observable : ∀ n, Ω n → ℝ) (meanPressure : ℕ → ℝ) (target : ℝ) where
  finalClosure : TwoStepL1ApproximationTri μ observable meanPressure
  meanPressure_tendsto : Tendsto meanPressure atTop (𝓝 target)

theorem LiteralFinalClosureCertificateTri.tendstoInProbability
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {observable : ∀ n, Ω n → ℝ} {meanPressure : ℕ → ℝ} {target : ℝ}
    (h : LiteralFinalClosureCertificateTri μ observable meanPressure target) :
    TendstoInProbabilityTri μ observable target := by
  exact longBranch_tendstoInProbabilityTri_of_L1_seams
    μ observable h.finalClosure.intermediate meanPressure
    h.finalClosure.seamError h.finalClosure.fluctuationError target
    h.finalClosure.seamIntegrable h.finalClosure.seamIntegral_le
    h.finalClosure.fluctuationIntegrable h.finalClosure.fluctuationIntegral_le
    h.finalClosure.seamError_tendsto_zero h.finalClosure.fluctuationError_tendsto_zero
    h.meanPressure_tendsto

/-- Extract the deterministic whole-pressure limit from the pressure receiver.  This
exposes the internal deterministic endpoint of `NearEndToEnd` for expectation-strength
downstream arguments. -/
theorem PressureLiftToTargetInputVarying.whole_tendsto
    {κ : Type*} (degrees : ℕ → Finset κ) (hdegrees : ∀ n, (degrees n).Nonempty)
    (base lifted : ℕ → κ → ℝ) (q m : ℕ → ℕ) (cellError : ℕ → ℝ)
    (wholeNormalizedPressure cellLengthRatio remainderError lengthRatioError : ℕ → ℝ)
    (target : ℝ)
    (h : PressureLiftToTargetInputVarying degrees hdegrees base lifted q m cellError
      wholeNormalizedPressure cellLengthRatio remainderError lengthRatioError)
    (hBase : Tendsto (baseNormalizedPressureVarying degrees hdegrees base m)
      atTop (𝓝 target)) :
    Tendsto wholeNormalizedPressure atTop (𝓝 target) := by
  have hCell : Tendsto
      (cellNormalizedPressureVarying degrees hdegrees lifted q m) atTop (𝓝 target) :=
    global_pressure_on_cell_multiples_varyingDegrees_eventually
      degrees hdegrees base lifted q m cellError target h.lifting_eventually
      h.normalized_cell_error_zero hBase
  have hCellError : Tendsto
      (fun n => |cellNormalizedPressureVarying degrees hdegrees lifted q m n - target|)
      atTop (𝓝 0) := by
    simpa using (hCell.sub_const target).abs
  exact target_pressure_tendsto wholeNormalizedPressure
    (cellNormalizedPressureVarying degrees hdegrees lifted q m)
    cellLengthRatio target remainderError
    (fun n => |cellNormalizedPressureVarying degrees hdegrees lifted q m n - target|)
    lengthRatioError h.ratio_nonneg h.ratio_le_one h.remainder_bound (fun _ => le_rfl)
    h.ratio_bound h.remainder_zero hCellError h.ratio_error_zero

/-- Final fixed-spectral-parameter literal certificate constructor.

Everything after the physical finite estimates and the two known Section 3 anchors is
proved here.  In particular, neither a `Section4LongBranchQuantitativeInputTri` nor a
`PressureLiftToTargetInputVarying` is assumed by the caller. -/
noncomputable def literalNearEndToEndCertificate
    {ι : ℕ → Type v} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (shortBranch : ℕ → Bool)
    (shortLogPotential : ∀ n, Ω n → ℝ)
    (calibrationRaw finalRaw : ∀ n, Ω n → ℝ)
    (calibrationY finalY : ∀ n, ι n → Ω n → ℝ)
    (lifted : ∀ n, ι n → ℝ) (q m N W : ℕ → ℕ)
    (cellError cellLengthRatio : ℕ → ℝ)
    (target δ γ CcalSeam CcalFluct CfinalSeam CfinalFluct Ccell Crow : ℝ)
    (hδ : 0 < δ) (hδγ : δ < γ) (_hγ : γ < 1 / 8)
    (hW : Tendsto W atTop atTop)
    (hLong : ∀ᶠ n in atTop, literalLongActive shortBranch n = true →
      (W n : ℝ) ^ (1 + γ) < (N n : ℝ))
    (hPhysical : PaperPhysicalLiteralLongBranchInputTri μ
      (literalLongActive shortBranch) calibrationRaw finalRaw
      calibrationY finalY lifted q m N cellError cellLengthRatio
      δ W CcalSeam CcalFluct CfinalSeam CfinalFluct Ccell Crow)
    (hSection3 : Section3IndicatorAnchorsTri μ shortLogPotential
      (literalActiveNormalizedObservable (literalLongActive shortBranch)
        calibrationRaw m target) target) :
    LiteralFinalClosureCertificateTri μ
      (literalActiveNormalizedObservable (literalLongActive shortBranch)
        finalRaw N target)
      (literalActiveNormalizedMeanPressure μ (literalLongActive shortBranch)
        finalY N target) target := by
  let active := literalLongActive shortBranch
  have hCalSeamZero : Tendsto
      (fun n => CcalSeam * paperCalibrationSeamRate δ W n)
      atTop (𝓝 0) := by
    simpa [paperCalibrationSeamRate] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => CcalSeam) atTop (𝓝 CcalSeam)).mul
      (paperCellErrorScale_div_mesoscopicLength_tendsto_zero δ W hδ hW)
  have hCalFluctZero : Tendsto
      (fun n => CcalFluct * paperCalibrationPressureRate δ W n)
      atTop (𝓝 0) := by
    simpa [paperCalibrationPressureRate] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => CcalFluct) atTop (𝓝 CcalFluct)).mul
      (paperLogEW_div_rpow_tendsto_zero W hW (half_pos hδ))
  have hFinalRateZero := paperFinalSeamRate_tendsto_zero_on_active
    active γ W N (lt_trans hδ hδγ) hW hLong
  have hFinalSeamZero := hFinalRateZero.const_mul CfinalSeam
  have hFinalFluctZero := hFinalRateZero.const_mul CfinalFluct
  have hRemainderZero : Tendsto
      (fun n => Crow * paperBalancedRemainderRate δ W n)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (paperBalancedRemainderRate_tendsto_zero δ W hδ hW)
  have hLengthRatioZero : ActiveRateTendstoZero active
      (paperPhysicalLengthRatioError δ W N) :=
    (hFinalRateZero.const_mul 2).add
      (activeRateTendstoZero_of_tendsto active _
        (paperBalancedRemainderRate_tendsto_zero δ W hδ hW))
  have hCellErrorZero := active_cell_error_normalized_zero_of_paper_bound
    active δ W m cellError Ccell hδ hW hPhysical.cell_length_lower
    hPhysical.cell_error_nonneg hPhysical.cell_error_bound
  let hCalibration : TwoStepL1ApproximationTri μ
      (literalActiveNormalizedObservable active calibrationRaw m target)
      (literalActiveNormalizedMeanPressure μ active calibrationY m target) :=
    literalTwoStepL1ApproximationTri_of_pressure_bound μ active
      calibrationRaw calibrationY m target
      (fun n => CcalSeam * paperCalibrationSeamRate δ W n)
      (fun n => CcalFluct * paperCalibrationPressureRate δ W n)
      hPhysical.calibration_scale_pos hPhysical.calibration_seam_integrable
      hPhysical.calibration_seam_bound hPhysical.calibration_pressure_memLp
      hPhysical.calibration_pressure_bound
      (activeRateTendstoZero_of_tendsto active _ hCalSeamZero)
      (activeRateTendstoZero_of_tendsto active _ hCalFluctZero)
  let hFinal : TwoStepL1ApproximationTri μ
      (literalActiveNormalizedObservable active finalRaw N target)
      (literalActiveNormalizedMeanPressure μ active finalY N target) :=
    literalTwoStepL1ApproximationTri_of_pressure_bound μ active
      finalRaw finalY N target
      (fun n => CfinalSeam * paperFinalSeamRate W N n)
      (fun n => CfinalFluct * paperFinalSeamRate W N n)
      hPhysical.final_scale_pos hPhysical.final_seam_integrable
      hPhysical.final_seam_bound hPhysical.final_pressure_memLp
      hPhysical.final_pressure_bound hFinalSeamZero hFinalFluctZero
  have hLiftActive : ∀ᶠ n in atTop, active n = true →
      0 < q n ∧ 0 < m n ∧ ∀ r, r ∈ scalarPressureDegrees n →
        (q n : ℝ) *
            (scalarPressureFamily (coordinateMeanFiniteSignedMaxTri μ calibrationY)
              n r - cellError n) ≤
          scalarPressureFamily (literalLiftedPressureMaximum lifted) n r ∧
        scalarPressureFamily (literalLiftedPressureMaximum lifted) n r ≤
          (q n : ℝ) *
            (scalarPressureFamily (coordinateMeanFiniteSignedMaxTri μ calibrationY)
              n r + cellError n) := by
    filter_upwards [hPhysical.cell_scale] with n hn
    intro hActive
    refine ⟨(hn hActive).1, (hn hActive).2, ?_⟩
    intro r _
    exact finiteSignedMax_cell_bounds Finset.univ_nonempty
      (literalCoordinateMeanPressure μ calibrationY n) (lifted n)
      (q n : ℝ) (cellError n) (Nat.cast_nonneg _)
      (fun i _ => hPhysical.cell_bounds n hActive i)
  have hPressure : PressureLiftToTargetInputVarying
      scalarPressureDegrees scalarPressureDegrees_nonempty
      (literalActivePressureFamily active
        (scalarPressureFamily (coordinateMeanFiniteSignedMaxTri μ calibrationY)) target)
      (literalActivePressureFamily active
        (scalarPressureFamily (literalLiftedPressureMaximum lifted)) target)
      (literalActiveNat active q) (literalActiveNat active m)
      (inactiveFilledTriRate active cellError)
      (literalActiveNormalizedMeanPressure μ active finalY N target)
      (inactiveFilledTriValue active cellLengthRatio (fun _ => 1))
      (inactiveFilledTriRate active
        (fun n => Crow * paperBalancedRemainderRate δ W n))
      (inactiveFilledTriRate active
        (paperPhysicalLengthRatioError δ W N)) := by
    apply pressureLiftToTargetInputVarying_inactiveFill
      scalarPressureDegrees scalarPressureDegrees_nonempty
      active (scalarPressureFamily (coordinateMeanFiniteSignedMaxTri μ calibrationY))
      (scalarPressureFamily (literalLiftedPressureMaximum lifted)) q m cellError
      (fun n => coordinateMeanFiniteSignedMaxTri μ finalY n / (N n : ℝ))
      cellLengthRatio
      (fun n => Crow * paperBalancedRemainderRate δ W n)
      (paperPhysicalLengthRatioError δ W N) (fun _ => target)
    · exact hLiftActive
    · exact hCellErrorZero
    · exact hPhysical.ratio_nonneg
    · exact hPhysical.ratio_le_one
    · exact hPhysical.inverse_row_remainder
    · exact activeRateTendstoZero_of_tendsto active _ hRemainderZero
    · exact hPhysical.length_ratio_bound
    · exact hLengthRatioZero
  have hSection4 : Section4LongBranchQuantitativeInputTri μ
      (literalActiveNormalizedObservable active calibrationRaw m target)
      (literalActiveNormalizedObservable active finalRaw N target)
      (baseNormalizedPressureVarying
        scalarPressureDegrees scalarPressureDegrees_nonempty
        (literalActivePressureFamily active
          (scalarPressureFamily (coordinateMeanFiniteSignedMaxTri μ calibrationY)) target)
        (literalActiveNat active m))
      (literalActiveNormalizedMeanPressure μ active finalY N target) := by
    refine { calibration := ?_, finalClosure := hFinal }
    convert hCalibration using 1
    funext n
    unfold baseNormalizedPressureVarying literalActivePressureFamily
      literalActiveNat literalActiveNormalizedMeanPressure scalarPressureFamily
      inactiveFilledTriValue
    cases active n <;> simp [finiteSignedMax_const]
  have hBaseTarget : Tendsto
      (baseNormalizedPressureVarying scalarPressureDegrees scalarPressureDegrees_nonempty
        (literalActivePressureFamily active
          (scalarPressureFamily (coordinateMeanFiniteSignedMaxTri μ calibrationY)) target)
        (literalActiveNat active m)) atTop (𝓝 target) :=
    deterministic_center_tendsto_of_tri_anchor_and_two_L1_seams
      μ (literalActiveNormalizedObservable active calibrationRaw m target)
      hSection4.calibration.intermediate _ hSection4.calibration.seamError
      hSection4.calibration.fluctuationError target hSection3.mesoscopic
      hSection4.calibration.seamIntegrable hSection4.calibration.seamIntegral_le
      hSection4.calibration.fluctuationIntegrable
      hSection4.calibration.fluctuationIntegral_le
      hSection4.calibration.seamError_tendsto_zero
      hSection4.calibration.fluctuationError_tendsto_zero
  exact
    { finalClosure := hFinal
      meanPressure_tendsto :=
        hPressure.whole_tendsto _ _ _ _ _ _ _ _ _ _ _ target hBaseTarget }

/-- Probability consequence of the expectation-strength literal certificate.  Exterior
degrees may vary with `n`, and the short/long branches may interleave arbitrarily. -/
theorem indicator_logPotential_literal_nearEndToEnd_tri
    {ι : ℕ → Type v} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (shortBranch : ℕ → Bool)
    (shortLogPotential : ∀ n, Ω n → ℝ)
    (calibrationRaw finalRaw : ∀ n, Ω n → ℝ)
    (calibrationY finalY : ∀ n, ι n → Ω n → ℝ)
    (lifted : ∀ n, ι n → ℝ) (q m N W : ℕ → ℕ)
    (cellError cellLengthRatio : ℕ → ℝ)
    (target δ γ CcalSeam CcalFluct CfinalSeam CfinalFluct Ccell Crow : ℝ)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8)
    (hW : Tendsto W atTop atTop)
    (hLong : ∀ᶠ n in atTop, literalLongActive shortBranch n = true →
      (W n : ℝ) ^ (1 + γ) < (N n : ℝ))
    (hPhysical : PaperPhysicalLiteralLongBranchInputTri μ
      (literalLongActive shortBranch) calibrationRaw finalRaw
      calibrationY finalY lifted q m N cellError cellLengthRatio
      δ W CcalSeam CcalFluct CfinalSeam CfinalFluct Ccell Crow)
    (hSection3 : Section3IndicatorAnchorsTri μ shortLogPotential
      (literalActiveNormalizedObservable (literalLongActive shortBranch)
        calibrationRaw m target) target) :
    TendstoInProbabilityTri μ
      (branchSelectedTri shortBranch shortLogPotential
        (literalActiveNormalizedObservable (literalLongActive shortBranch)
          finalRaw N target)) target := by
  have hCertificate := literalNearEndToEndCertificate μ shortBranch shortLogPotential
    calibrationRaw finalRaw calibrationY finalY lifted q m N W cellError cellLengthRatio
    target δ γ CcalSeam CcalFluct CfinalSeam CfinalFluct Ccell Crow
    hδ hδγ hγ hW hLong hPhysical hSection3
  exact tendstoInProbabilityTri_branchSelected μ shortBranch shortLogPotential
    (literalActiveNormalizedObservable (literalLongActive shortBranch) finalRaw N target)
    target hSection3.target_size hCertificate.tendstoInProbability

/-- Apply a constructed literal certificate to the actual physical log potential.
Only the physical observable identification is still needed here; all long-branch
analytic information is retained in `hCertificate`. -/
theorem indicator_actualLogPotential_of_literal_certificate
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (shortBranch : ℕ → Bool)
    (shortLogPotential calibrationLogPotential longLogPotential actualLogPotential :
      ∀ n, Ω n → ℝ)
    (wholeMeanPressure : ℕ → ℝ) (target : ℝ)
    (hSection3 : Section3IndicatorAnchorsTri μ
      shortLogPotential calibrationLogPotential target)
    (hCertificate : LiteralFinalClosureCertificateTri μ
      longLogPotential wholeMeanPressure target)
    (hActual : ∀ n ω, actualLogPotential n ω =
      branchSelectedTri shortBranch shortLogPotential longLogPotential n ω) :
    TendstoInProbabilityTri μ actualLogPotential target := by
  have hSelected := tendstoInProbabilityTri_branchSelected μ shortBranch
    shortLogPotential longLogPotential target hSection3.target_size
    hCertificate.tendstoInProbability
  exact hSelected.congr (fun n ω => (hActual n ω).symm) rfl

/-- External replacement-principle wrapper for a physical observable obtained from the
literal certificate.  The Hilbert--Schmidt identity is converted to a uniform bound;
the a.e.-spectral-parameter replacement theorem remains an honest caller input. -/
theorem indicator_circularLaw_of_literal_certificate
    {CircularLawConclusion : Prop}
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (shortBranch : ℕ → Bool)
    (shortLogPotential calibrationLogPotential longLogPotential actualLogPotential :
      ∀ n, Ω n → ℝ)
    (wholeMeanPressure normalizedExpectedHSSquare : ℕ → ℝ) (target : ℝ)
    (hSection3 : Section3IndicatorAnchorsTri μ
      shortLogPotential calibrationLogPotential target)
    (hCertificate : LiteralFinalClosureCertificateTri μ
      longLogPotential wholeMeanPressure target)
    (hActual : ∀ n ω, actualLogPotential n ω =
      branchSelectedTri shortBranch shortLogPotential longLogPotential n ω)
    (hHSIdentity : ∀ n, normalizedExpectedHSSquare n = 1)
    (hReplacement : TendstoInProbabilityTri μ actualLogPotential target →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ n, normalizedExpectedHSSquare n ≤ C) →
      CircularLawConclusion) :
    CircularLawConclusion := by
  exact hReplacement
    (indicator_actualLogPotential_of_literal_certificate μ shortBranch
      shortLogPotential calibrationLogPotential longLogPotential actualLogPotential
      wholeMeanPressure target hSection3 hCertificate hActual)
    (uniform_hs_square_bound_of_eq_one normalizedExpectedHSSquare hHSIdentity)

end CircularLawSections56.Section5
