import CircularLawSections56.Section5.LiteralAdaptedCellJointAdapter
import CircularLawSections56.Section5.LiteralIidCellTelescopeAdapter
import CircularLawSections56.Section5.NearEndToEnd

/-!
# Literal cell-error scale closure

The literal complex cell telescope currently has the symmetric error

`max (projective loss) (expected open pressure)`.

This file performs all deterministic asymptotic bookkeeping for such a maximum.  It
also records the centered version needed by the paper: once the second component is a
genuine error relative to the deterministic one-cell pressure, the two component scale
limits feed directly into `global_pressure_on_cell_multiples_varyingDegrees_eventually`,
`target_pressure_tendsto`, and `PressureLiftToTargetInputVarying`.

For the fresh-only literal theorem the second component is the raw expected pressure, not
its error from the Section 3 calibrated pressure.  Consequently its direct nonzero-target
application would require the generally false limit `expectedPressure / cellLength -> 0`.
The last lemma makes this centering obstruction explicit.  The sharper centered one-cell
comparison and random-outside telescope are now proved in
`LiteralCenteredMatrixCellAdapter` and `LiteralCenteredMesoscopicTelescope`; those are the
appropriate inputs for a nonzero target.  No scale arithmetic is hidden here.
-/

open Filter Topology

namespace CircularLawSections56.Section5

universe v

/-- The exact common error used by the literal telescope, or its centered analogue when
`openPressureTerm` is already the upper-pressure error from a deterministic center. -/
def literalCombinedCellError
    (projectiveLoss openPressureTerm : ℕ → ℝ) : ℕ → ℝ :=
  fun n => max (projectiveLoss n) (openPressureTerm n)

/-! ## Centered adapted-cell pressure lifting -/

/-- Per-cell average of a finite list of deterministic adapted exterior-family
pressures.  This is the correct center for the genuine FreshZ cumulative telescope. -/
noncomputable def adaptedAverageBasePressure
    (cellCount : ℕ) (base : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range cellCount, base j) / (cellCount : ℝ)

/-- Algebraic adapter from the centered cumulative estimate proved by
`complex_adaptedFreshCell_cumulative_telescope` (or its real analogue) to the exact
per-cell lifting inequality expected by the pressure-asymptotic receiver. -/
theorem centered_sum_bounds_to_average_pressure_lift
    (cellCount : ℕ) (hcellCount : 0 < cellCount)
    (base : ℕ → ℝ) (lifted error : ℝ)
    (hBounds :
      (∑ j ∈ Finset.range cellCount, base j) - (cellCount : ℝ) * error ≤ lifted ∧
      lifted ≤ (∑ j ∈ Finset.range cellCount, base j) +
        (cellCount : ℝ) * error) :
    (cellCount : ℝ) * (adaptedAverageBasePressure cellCount base - error) ≤ lifted ∧
      lifted ≤ (cellCount : ℝ) *
        (adaptedAverageBasePressure cellCount base + error) := by
  have hq : (cellCount : ℝ) ≠ 0 := by exact_mod_cast hcellCount.ne'
  have havg : (cellCount : ℝ) * adaptedAverageBasePressure cellCount base =
      ∑ j ∈ Finset.range cellCount, base j := by
    simp only [adaptedAverageBasePressure]
    field_simp
  constructor
  · rw [mul_sub, havg]
    exact hBounds.1
  · rw [mul_add, havg]
    exact hBounds.2

/-- The singleton degree family used to feed a scalar adapted FreshZ pressure into the
varying-degree receiver without inventing an unrelated matrix degree. -/
def scalarPressureDegrees (_ : ℕ) : Finset Unit := {()}

theorem scalarPressureDegrees_nonempty (n : ℕ) :
    (scalarPressureDegrees n).Nonempty := by
  exact ⟨(), by simp [scalarPressureDegrees]⟩

/-- Embed a scalar pressure sequence as the unique member of the singleton degree
family. -/
def scalarPressureFamily (pressure : ℕ → ℝ) : ℕ → Unit → ℝ :=
  fun n _ => pressure n

/-- Centered scalar FreshZ pressure bounds give the exact lifting part of
`PressureLiftToTargetInputVarying`.  In applications, `hLifting` is obtained pointwise
from `complex_adaptedFreshCell_cumulative_telescope` or
`real_adaptedFreshCell_cumulative_telescope`, followed by
`centered_sum_bounds_to_average_pressure_lift`. -/
theorem pressureLiftToTargetInputVarying_of_centered_scalar_fresh_cells
    (base lifted : ℕ → ℝ) (cellCount cellLength : ℕ → ℕ)
    (cellError wholeNormalizedPressure cellLengthRatio : ℕ → ℝ)
    (remainderError lengthRatioError : ℕ → ℝ)
    (hLifting : ∀ᶠ n in atTop,
      0 < cellCount n ∧ 0 < cellLength n ∧
        (cellCount n : ℝ) * (base n - cellError n) ≤ lifted n ∧
        lifted n ≤ (cellCount n : ℝ) * (base n + cellError n))
    (hCellErrorZero :
      Tendsto (fun n => cellError n / (cellLength n : ℝ)) atTop (𝓝 0))
    (hRatioNonneg : ∀ n, 0 ≤ cellLengthRatio n)
    (hRatioLeOne : ∀ n, cellLengthRatio n ≤ 1)
    (hRemainder : ∀ n,
      |wholeNormalizedPressure n - cellLengthRatio n *
        cellNormalizedPressureVarying scalarPressureDegrees
          scalarPressureDegrees_nonempty (scalarPressureFamily lifted)
          cellCount cellLength n| ≤ remainderError n)
    (hRemainderZero : Tendsto remainderError atTop (𝓝 0))
    (hLengthRatio : ∀ n, |cellLengthRatio n - 1| ≤ lengthRatioError n)
    (hLengthRatioZero : Tendsto lengthRatioError atTop (𝓝 0)) :
    PressureLiftToTargetInputVarying scalarPressureDegrees
      scalarPressureDegrees_nonempty (scalarPressureFamily base)
      (scalarPressureFamily lifted) cellCount cellLength cellError
      wholeNormalizedPressure cellLengthRatio remainderError lengthRatioError := by
  refine
    { lifting_eventually := ?_
      normalized_cell_error_zero := hCellErrorZero
      ratio_nonneg := hRatioNonneg
      ratio_le_one := hRatioLeOne
      remainder_bound := hRemainder
      remainder_zero := hRemainderZero
      ratio_bound := hLengthRatio
      ratio_error_zero := hLengthRatioZero }
  filter_upwards [hLifting] with n hn
  refine ⟨hn.1, hn.2.1, ?_⟩
  intro r hr
  rcases r with ⟨⟩
  simpa only [scalarPressureFamily] using hn.2.2

/-- Transparent scale contract for the two components of the literal maximum error.

For the theorem as currently instantiated, `openPressureTerm` is the raw expected open
pressure.  For the paper-centered application it should instead be the proved error of
that pressure from the deterministic Section 3 one-cell center. -/
structure LiteralCellScaleChoice
    (cellLength : ℕ → ℕ)
    (projectiveLoss openPressureTerm : ℕ → ℝ) : Prop where
  projectiveLoss_normalized_zero :
    Tendsto (fun n => projectiveLoss n / (cellLength n : ℝ)) atTop (𝓝 0)
  openPressureTerm_normalized_zero :
    Tendsto (fun n => openPressureTerm n / (cellLength n : ℝ)) atTop (𝓝 0)

/-- Choosing a cell length that dominates both error components makes their exact
maximum negligible.  This identity is valid even on a finite prefix where the natural
cell length is zero, because division in `ℝ` is totalized. -/
theorem literalCombinedCellError_normalized_tendsto_zero
    (cellLength : ℕ → ℕ)
    (projectiveLoss openPressureTerm : ℕ → ℝ)
    (hScale : LiteralCellScaleChoice cellLength projectiveLoss openPressureTerm) :
    Tendsto
      (fun n => literalCombinedCellError projectiveLoss openPressureTerm n /
        (cellLength n : ℝ)) atTop (𝓝 0) := by
  have hmax := hScale.projectiveLoss_normalized_zero.max
    hScale.openPressureTerm_normalized_zero
  have heq :
      (fun n => literalCombinedCellError projectiveLoss openPressureTerm n /
        (cellLength n : ℝ)) =
      (fun n => max (projectiveLoss n / (cellLength n : ℝ))
        (openPressureTerm n / (cellLength n : ℝ))) := by
    funext n
    exact (max_div_div_right (Nat.cast_nonneg (cellLength n))
      (projectiveLoss n) (openPressureTerm n)).symm
  rw [heq]
  simpa only [max_self] using hmax

/-- The strongest complete-cell asymptotic closure supplied by the current deterministic
spine.  The Section 3 known result enters only as `hBaseTarget`; it is not reproved.

When `openPressureTerm` is a centered upper-pressure error, this is the paper's pressure
asymptotic.  With the raw literal expected pressure it remains a mathematically valid,
but normally only zero-target, specialization. -/
theorem global_pressure_on_cell_multiples_of_literal_component_scales
    {ι : Type v}
    (degrees : ℕ → Finset ι) (hdegrees : ∀ n, (degrees n).Nonempty)
    (base lifted : ℕ → ι → ℝ) (cellCount cellLength : ℕ → ℕ)
    (projectiveLoss openPressureTerm : ℕ → ℝ)
    (target : ℝ)
    (hLifting : ∀ᶠ n in atTop,
      0 < cellCount n ∧ 0 < cellLength n ∧ ∀ r, r ∈ degrees n →
        (cellCount n : ℝ) *
            (base n r - literalCombinedCellError projectiveLoss openPressureTerm n) ≤
          lifted n r ∧
        lifted n r ≤ (cellCount n : ℝ) *
          (base n r + literalCombinedCellError projectiveLoss openPressureTerm n))
    (hScale : LiteralCellScaleChoice cellLength projectiveLoss openPressureTerm)
    (hBaseTarget : Tendsto
      (baseNormalizedPressureVarying degrees hdegrees base cellLength)
      atTop (𝓝 target)) :
    Tendsto
      (cellNormalizedPressureVarying degrees hdegrees lifted cellCount cellLength)
      atTop (𝓝 target) := by
  apply global_pressure_on_cell_multiples_varyingDegrees_eventually
    degrees hdegrees base lifted cellCount cellLength
      (literalCombinedCellError projectiveLoss openPressureTerm) target
      hLifting
      (literalCombinedCellError_normalized_tendsto_zero
        cellLength projectiveLoss openPressureTerm hScale)
  exact hBaseTarget

/-- Add the already-isolated balanced remainder and length-ratio estimates to the literal
component scales.  This yields the full deterministic target-pressure asymptotic consumed
by the final Section 4 seam/fluctuation receiver. -/
theorem target_pressure_tendsto_of_literal_component_scales
    {ι : Type v}
    (degrees : ℕ → Finset ι) (hdegrees : ∀ n, (degrees n).Nonempty)
    (base lifted : ℕ → ι → ℝ) (cellCount cellLength : ℕ → ℕ)
    (projectiveLoss openPressureTerm : ℕ → ℝ)
    (wholeNormalizedPressure cellLengthRatio : ℕ → ℝ)
    (remainderError lengthRatioError : ℕ → ℝ) (target : ℝ)
    (hLifting : ∀ᶠ n in atTop,
      0 < cellCount n ∧ 0 < cellLength n ∧ ∀ r, r ∈ degrees n →
        (cellCount n : ℝ) *
            (base n r - literalCombinedCellError projectiveLoss openPressureTerm n) ≤
          lifted n r ∧
        lifted n r ≤ (cellCount n : ℝ) *
          (base n r + literalCombinedCellError projectiveLoss openPressureTerm n))
    (hScale : LiteralCellScaleChoice cellLength projectiveLoss openPressureTerm)
    (hBaseTarget : Tendsto
      (baseNormalizedPressureVarying degrees hdegrees base cellLength)
      atTop (𝓝 target))
    (hRatioNonneg : ∀ n, 0 ≤ cellLengthRatio n)
    (hRatioLeOne : ∀ n, cellLengthRatio n ≤ 1)
    (hRemainder : ∀ n,
      |wholeNormalizedPressure n - cellLengthRatio n *
        cellNormalizedPressureVarying degrees hdegrees lifted
          cellCount cellLength n| ≤ remainderError n)
    (hLengthRatio : ∀ n, |cellLengthRatio n - 1| ≤ lengthRatioError n)
    (hRemainderZero : Tendsto remainderError atTop (𝓝 0))
    (hLengthRatioZero : Tendsto lengthRatioError atTop (𝓝 0)) :
    Tendsto wholeNormalizedPressure atTop (𝓝 target) := by
  have hCellTarget :=
    global_pressure_on_cell_multiples_of_literal_component_scales
      degrees hdegrees base lifted cellCount cellLength projectiveLoss
      openPressureTerm target hLifting hScale hBaseTarget
  have hCellErrorZero : Tendsto
      (fun n => |cellNormalizedPressureVarying degrees hdegrees lifted
        cellCount cellLength n - target|) atTop (𝓝 0) := by
    have hSub := hCellTarget.sub_const target
    simpa using hSub.abs
  apply target_pressure_tendsto wholeNormalizedPressure
    (cellNormalizedPressureVarying degrees hdegrees lifted cellCount cellLength)
    cellLengthRatio target remainderError
    (fun n => |cellNormalizedPressureVarying degrees hdegrees lifted
      cellCount cellLength n - target|) lengthRatioError
    hRatioNonneg hRatioLeOne hRemainder (fun _ => le_rfl) hLengthRatio
    hRemainderZero hCellErrorZero hLengthRatioZero

/-- Constructor for the exact receiver used by `NearEndToEnd`.  All scale bookkeeping
for the maximum error is discharged here; only the centered finite-cell lift and the
separately proved balanced-remainder inputs remain. -/
theorem pressureLiftToTargetInputVarying_of_literal_component_scales
    {ι : Type v}
    (degrees : ℕ → Finset ι) (hdegrees : ∀ n, (degrees n).Nonempty)
    (base lifted : ℕ → ι → ℝ) (cellCount cellLength : ℕ → ℕ)
    (projectiveLoss openPressureTerm : ℕ → ℝ)
    (wholeNormalizedPressure cellLengthRatio : ℕ → ℝ)
    (remainderError lengthRatioError : ℕ → ℝ)
    (hLifting : ∀ᶠ n in atTop,
      0 < cellCount n ∧ 0 < cellLength n ∧ ∀ r, r ∈ degrees n →
        (cellCount n : ℝ) *
            (base n r - literalCombinedCellError projectiveLoss openPressureTerm n) ≤
          lifted n r ∧
        lifted n r ≤ (cellCount n : ℝ) *
          (base n r + literalCombinedCellError projectiveLoss openPressureTerm n))
    (hScale : LiteralCellScaleChoice cellLength projectiveLoss openPressureTerm)
    (hRatioNonneg : ∀ n, 0 ≤ cellLengthRatio n)
    (hRatioLeOne : ∀ n, cellLengthRatio n ≤ 1)
    (hRemainder : ∀ n,
      |wholeNormalizedPressure n - cellLengthRatio n *
        cellNormalizedPressureVarying degrees hdegrees lifted
          cellCount cellLength n| ≤ remainderError n)
    (hRemainderZero : Tendsto remainderError atTop (𝓝 0))
    (hLengthRatio : ∀ n, |cellLengthRatio n - 1| ≤ lengthRatioError n)
    (hLengthRatioZero : Tendsto lengthRatioError atTop (𝓝 0)) :
    PressureLiftToTargetInputVarying degrees hdegrees base lifted
      cellCount cellLength
      (literalCombinedCellError projectiveLoss openPressureTerm)
      wholeNormalizedPressure cellLengthRatio remainderError lengthRatioError := by
  exact
    { lifting_eventually := hLifting
      normalized_cell_error_zero :=
        literalCombinedCellError_normalized_tendsto_zero
          cellLength projectiveLoss openPressureTerm hScale
      ratio_nonneg := hRatioNonneg
      ratio_le_one := hRatioLeOne
      remainder_bound := hRemainder
      remainder_zero := hRemainderZero
      ratio_bound := hLengthRatio
      ratio_error_zero := hLengthRatioZero }

/-! ## The manuscript's concrete mesoscopic scales -/

/-- The manuscript choice `m₀(W) = ⌈W^(1+δ)⌉`. -/
noncomputable def paperMesoscopicCellLength
    (δ : ℝ) (W : ℕ → ℕ) (n : ℕ) : ℕ :=
  ⌈(W n : ℝ) ^ (1 + δ)⌉₊

/-- The logarithm `log(e W)` appearing in the cell, seam, and remainder estimates. -/
noncomputable def paperLogEW (W : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.log (Real.exp 1 * (W n : ℝ))

/-- The unnormalized one-cell scale `W log(e W)`. -/
noncomputable def paperCellErrorScale (W : ℕ → ℕ) (n : ℕ) : ℝ :=
  (W n : ℝ) * paperLogEW W n

/-- The final long-branch seam rate from the manuscript:
`W log(eW) / N + sqrt(W/N) log(eW)`. -/
noncomputable def paperFinalSeamRate
    (W N : ℕ → ℕ) (n : ℕ) : ℝ :=
  paperCellErrorScale W n / (N n : ℝ) +
    Real.sqrt ((W n : ℝ) / (N n : ℝ)) * paperLogEW W n

/-- The balanced incomplete-cell remainder rate `log(eW) / m₀(W)`. -/
noncomputable def paperBalancedRemainderRate
    (δ : ℝ) (W : ℕ → ℕ) (n : ℕ) : ℝ :=
  paperLogEW W n / (paperMesoscopicCellLength δ W n : ℝ)

/-- Exact concrete scale contract used by the manuscript's long branch.

The functions are fixed above, not abstract placeholders.  The three limit fields are
the purely real-asymptotic facts still required of the ambient `W,N` chooser; they can
be discharged independently of the matrix probability argument. -/
structure PaperMesoscopicScaleChoice
    (δ γ : ℝ) (W N : ℕ → ℕ) : Prop where
  delta_pos : 0 < δ
  delta_lt_gamma : δ < γ
  gamma_lt_one_eighth : γ < 1 / 8
  bandwidth_tendsto : Tendsto W atTop atTop
  long_branch : ∀ᶠ n in atTop, (W n : ℝ) ^ (1 + γ) < (N n : ℝ)
  cell_error_rate_zero :
    Tendsto
      (fun n => paperCellErrorScale W n /
        (paperMesoscopicCellLength δ W n : ℝ)) atTop (𝓝 0)
  final_seam_rate_zero : Tendsto (paperFinalSeamRate W N) atTop (𝓝 0)
  balanced_remainder_rate_zero :
    Tendsto (paperBalancedRemainderRate δ W) atTop (𝓝 0)

/-- Any nonnegative centered cell error bounded by `C W log(eW)` is negligible after
the manuscript normalization `m₀(W)=⌈W^(1+δ)⌉`. -/
theorem centered_cell_error_normalized_zero_of_paper_bound
    (δ γ : ℝ) (W N : ℕ → ℕ)
    (hScale : PaperMesoscopicScaleChoice δ γ W N)
    (error : ℕ → ℝ) (C : ℝ)
    (hErrorNonneg : ∀ᶠ n in atTop, 0 ≤ error n)
    (hErrorBound : ∀ᶠ n in atTop,
      error n ≤ C * paperCellErrorScale W n) :
    Tendsto
      (fun n => error n / (paperMesoscopicCellLength δ W n : ℝ))
      atTop (𝓝 0) := by
  have hUpper : Tendsto
      (fun n => C * (paperCellErrorScale W n /
        (paperMesoscopicCellLength δ W n : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hScale.cell_error_rate_zero)
  apply squeeze_zero'
  · filter_upwards [hErrorNonneg] with n hn
    exact div_nonneg hn (Nat.cast_nonneg _)
  · filter_upwards [hErrorBound] with n hn
    calc
      error n / (paperMesoscopicCellLength δ W n : ℝ) ≤
          (C * paperCellErrorScale W n) /
            (paperMesoscopicCellLength δ W n : ℝ) :=
        div_le_div_of_nonneg_right hn (Nat.cast_nonneg _)
      _ = C * (paperCellErrorScale W n /
            (paperMesoscopicCellLength δ W n : ℝ)) := by ring
  · exact hUpper

/-- Concrete complex FreshZ specialization.  The only quantitative model input is the
paper estimate `complexIidFreshCellError ≤ C W log(eW)`; nonnegativity follows from the
already-proved Section 4 component bounds. -/
theorem complexIidFreshCellError_normalized_zero_of_paper_bound
    (δ γ : ℝ) (W N d : ℕ → ℕ) (c0 L : ℕ → ℝ) (z : ℕ → ℂ)
    (hScale : PaperMesoscopicScaleChoice δ γ W N)
    (hc0 : ∀ n, 0 < c0 n)
    (hsqrt : ∀ n, Real.sqrt (c0 n / (d n + 2 : ℝ)) ≤ 1)
    (C : ℝ)
    (hErrorBound : ∀ᶠ n in atTop,
      complexIidFreshCellError (d n) (c0 n) (L n) (z n) ≤
        C * paperCellErrorScale W n) :
    Tendsto
      (fun n => complexIidFreshCellError (d n) (c0 n) (L n) (z n) /
        (paperMesoscopicCellLength δ W n : ℝ)) atTop (𝓝 0) := by
  apply centered_cell_error_normalized_zero_of_paper_bound
    δ γ W N hScale _ C
  · filter_upwards with n
    exact add_nonneg
      (add_nonneg
        (CircularLawSection4.PaperIndicatorWeights.paperIsolatedCoefficientLoss_nonneg
          (hc0 n) (hsqrt n))
        (CircularLawSection4.PaperIndicatorWeights.complexFreshNegativeBound_nonneg
          (d n) (L n)))
      (CircularLawSection4.PaperIndicatorWeights.paperFreshPositiveBound_nonneg
        (d n) (z n))
  · exact hErrorBound

/-- Real-law counterpart of
`complexIidFreshCellError_normalized_zero_of_paper_bound`. -/
theorem realIidFreshCellError_normalized_zero_of_paper_bound
    (δ γ : ℝ) (W N d : ℕ → ℕ) (c0 L : ℕ → ℝ) (z : ℕ → ℂ)
    (hScale : PaperMesoscopicScaleChoice δ γ W N)
    (hc0 : ∀ n, 0 < c0 n)
    (hsqrt : ∀ n, Real.sqrt (c0 n / (d n + 2 : ℝ)) ≤ 1)
    (C : ℝ)
    (hErrorBound : ∀ᶠ n in atTop,
      realIidFreshCellError (d n) (c0 n) (L n) (z n) ≤
        C * paperCellErrorScale W n) :
    Tendsto
      (fun n => realIidFreshCellError (d n) (c0 n) (L n) (z n) /
        (paperMesoscopicCellLength δ W n : ℝ)) atTop (𝓝 0) := by
  apply centered_cell_error_normalized_zero_of_paper_bound
    δ γ W N hScale _ C
  · filter_upwards with n
    exact add_nonneg
      (add_nonneg
        (CircularLawSection4.PaperIndicatorWeights.paperIsolatedCoefficientLoss_nonneg
          (hc0 n) (hsqrt n))
        (CircularLawSection4.PaperIndicatorWeights.realFreshNegativeBound_nonneg
          (d n) (L n)))
      (CircularLawSection4.PaperIndicatorWeights.paperFreshPositiveBound_nonneg
        (d n) (z n))
  · exact hErrorBound

/-- The manuscript scale chooser simultaneously discharges the exact final seam and
balanced-remainder limits consumed by the target-pressure and near-end-to-end receivers. -/
theorem paperMesoscopicScaleChoice_receiver_rates
    (δ γ : ℝ) (W N : ℕ → ℕ)
    (hScale : PaperMesoscopicScaleChoice δ γ W N) :
    Tendsto (paperFinalSeamRate W N) atTop (𝓝 0) ∧
      Tendsto (paperBalancedRemainderRate δ W) atTop (𝓝 0) :=
  ⟨hScale.final_seam_rate_zero, hScale.balanced_remainder_rate_zero⟩

/-- Exact obstruction to using an error centered at zero for a nonzero deterministic
pressure target.  If a vanishing normalized error dominates the absolute normalized base
pressure, then the Section 3 target forced by that base is zero. -/
theorem target_eq_zero_of_zero_centered_error
    (baseNormalized errorNormalized : ℕ → ℝ) (target : ℝ)
    (hBaseTarget : Tendsto baseNormalized atTop (𝓝 target))
    (hDom : ∀ᶠ n in atTop, |baseNormalized n| ≤ errorNormalized n)
    (hErrorZero : Tendsto errorNormalized atTop (𝓝 0)) :
    target = 0 := by
  have hAbsZero : Tendsto (fun n => |baseNormalized n|) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n => abs_nonneg (baseNormalized n)
    · exact hDom
    · exact hErrorZero
  have hBaseZero : Tendsto baseNormalized atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.2 (by
      simpa [Real.dist_eq] using hAbsZero)
  exact tendsto_nhds_unique hBaseTarget hBaseZero

end CircularLawSections56.Section5
