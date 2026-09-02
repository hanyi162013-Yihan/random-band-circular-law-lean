import CircularLawSection4.MultiaffineUntruncated
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# The analytic closing step for one fresh block

The fresh-closure argument has two one-sided inputs.  The isolated
multiaffine coefficient controls the logarithmic deficit, while the trace
and row-norm estimates control the logarithmic excess.  This file proves
the exact deterministic decomposition and combines the two integrable
parts.  It also records the change-of-scale loss needed when the isolated
coefficient is only comparable with the exterior-family scale.
-/

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace CircularLawSection4

/-- Positive logarithmic deficit of `radius` below `scale`. -/
noncomputable def logDeficit (scale radius : ℝ) : ℝ :=
  max 0 (Real.log scale - Real.log radius)

theorem logDeficit_eq_positiveLogLoss (scale radius : ℝ) :
    logDeficit scale radius = positiveLogLoss scale radius := rfl

/-- Positive logarithmic excess of `radius` above `scale`. -/
noncomputable def logExcess (scale radius : ℝ) : ℝ :=
  max 0 (Real.log radius - Real.log scale)

theorem logDeficit_nonneg (scale radius : ℝ) :
    0 ≤ logDeficit scale radius :=
  le_max_left _ _

theorem logExcess_nonneg (scale radius : ℝ) :
    0 ≤ logExcess scale radius :=
  le_max_left _ _

/-- The absolute logarithmic deviation is exactly the sum of its two
one-sided parts. -/
theorem abs_log_sub_log_eq_logDeficit_add_logExcess
    (scale radius : ℝ) :
    |Real.log radius - Real.log scale| =
      logDeficit scale radius + logExcess scale radius := by
  by_cases h : Real.log scale ≤ Real.log radius
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    simp only [logDeficit, logExcess,
      max_eq_left (sub_nonpos.mpr h), max_eq_right (sub_nonneg.mpr h),
      zero_add]
  · have h' : Real.log radius ≤ Real.log scale := le_of_not_ge h
    rw [abs_of_nonpos (sub_nonpos.mpr h')]
    simp only [logDeficit, logExcess,
      max_eq_right (sub_nonneg.mpr h'), max_eq_left (sub_nonpos.mpr h'),
      add_zero]
    ring

theorem measurable_logDeficit
    {Ω : Type*} [MeasurableSpace Ω] (scale : ℝ)
    {radius : Ω → ℝ} (hradius : Measurable radius) :
    Measurable (fun ω => logDeficit scale (radius ω)) := by
  unfold logDeficit
  fun_prop

theorem measurable_logExcess
    {Ω : Type*} [MeasurableSpace Ω] (scale : ℝ)
    {radius : Ω → ℝ} (hradius : Measurable radius) :
    Measurable (fun ω => logExcess scale (radius ω)) := by
  unfold logExcess
  fun_prop

/-- Replacing the coefficient scale by a larger reference scale costs only
the logarithmic scale gap. -/
theorem logDeficit_le_scaleLoss_add
    {coefficient scale radius loss : ℝ} (hloss : 0 ≤ loss)
    (hscale : Real.log scale - Real.log coefficient ≤ loss) :
    logDeficit scale radius ≤
      loss + logDeficit coefficient radius := by
  unfold logDeficit
  apply max_le
  · exact add_nonneg hloss (le_max_left _ _)
  · calc
      Real.log scale - Real.log radius =
          (Real.log scale - Real.log coefficient) +
            (Real.log coefficient - Real.log radius) := by ring
      _ ≤ loss + max 0 (Real.log coefficient - Real.log radius) :=
        add_le_add hscale (le_max_right _ _)

/-- A multiplicative coefficient comparison gives the logarithmic scale
loss used by fresh closure. -/
theorem log_scale_sub_log_coefficient_le_of_exp_loss
    {coefficient scale loss : ℝ} (hscale : 0 < scale)
    (hcoefficient : scale * Real.exp (-loss) ≤ coefficient) :
    Real.log scale - Real.log coefficient ≤ loss := by
  have hfloor : 0 < scale * Real.exp (-loss) :=
    mul_pos hscale (Real.exp_pos _)
  have hlog :
      Real.log (scale * Real.exp (-loss)) ≤ Real.log coefficient :=
    Real.log_le_log hfloor hcoefficient
  rw [Real.log_mul hscale.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  linarith

/-- The form produced directly by an isolated word: if its coefficient is
at least `bmin ^ d * scale`, then changing back to `scale` costs at most
`-d * log bmin`. -/
theorem log_scale_sub_log_coefficient_le_of_power_lower_bound
    {coefficient scale bmin : ℝ} {d : ℕ}
    (hscale : 0 < scale) (hbmin : 0 < bmin)
    (hcoefficient : bmin ^ d * scale ≤ coefficient) :
    Real.log scale - Real.log coefficient ≤
      -(d : ℝ) * Real.log bmin := by
  have hproduct : 0 < bmin ^ d * scale :=
    mul_pos (pow_pos hbmin _) hscale
  have hlog :
      Real.log (bmin ^ d * scale) ≤ Real.log coefficient :=
    Real.log_le_log hproduct hcoefficient
  rw [Real.log_mul (pow_ne_zero d hbmin.ne') hscale.ne',
    Real.log_pow] at hlog
  linarith

/-- Integrability of the two one-sided logarithmic parts is equivalent to
an integrable absolute logarithmic deviation in the direction needed by
fresh closure. -/
theorem integrable_abs_log_sub_log_of_parts
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (scale : ℝ) {radius : Ω → ℝ}
    (hdeficit : Integrable (fun ω => logDeficit scale (radius ω)) μ)
    (hexcess : Integrable (fun ω => logExcess scale (radius ω)) μ) :
    Integrable (fun ω => |Real.log (radius ω) - Real.log scale|) μ := by
  have hadd := hdeficit.add hexcess
  apply hadd.congr
  filter_upwards with ω
  exact (abs_log_sub_log_eq_logDeficit_add_logExcess scale (radius ω)).symm

/-- Direct two-sided `L¹` closure from bounds on the negative and positive
logarithmic parts. -/
theorem freshClosure_L1_of_logParts
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (scale : ℝ) {radius : Ω → ℝ}
    (hdeficit : Integrable (fun ω => logDeficit scale (radius ω)) μ)
    (hexcess : Integrable (fun ω => logExcess scale (radius ω)) μ)
    {negativeBound positiveBound : ℝ}
    (hnegative :
      ∫ ω, logDeficit scale (radius ω) ∂μ ≤ negativeBound)
    (hpositive :
      ∫ ω, logExcess scale (radius ω) ∂μ ≤ positiveBound) :
    Integrable (fun ω => |Real.log (radius ω) - Real.log scale|) μ ∧
      ∫ ω, |Real.log (radius ω) - Real.log scale| ∂μ ≤
        negativeBound + positiveBound := by
  refine ⟨integrable_abs_log_sub_log_of_parts scale hdeficit hexcess, ?_⟩
  have heq :
      (fun ω => |Real.log (radius ω) - Real.log scale|) =
        (fun ω => logDeficit scale (radius ω) +
          logExcess scale (radius ω)) := by
    funext ω
    exact abs_log_sub_log_eq_logDeficit_add_logExcess scale (radius ω)
  rw [heq, integral_add hdeficit hexcess]
  exact add_le_add hnegative hpositive

/-- Fresh closure with the isolated coefficient at a possibly smaller
scale.  This is the exact analytic assembly used in the manuscript: the
negative estimate is made at `coefficient`, the positive estimate at
`scale`, and `loss` accounts for their deterministic logarithmic gap. -/
theorem freshClosure_L1_of_isolatedCoefficient
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (coefficient scale loss : ℝ) {radius : Ω → ℝ}
    (hradius : Measurable radius) (hloss : 0 ≤ loss)
    (hscale : Real.log scale - Real.log coefficient ≤ loss)
    (hcoefficientDeficit :
      Integrable (fun ω => logDeficit coefficient (radius ω)) μ)
    (hscaleExcess :
      Integrable (fun ω => logExcess scale (radius ω)) μ)
    {negativeBound positiveBound : ℝ}
    (hnegative :
      ∫ ω, logDeficit coefficient (radius ω) ∂μ ≤ negativeBound)
    (hpositive :
      ∫ ω, logExcess scale (radius ω) ∂μ ≤ positiveBound) :
    Integrable (fun ω => |Real.log (radius ω) - Real.log scale|) μ ∧
      ∫ ω, |Real.log (radius ω) - Real.log scale| ∂μ ≤
        loss + negativeBound + positiveBound := by
  let deficitScale : Ω → ℝ := fun ω => logDeficit scale (radius ω)
  let deficitCoeff : Ω → ℝ := fun ω => logDeficit coefficient (radius ω)
  let majorant : Ω → ℝ := fun ω => loss + deficitCoeff ω
  have hmajorant : Integrable majorant μ :=
    (integrable_const loss).add hcoefficientDeficit
  have hpoint : ∀ ω, deficitScale ω ≤ majorant ω := fun ω =>
    logDeficit_le_scaleLoss_add hloss hscale
  have hdeficitScale : Integrable deficitScale μ := by
    apply hmajorant.mono' (measurable_logDeficit scale hradius).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs,
      abs_of_nonneg (logDeficit_nonneg scale (radius ω))]
    exact hpoint ω
  have hscaleNegative :
      ∫ ω, deficitScale ω ∂μ ≤ loss + negativeBound := by
    calc
      (∫ ω, deficitScale ω ∂μ) ≤ ∫ ω, majorant ω ∂μ :=
        integral_mono hdeficitScale hmajorant hpoint
      _ = loss + ∫ ω, deficitCoeff ω ∂μ := by
        calc
          (∫ ω, majorant ω ∂μ) =
              (∫ ω, (fun _ : Ω => loss) ω + deficitCoeff ω ∂μ) := rfl
          _ = (∫ _ : Ω, loss ∂μ) + ∫ ω, deficitCoeff ω ∂μ :=
            integral_add (integrable_const loss) hcoefficientDeficit
          _ = loss + ∫ ω, deficitCoeff ω ∂μ := by simp
      _ ≤ loss + negativeBound := by linarith
  simpa only [deficitScale] using
    freshClosure_L1_of_logParts scale hdeficitScale hscaleExcess
      hscaleNegative hpositive

/-- End-to-end negative-half assembly: a power small-ball estimate at the
isolated coefficient scale, a deterministic logarithmic comparison with the
reference scale, and the positive-half integrability input imply the full
fresh-closure `L¹` estimate. -/
theorem freshClosure_L1_of_powerSmallBall_and_excess
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (radius : Ω → ℝ) (hradius : Measurable radius)
    (hradius0 : ∀ ω, 0 ≤ radius ω)
    (coefficient scale loss A : ℝ) (hcoefficient : 0 < coefficient)
    (hloss : 0 ≤ loss)
    (hscale : Real.log scale - Real.log coefficient ≤ loss)
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (hsmall : ∀ ρ : ℝ, 0 < ρ →
      μ {ω | radius ω ≤ coefficient * ρ ^ d} ≤
        ENNReal.ofReal (A * ρ ^ m))
    (hexcess : Integrable (fun ω => logExcess scale (radius ω)) μ)
    {positiveBound : ℝ}
    (hpositive : ∫ ω, logExcess scale (radius ω) ∂μ ≤ positiveBound) :
    μ {ω | radius ω = 0} = 0 ∧
      Integrable (fun ω => |Real.log (radius ω) - Real.log scale|) μ ∧
      ∫ ω, |Real.log (radius ω) - Real.log scale| ∂μ ≤
        loss +
          (Real.log (max 1 A) + 1) / ((m : ℝ) / (d : ℝ)) +
          positiveBound := by
  obtain ⟨hzero, _hae, hnegativeInt, hnegative⟩ :=
    zeroSet_aeLog_and_integrable_positiveLogLoss_of_power_smallBall
      μ radius hradius hradius0 coefficient A hcoefficient d m hd hm hsmall
  have hnegativeInt' :
      Integrable (fun ω => logDeficit coefficient (radius ω)) μ := by
    simpa only [logDeficit_eq_positiveLogLoss] using hnegativeInt
  refine ⟨hzero, ?_⟩
  exact freshClosure_L1_of_isolatedCoefficient μ coefficient scale loss
    hradius hloss hscale hnegativeInt' hexcess hnegative hpositive

end CircularLawSection4
