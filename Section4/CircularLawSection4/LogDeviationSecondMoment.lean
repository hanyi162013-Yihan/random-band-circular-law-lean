import CircularLawSection4.FreshClosure
import CircularLawSection4.ExponentialTailSecondMoment
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Two-sided logarithmic tails imply an `L²` log deviation

This is the analytic closing step in the operator-valued affine logarithm
lemma.  The small-ball argument controls `logDeficit`; a deterministic norm
bound plus a moment estimate controls `logExcess`.  Separate exponential
tails for those nonnegative parts are combined here into square
integrability of the full logarithmic deviation.
-/

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace CircularLawSection4

/-- Explicit bound supplied by the one-sided exponential-tail lemma. -/
noncomputable def oneSidedLogSecondMomentBound (A q : ℝ) : ℝ :=
  4 * ((Real.log (max 1 A) + 1) / q) ^ 2

/-- Generic `L²` assembly from the two one-sided logarithmic parts. -/
theorem memLp_two_and_integral_sq_abs_log_sub_log_of_parts
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (scale : ℝ) {radius : Ω → ℝ}
    (hdeficit : MemLp (fun ω => logDeficit scale (radius ω)) 2 μ)
    (hexcess : MemLp (fun ω => logExcess scale (radius ω)) 2 μ)
    {negativeBound positiveBound : ℝ}
    (hnegative :
      ∫ ω, logDeficit scale (radius ω) ^ 2 ∂μ ≤ negativeBound)
    (hpositive :
      ∫ ω, logExcess scale (radius ω) ^ 2 ∂μ ≤ positiveBound) :
    MemLp (fun ω => |Real.log (radius ω) - Real.log scale|) 2 μ ∧
      ∫ ω, |Real.log (radius ω) - Real.log scale| ^ 2 ∂μ ≤
        2 * negativeBound + 2 * positiveBound := by
  let D : Ω → ℝ := fun ω => logDeficit scale (radius ω)
  let E : Ω → ℝ := fun ω => logExcess scale (radius ω)
  let Z : Ω → ℝ := fun ω => |Real.log (radius ω) - Real.log scale|
  have hsum : MemLp (D + E) 2 μ := hdeficit.add hexcess
  have hZ : MemLp Z 2 μ := by
    apply hsum.ae_eq
    filter_upwards with ω
    exact (abs_log_sub_log_eq_logDeficit_add_logExcess
      scale (radius ω)).symm
  refine ⟨hZ, ?_⟩
  have hZsqInt : Integrable (fun ω => Z ω ^ 2) μ := hZ.integrable_sq
  have hDsqInt : Integrable (fun ω => D ω ^ 2) μ := hdeficit.integrable_sq
  have hEsqInt : Integrable (fun ω => E ω ^ 2) μ := hexcess.integrable_sq
  have hdomInt : Integrable (fun ω => 2 * D ω ^ 2 + 2 * E ω ^ 2) μ :=
    (hDsqInt.const_mul 2).add (hEsqInt.const_mul 2)
  have hpoint : ∀ ω, Z ω ^ 2 ≤ 2 * D ω ^ 2 + 2 * E ω ^ 2 := by
    intro ω
    have hZE : Z ω = D ω + E ω :=
      abs_log_sub_log_eq_logDeficit_add_logExcess scale (radius ω)
    rw [hZE]
    nlinarith [sq_nonneg (D ω - E ω)]
  calc
    (∫ ω, Z ω ^ 2 ∂μ) ≤
        ∫ ω, (2 * D ω ^ 2 + 2 * E ω ^ 2) ∂μ :=
      integral_mono hZsqInt hdomInt hpoint
    _ = 2 * ∫ ω, D ω ^ 2 ∂μ + 2 * ∫ ω, E ω ^ 2 ∂μ := by
      rw [integral_add (hDsqInt.const_mul 2) (hEsqInt.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 2 * negativeBound + 2 * positiveBound := by
      gcongr

/-- Two exponential tails, one below and one above the reference scale,
give the full squared logarithmic deviation bound. -/
theorem memLp_two_and_integral_sq_abs_log_sub_log_of_two_tails
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (scale : ℝ) {radius : Ω → ℝ} (hradius : Measurable radius)
    (Aneg qneg Apos qpos : ℝ)
    (hAneg : 0 ≤ Aneg) (hqneg : 0 < qneg)
    (hApos : 0 ≤ Apos) (hqpos : 0 < qpos)
    (hnegativeTail : ∀ t : ℝ, 0 < t →
      μ {ω | t < logDeficit scale (radius ω)} ≤
        ENNReal.ofReal (Aneg * Real.exp (-(qneg * t))))
    (hpositiveTail : ∀ t : ℝ, 0 < t →
      μ {ω | t < logExcess scale (radius ω)} ≤
        ENNReal.ofReal (Apos * Real.exp (-(qpos * t)))) :
    MemLp (fun ω => |Real.log (radius ω) - Real.log scale|) 2 μ ∧
      ∫ ω, |Real.log (radius ω) - Real.log scale| ^ 2 ∂μ ≤
        2 * oneSidedLogSecondMomentBound Aneg qneg +
          2 * oneSidedLogSecondMomentBound Apos qpos := by
  let D : Ω → ℝ := fun ω => logDeficit scale (radius ω)
  let E : Ω → ℝ := fun ω => logExcess scale (radius ω)
  let Z : Ω → ℝ := fun ω => |Real.log (radius ω) - Real.log scale|
  have hDmeas : Measurable D := measurable_logDeficit scale hradius
  have hEmeas : Measurable E := measurable_logExcess scale hradius
  obtain ⟨hDL2, hDsq⟩ :=
    memLp_two_and_integral_sq_le_of_exponential_tail
      μ D hDmeas (fun ω => logDeficit_nonneg scale (radius ω))
      Aneg qneg hAneg hqneg hnegativeTail
  obtain ⟨hEL2, hEsq⟩ :=
    memLp_two_and_integral_sq_le_of_exponential_tail
      μ E hEmeas (fun ω => logExcess_nonneg scale (radius ω))
      Apos qpos hApos hqpos hpositiveTail
  have hsumL2 : MemLp (D + E) 2 μ := hDL2.add hEL2
  have hZL2 : MemLp Z 2 μ := by
    apply hsumL2.ae_eq
    filter_upwards with ω
    exact (abs_log_sub_log_eq_logDeficit_add_logExcess
      scale (radius ω)).symm
  refine ⟨hZL2, ?_⟩
  have hZsqInt : Integrable (fun ω => Z ω ^ 2) μ := hZL2.integrable_sq
  have hDsqInt : Integrable (fun ω => D ω ^ 2) μ := hDL2.integrable_sq
  have hEsqInt : Integrable (fun ω => E ω ^ 2) μ := hEL2.integrable_sq
  have hdomInt :
      Integrable (fun ω => 2 * D ω ^ 2 + 2 * E ω ^ 2) μ :=
    (hDsqInt.const_mul 2).add (hEsqInt.const_mul 2)
  have hpoint : ∀ ω, Z ω ^ 2 ≤ 2 * D ω ^ 2 + 2 * E ω ^ 2 := by
    intro ω
    have hZE : Z ω = D ω + E ω :=
      abs_log_sub_log_eq_logDeficit_add_logExcess scale (radius ω)
    rw [hZE]
    nlinarith [sq_nonneg (D ω - E ω)]
  calc
    (∫ ω, Z ω ^ 2 ∂μ) ≤
        ∫ ω, (2 * D ω ^ 2 + 2 * E ω ^ 2) ∂μ :=
      integral_mono hZsqInt hdomInt hpoint
    _ = 2 * ∫ ω, D ω ^ 2 ∂μ + 2 * ∫ ω, E ω ^ 2 ∂μ := by
      rw [integral_add (hDsqInt.const_mul 2) (hEsqInt.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 2 * oneSidedLogSecondMomentBound Aneg qneg +
          2 * oneSidedLogSecondMomentBound Apos qpos := by
      apply add_le_add
      · gcongr
        simpa only [oneSidedLogSecondMomentBound] using hDsq
      · gcongr
        simpa only [oneSidedLogSecondMomentBound] using hEsq

end CircularLawSection4
