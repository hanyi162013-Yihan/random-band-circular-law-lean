import CircularLawSection4.LogDeviationSecondMoment

/-!
# Linear small balls give the negative-log `L²` half

A small-ball estimate at the reference scale turns the logarithmic deficit
into a random variable with an exponential upper tail.  This module records
that conversion, including nullity of the zero set and the explicit
second-moment constant used by the two-sided logarithmic closure.

The threshold-factor version is arranged for the operator-affine argument:
if scalarization only reaches `theta * scale`, changing back to `scale`
replaces the linear small-ball prefactor `C` by exactly `C / theta`.
-/

open scoped ENNReal MeasureTheory
open Set MeasureTheory

namespace CircularLawSection4

/-- A linear small-ball bound at `scale` rules out a zero atom and puts the
logarithmic deficit in `L²`. -/
theorem zeroSet_memLp_two_and_integral_sq_logDeficit_of_linearSmallBall
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (radius : Ω → ℝ) (hradius : Measurable radius)
    (hradius0 : ∀ ω, 0 ≤ radius ω)
    (scale A : ℝ) (hscale : 0 < scale) (hA : 0 ≤ A)
    (hsmall : ∀ ρ : ℝ, 0 < ρ →
      μ {ω | radius ω ≤ scale * ρ} ≤ ENNReal.ofReal (A * ρ)) :
    μ {ω | radius ω = 0} = 0 ∧
      MemLp (fun ω => logDeficit scale (radius ω)) 2 μ ∧
      ∫ ω, logDeficit scale (radius ω) ^ 2 ∂μ ≤
        oneSidedLogSecondMomentBound A 1 := by
  have hzero : μ {ω | radius ω = 0} = 0 := by
    apply measure_zeroSet_eq_zero_of_power_smallBall
      μ radius scale A hscale 1 1 Nat.one_pos
    intro ρ hρ
    simpa only [pow_one] using hsmall ρ hρ
  have htail : ∀ t : ℝ, 0 < t →
      μ {ω | t < logDeficit scale (radius ω)} ≤
        ENNReal.ofReal (A * Real.exp (-(1 * t))) := by
    intro t ht
    have hsubset :
        {ω | t < logDeficit scale (radius ω)} ⊆
          {ω | radius ω ≤ scale * Real.exp (-t)} := by
      intro ω hω
      apply positiveLogLoss_tail_imp_radius_le hscale (hradius0 ω) ht
      simpa only [Set.mem_ofPred_eq, logDeficit_eq_positiveLogLoss] using hω
    calc
      μ {ω | t < logDeficit scale (radius ω)} ≤
          μ {ω | radius ω ≤ scale * Real.exp (-t)} :=
        measure_mono hsubset
      _ ≤ ENNReal.ofReal (A * Real.exp (-t)) :=
        hsmall (Real.exp (-t)) (Real.exp_pos _)
      _ = ENNReal.ofReal (A * Real.exp (-(1 * t))) := by ring_nf
  obtain ⟨hL2, hsquare⟩ :=
    memLp_two_and_integral_sq_le_of_exponential_tail
      μ (fun ω => logDeficit scale (radius ω))
      (measurable_logDeficit scale hradius)
      (fun ω => logDeficit_nonneg scale (radius ω))
      A 1 hA zero_lt_one htail
  refine ⟨hzero, hL2, ?_⟩
  simpa only [oneSidedLogSecondMomentBound] using hsquare

/-- Threshold-factor form.  A linear small-ball estimate at
`theta * scale` gives the logarithmic deficit relative to `scale`, with
prefactor `C / theta`. -/
theorem zeroSet_memLp_two_and_integral_sq_logDeficit_of_threshold_linearSmallBall
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (radius : Ω → ℝ) (hradius : Measurable radius)
    (hradius0 : ∀ ω, 0 ≤ radius ω)
    (scale theta C : ℝ) (hscale : 0 < scale) (htheta : 0 < theta)
    (hC : 0 ≤ C)
    (hsmall : ∀ ρ : ℝ, 0 < ρ →
      μ {ω | radius ω ≤ theta * scale * ρ} ≤
        ENNReal.ofReal (C * ρ)) :
    μ {ω | radius ω = 0} = 0 ∧
      MemLp (fun ω => logDeficit scale (radius ω)) 2 μ ∧
      ∫ ω, logDeficit scale (radius ω) ^ 2 ∂μ ≤
        oneSidedLogSecondMomentBound (C / theta) 1 := by
  apply zeroSet_memLp_two_and_integral_sq_logDeficit_of_linearSmallBall
    μ radius hradius hradius0 scale (C / theta) hscale
      (div_nonneg hC htheta.le)
  intro ρ hρ
  have hρtheta : 0 < ρ / theta := div_pos hρ htheta
  have hscaleIdentity : theta * scale * (ρ / theta) = scale * ρ := by
    field_simp [htheta.ne']
  calc
    μ {ω | radius ω ≤ scale * ρ} =
        μ {ω | radius ω ≤ theta * scale * (ρ / theta)} := by
      rw [hscaleIdentity]
    _ ≤ ENNReal.ofReal (C * (ρ / theta)) :=
      hsmall (ρ / theta) hρtheta
    _ = ENNReal.ofReal ((C / theta) * ρ) := by
      congr 1
      field_simp [htheta.ne']

end CircularLawSection4
