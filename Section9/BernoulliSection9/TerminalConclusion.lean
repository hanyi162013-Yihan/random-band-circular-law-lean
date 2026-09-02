import BernoulliSection9.TerminalSmallBall

/-!
# Assembly of the terminal small-ball conclusion

This module packages the final measure-theoretic step of Proposition 7.3.
In particular, the atom-at-zero estimate is derived from the capped bounds;
it is not an additional hypothesis.
-/

noncomputable section

namespace BernoulliSection9

open MeasureTheory

/-- The capped integral dominates the cap times the mass of the zero set. -/
theorem terminal_cap_mul_zeroProbability_le_integral
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (T c : Real) (hT : 0 <= T)
    (value : Omega -> Complex) (hvalue : Measurable value)
    (hloss : Integrable (fun omega => cappedLogLoss T c (value omega)) mu) :
    T * mu.real {omega | value omega = 0} <=
      ∫ omega, cappedLogLoss T c (value omega) ∂mu := by
  let zeroSet : Set Omega := {omega | value omega = 0}
  let indicator : Omega -> Real := zeroSet.indicator (fun _ => T)
  have hzero : MeasurableSet zeroSet :=
    hvalue (measurableSet_singleton 0)
  have hind : Integrable indicator mu :=
    (integrable_const T).indicator hzero
  have hpoint : forall omega,
      indicator omega <= cappedLogLoss T c (value omega) := by
    intro omega
    by_cases homega : value omega = 0
    · simp [indicator, zeroSet, homega]
    · simp [indicator, zeroSet, homega, cappedLogLoss_nonneg hT]
  calc
    T * mu.real {omega | value omega = 0} =
        ∫ omega, indicator omega ∂mu := by
      rw [show {omega | value omega = 0} = zeroSet from rfl]
      rw [show (∫ omega, indicator omega ∂mu) =
          mu.real zeroSet * T by
        simpa [indicator] using
          (integral_indicator_const (μ := mu) T hzero)]
      ring
    _ <= ∫ omega, cappedLogLoss T c (value omega) ∂mu :=
      integral_mono hind hloss hpoint

/-- Build the four-part terminal conclusion once the concrete capped,
reverse, and Parseval estimates have been proved.  The zero probability is
deduced by sending the cap to infinity. -/
noncomputable def terminalSmallBallConclusion_of_capped
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (coefficientNorm : Real) (value : Omega -> Complex)
    (baseLoss badProbability : Real)
    (hcoefficientNorm : 0 < coefficientNorm)
    (hbase : 0 <= baseLoss)
    (hvalue : Measurable value)
    (hloss : forall T : Real, 0 < T ->
      Integrable (fun omega => cappedLogLoss T coefficientNorm (value omega)) mu)
    (hcapped : forall T : Real, 0 < T ->
      ∫ omega, cappedLogLoss T coefficientNorm (value omega) ∂mu <=
        baseLoss + badProbability * T)
    (reverseEvent : Set Omega)
    (hreverse : ∀ omega ∈ reverseEvent,
      Real.posLog (‖value omega‖ / coefficientNorm) <= baseLoss)
    (hparseval : coefficientNorm ^ 2 =
      ∫ omega, ‖value omega‖ ^ 2 ∂mu) :
    TerminalSmallBallConclusion mu coefficientNorm value
      baseLoss badProbability := by
  have hzero : mu.real {omega | value omega = 0} <= badProbability := by
    apply zeroProbability_of_all_capped_bounds hbase
    intro T hT
    exact (terminal_cap_mul_zeroProbability_le_integral mu T coefficientNorm
      hT.le value hvalue (hloss T hT)).trans (hcapped T hT)
  exact
    { coefficientNorm_pos := hcoefficientNorm
      capped := hcapped
      zero_probability := hzero
      reverse_event := reverseEvent
      reverse := hreverse
      parseval := hparseval }

end BernoulliSection9
