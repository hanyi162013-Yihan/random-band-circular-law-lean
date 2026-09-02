import CircularLawSections56.Section5.RealAtomLogMoments

/-! # Elementary atom hypotheses shared by the real and complex branches -/

open scoped ENNReal MeasureTheory
open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5

open CircularLawSection4

structure AtomLogControl (ν : Measure ℂ) (K : ℝ) : Prop where
  second_integrable : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν
  second_le_one : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1
  nonzero : ∀ᵐ u : ℂ ∂ν, u ≠ 0
  negative_integrable : Integrable (fun u : ℂ => negativeLog ‖u‖) ν
  negative_bound : ∫ u : ℂ, negativeLog ‖u‖ ∂ν ≤ K

theorem AtomLogControl.real
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (L : ℝ) (hL : 0 ≤ L)
    (hν : RealIntervalBound ν (ENNReal.ofReal L))
    (hInt : Integrable (fun u : ℝ => u ^ 2) ν) (hSecond : ∫ u : ℝ, u ^ 2 ∂ν ≤ 1) :
    AtomLogControl (realComplexAtomLaw ν) (Real.log (max 1 (2 * L)) + 1) where
  second_integrable := (realComplexAtomLaw_secondMoment ν hInt).1
  second_le_one := (realComplexAtomLaw_secondMoment ν hInt).2.trans_le hSecond
  nonzero := realComplexAtomLaw_ae_ne_zero ν hν
  negative_integrable := (realComplexAtomLaw_negativeLog ν L hL hν).1
  negative_bound := (realComplexAtomLaw_negativeLog ν L hL hν).2

theorem AtomLogControl.complex
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (L : ℝ) (hL : 0 ≤ L)
    (hν : ComplexBallBound ν (ENNReal.ofReal L))
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν) (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    AtomLogControl ν ((Real.log (max 1 (Real.pi * L)) + 1) / 2) where
  second_integrable := hInt
  second_le_one := hSecond
  nonzero := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using
      measure_singleton_zero_eq_zero_of_complexBallBound hν
  negative_integrable := (negativeLog_norm_integrable_and_bound ν L hL hν).1
  negative_bound := (negativeLog_norm_integrable_and_bound ν L hL hν).2

end CircularLawSections56.Section5
