import BernoulliSection10.PhysicalMatrixEntries
import BernoulliSection10.Section3Inputs
import BernoulliSection10.CyclicPressureComparison
import BernoulliSection10.ProbabilityTransport

/-! # Exact transfer between the source IID array and the actual row model -/

open MeasureTheory

noncomputable section

namespace BernoulliSection10.SourceInputs

open ProbabilityLimits ShortRingAnchor

def physicalRowsFromInput (W s : ℕ) (ω : InputSpace) : IntervalRows W (s + 3) :=
  physicalRowsFromSequence W s ω.1

theorem physicalRowsFromInput_measurePreserving
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (W s : ℕ) :
    MeasurePreserving (physicalRowsFromInput W s) (inputLaw μ) (intervalRowsLaw W (s + 3) μ) :=
  (physicalRowsFromSequence_measurePreserving μ W s).comp
    (measurePreserving_fst (μ := Measure.infinitePi fun _ : ℕ => μ)
      (ν := Measure.infinitePi fun _ : ℕ => circularGaussianPairLaw))

theorem densityCyclicMatrix_physicalRowsFromInput (W s : ℕ) (ω : InputSpace) :
    densityCyclicMatrix W s (physicalRowsFromInput W s ω) = profileMatrix (physicalProfile W s) ω := by
  ext i j
  exact densityCyclicMatrix_from_sequence W s ω.1 i j

theorem normalizedShiftLogDet_physicalProfile (W s : ℕ) (z : ℂ) (ω : InputSpace) :
    normalizedShiftLogDet (profileMatrix (physicalProfile W s) ω) z =
      densityCyclicLogDet W s z (physicalRowsFromInput W s ω) / (((s + 3) * W : ℕ) : ℝ) := by
  unfold normalizedShiftLogDet densityCyclicLogDet
  rw [densityShiftedCyclicMatrix_eq_sub_scalar, densityCyclicMatrix_physicalRowsFromInput]

theorem profile_log_converges_iff_physical_rows
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (W s : ℕ → ℕ) (z : ℂ) (u : ℝ) :
    ConvergesInProbability (inputLaw μ)
      (fun n ω => normalizedShiftLogDet (profileMatrix (physicalProfile (W n) (s n)) ω) z) u ↔
      TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) μ)
        (fun n x => densityCyclicLogDet (W n) (s n) z x / (((s n + 3) * W n : ℕ) : ℝ)) u := by
  have h := tendstoInProbabilityTri_measurePreserving_iff
    (fun _ => inputLaw μ) (fun n => intervalRowsLaw (W n) (s n + 3) μ)
    (fun n => physicalRowsFromInput (W n) (s n))
    (fun n => physicalRowsFromInput_measurePreserving μ (W n) (s n))
    (fun n x => densityCyclicLogDet (W n) (s n) z x / (((s n + 3) * W n : ℕ) : ℝ))
    (fun n => (measurable_densityCyclicLogDet (W n) (s n) z).div_const _) u
  simpa only [TendstoInProbabilityTri, ConvergesInProbability,
    tendstoInMeasure_iff_measureReal_norm, Real.norm_eq_abs,
    ← normalizedShiftLogDet_physicalProfile] using h

end BernoulliSection10.SourceInputs
