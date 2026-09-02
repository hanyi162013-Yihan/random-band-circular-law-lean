import BernoulliSection10.DiagonalDiskReference
import BernoulliSection10.SpectralLimitAssembly

/-!
Adapted from the user's proved Section 5 assembly, with a diverging dimension
sequence and the same internally constructed diagonal comparison ensemble.

# From the circular logarithmic potential to the circular law

All comparison-ensemble requirements are discharged with the diagonal disk
ensemble. The auxiliary independent sample is removed from the conclusion.
Only measurability, a uniform expected energy bound, and the circular
log-potential limit of the matrix being studied remain as hypotheses.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1800000

namespace BernoulliSection10.DiskReference

open BernoulliSection10.Replacement BernoulliSection10.ProbabilityLimits TaoVuReplacement ShortRingAnchor

universe u v
variable {Ω : Type u} {Λ : Type v} [MeasurableSpace Ω] [MeasurableSpace Λ]

/-- This identity needs no measurability of the test statistic: the product
measure formula for rectangles is valid for arbitrary sets. -/
theorem tendstoInMeasure_prod_fst_iff
    (P : Measure Ω) (Q : Measure Λ) [IsProbabilityMeasure Q]
    (X : ℕ → Ω → ℝ) (a : ℝ) :
    TendstoInMeasure (P.prod Q) (fun n ω => X n ω.1) atTop (fun _ => a) ↔
      TendstoInMeasure P X atTop (fun _ => a) := by
  simp only [tendstoInMeasure_iff_norm]
  have heq (n : ℕ) (ε : ℝ) :
      (P.prod Q) {ω : Ω × Λ | ε ≤ ‖X n ω.1 - a‖} =
        P {ω | ε ≤ ‖X n ω - a‖} := by
    have hs : {ω : Ω × Λ | ε ≤ ‖X n ω.1 - a‖} =
        {ω | ε ≤ ‖X n ω - a‖} ×ˢ Set.univ := by ext ω; simp
    rw [hs, Measure.prod_prod, measure_univ, mul_one]
  simp only [heq]

theorem tendstoInMeasure_prod_snd_iff
    (P : Measure Ω) (Q : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Λ → ℝ) (a : ℝ) :
    TendstoInMeasure (P.prod Q) (fun n ω => X n ω.2) atTop (fun _ => a) ↔
      TendstoInMeasure Q X atTop (fun _ => a) := by
  simp only [tendstoInMeasure_iff_norm]
  have heq (n : ℕ) (ε : ℝ) :
      (P.prod Q) {ω : Ω × Λ | ε ≤ ‖X n ω.2 - a‖} =
        Q {ω | ε ≤ ‖X n ω - a‖} := by
    have hs : {ω : Ω × Λ | ε ≤ ‖X n ω.2 - a‖} =
        Set.univ ×ˢ {ω | ε ≤ ‖X n ω - a‖} := by ext ω; simp
    rw [hs, Measure.prod_prod, measure_univ, one_mul]
  simp only [heq]

/-- The actual circular-law conclusion. No comparison model, comparison limit,
or replacement-principle implication is supplied by the caller. -/
theorem physical_circularLaw_of_logPotential
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → ℕ) (hd : Tendsto d atTop atTop)
    (X : ∀ k, Ω → Matrix (Fin (d k + 1)) (Fin (d k + 1)) ℂ)
    (hX : ∀ k i j, Measurable (fun ω => X k ω i j))
    (C : ℝ) (hC : 0 ≤ C)
    (hInt : ∀ k, Integrable (fun ω => physicalEnergy (X k ω)) P)
    (hEnergy : ∀ k, ∫ ω, physicalEnergy (X k ω) ∂P ≤ C)
    (hLog : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInMeasure P
      (fun k ω => physicalLogPotential (X k ω) z) atTop (fun _ => circularLogPotential z)) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure P (fun k ω => realEsdTest (X k ω) f) atTop
        (fun _ => ∫ w, f w ∂circularMeasure) := by
  let R := P.prod circularSampleMeasure
  let X' := fun k (ω : Ω × (ℕ → ℂ)) => X k ω.1
  let Y' := fun k (ω : Ω × (ℕ → ℂ)) => diagonalDiskReference (d k) ω.2
  have hXI : ∀ k, Integrable (fun ω => physicalEnergy (X' k ω)) R := fun k =>
    (measurePreserving_fst (μ := P) (ν := circularSampleMeasure)).integrable_comp_of_integrable
      (hInt k)
  have hYI : ∀ k, Integrable (fun ω => physicalEnergy (Y' k ω)) R := fun k =>
    (measurePreserving_snd (μ := P) (ν := circularSampleMeasure)).integrable_comp_of_integrable
      (diagonalDiskReference_energy_integrable_and_le_one (d k)).1
  have hReplacement := physical_replacement_of_logPotential_limits R X' Y'
    (fun k i j => (hX k i j).comp measurable_fst)
    (fun k i j => (diagonalDiskReference_measurable (d k) i j).comp measurable_snd)
    (C + 1) (by positivity) (fun k => (hXI k).add (hYI k)) (fun k => by
      rw [integral_add (hXI k) (hYI k)]
      change (∫ ω, physicalEnergy (X k ω.1) ∂P.prod circularSampleMeasure) +
        (∫ ω, physicalEnergy (diagonalDiskReference (d k) ω.2) ∂P.prod circularSampleMeasure) ≤ _
      rw [integral_fun_fst (μ := P) (ν := circularSampleMeasure)
        (fun ω => physicalEnergy (X k ω)),
        integral_fun_snd (μ := P) (ν := circularSampleMeasure)
          (fun ω => physicalEnergy (diagonalDiskReference (d k) ω))]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      exact add_le_add (hEnergy k) (diagonalDiskReference_energy_integrable_and_le_one (d k)).2)
    circularLogPotential (by
      filter_upwards [hLog] with z hz
      exact (tendstoInMeasure_iff_tri R
        (fun k ω => physicalLogPotential (X' k ω) z) (circularLogPotential z)).1
        ((tendstoInMeasure_prod_fst_iff P circularSampleMeasure
          (fun k ω => physicalLogPotential (X k ω) z) (circularLogPotential z)).2 hz)) (by
      exact ae_of_all _ fun z => (tendstoInMeasure_iff_tri R
        (fun k ω => physicalLogPotential (Y' k ω) z) (circularLogPotential z)).1
        ((tendstoInMeasure_prod_snd_iff P circularSampleMeasure
          (fun k ω => physicalLogPotential (diagonalDiskReference (d k) ω) z)
          (circularLogPotential z)).2
          (diagonalDiskReference_logPotential_limit_sequence d hd z)))
  have hLimit := esd_limit_of_replacement R X' Y'
    (fun f => ∫ w, f w ∂circularMeasure) hReplacement (fun f hf hc =>
      (tendstoInMeasure_prod_snd_iff P circularSampleMeasure
        (fun k ω => realEsdTest (diagonalDiskReference (d k) ω) f)
        (∫ w, f w ∂circularMeasure)).2
        (diagonalDiskReference_esd_limit_sequence d hd f hf hc))
  intro f hf hc
  exact (tendstoInMeasure_prod_fst_iff P circularSampleMeasure
    (fun k ω => realEsdTest (X k ω) f) (∫ w, f w ∂circularMeasure)).1 (hLimit f hf hc)


end BernoulliSection10.DiskReference
