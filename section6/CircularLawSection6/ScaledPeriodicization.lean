import CircularLawSection6.PeriodicizationEnergy
import CircularLawSection6.SingularBasisCutoff
import CircularLawSection6.FixedScaleCoreBridge

/-! # The actual periodicization error at positive variance scale

The exact cutoff scaling identity and null-set transport give the factor
`r/a` in the manuscript's periodicization estimate. All sample
nonsingularity and integrability premises are discharged by earlier
finite-matrix results.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem periodicization_expected_scaled_cutoff_ae
    {q : ℕ} (len : Fin q → ℕ) [∀ b, NeZero (len b)] [NeZero (∑ b, len b)]
    {H m₀ : ℕ} (hm₀ : 0 < m₀) (hmin : ∀ b, m₀ ≤ len b)
    (hfit : ∀ b, 2 * H + 1 ≤ len b)
    (b : Fin (2 * H + 1) → ℂ) (hb : ∑ s, ‖b s‖ ^ 2 = 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν) (hMoment : (∫ u : ℂ, ‖u‖ ^ 2 ∂ν) = 1)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ a : ℝ, 0 < a →
      Integrable (fun ω =>
        |matrixCutoffPotential ((r : ℂ) • routedBandMatrix (fullBlockRoute len H) b ω - z • 1) a -
          matrixCutoffPotential ((r : ℂ) • routedBandMatrix (periodicBlockRoute len H) b ω - z • 1) a|)
        (Measure.pi (fun _ : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) => ν)) ∧
      (∫ ω,
        |matrixCutoffPotential ((r : ℂ) • routedBandMatrix (fullBlockRoute len H) b ω - z • 1) a -
          matrixCutoffPotential ((r : ℂ) • routedBandMatrix (periodicBlockRoute len H) b ω - z • 1) a|
        ∂Measure.pi (fun _ : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) => ν)) ≤
          r * Real.sqrt (8 * (H : ℝ) / m₀) / a := by
  let : Nonempty ((j : Fin q) × Fin (len j)) := Fintype.card_pos_iff.mp (by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using NeZero.pos (∑ j, len j))
  let μ := Measure.pi (fun _ : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) => ν)
  let A := routedBandMatrix (fullBlockRoute len H) b
  let B := routedBandMatrix (periodicBlockRoute len H) b
  have hA := ae_div_real hr.ne' (ae_shifted_matrix_det_ne_zero μ A (routedBandMatrix_measurable _ _))
  have hB := ae_div_real hr.ne' (ae_shifted_matrix_det_ne_zero μ B (routedBandMatrix_measurable _ _))
  have herror := ae_div_real hr.ne'
    (periodicization_expected_cutoff_ae len hm₀ hmin hfit b hb ν hInt hMoment)
  filter_upwards [hA, hB, herror] with z hzA hzB hzerror
  intro a ha
  have heq : (fun ω => |matrixCutoffPotential ((r : ℂ) • A ω - z • 1) a -
      matrixCutoffPotential ((r : ℂ) • B ω - z • 1) a|) =ᵐ[μ]
      (fun ω => |matrixCutoffPotential (A ω - (z / (r : ℂ)) • 1) (a / r) -
        matrixCutoffPotential (B ω - (z / (r : ℂ)) • 1) (a / r)|) := by
    filter_upwards [hzA, hzB] with ω hωA hωB
    rw [matrixCutoffPotential_shifted_smul (A ω) z hr ha hωA,
      matrixCutoffPotential_shifted_smul (B ω) z hr ha hωB, add_sub_add_left_eq_sub]
  have h := hzerror (a / r) (div_pos ha hr)
  refine ⟨h.1.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  exact h.2.trans_eq (by field_simp)

end CircularLawSection6
