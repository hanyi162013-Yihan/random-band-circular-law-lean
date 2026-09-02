import CircularLawSection6.ContiguousBlockRouting
import CircularLawSection6.RoutedBandCoupling
import CircularLawSection6.MatrixParameterNonvanishing
import CircularLawSection4.PiRestrictMarginal

/-! # Actual periodic block marginals and the boundary energy

The block-periodic matrix uses the common row/slot atoms. Its off-block
entries vanish, and each diagonal block has exactly the finite IID atom
law. The full and block routes differ only on the proved boundary set.
Thus their expected normalized HS error is at most `8H/m₀` whenever every
block has length at least `m₀`. No random coupling or boundary estimate is
left as a hypothesis of this finite result.
-/

open MeasureTheory
open TaoVuReplacement
open CircularLawSection4
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

variable {q : ℕ} (len : Fin q → ℕ)

def periodicBlockAtoms (H : ℕ) (b : Fin q)
    (ω : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) → ℂ) :
    Fin (len b) × Fin (2 * H + 1) → ℂ := fun k => ω (⟨b, k.1⟩, k.2)

theorem periodicBlockAtoms_measurePreserving (H : ℕ) (b : Fin q)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    MeasurePreserving (periodicBlockAtoms len H b)
      (Measure.pi (fun _ : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) => ν))
      (Measure.pi (fun _ : Fin (len b) × Fin (2 * H + 1) => ν)) := by
  apply measurePreserving_pi_restrict_injective
    (fun k : Fin (len b) × Fin (2 * H + 1) =>
      ((⟨b, k.1⟩ : (j : Fin q) × Fin (len j)), k.2))
  intro x y h
  exact Prod.ext (sigma_mk_injective (congrArg Prod.fst h)) (congrArg Prod.snd h)

theorem periodicBlockMatrix_diagonal_block [∀ b, NeZero (len b)] (H : ℕ)
    (b : Fin q) (a : Fin (2 * H + 1) → ℂ)
    (ω : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) → ℂ) :
    (routedBandMatrix (periodicBlockRoute len H) a ω).submatrix
      (fun i => (⟨b, i⟩ : (j : Fin q) × Fin (len j)))
      (fun i => (⟨b, i⟩ : (j : Fin q) × Fin (len j))) =
        routedBandMatrix (cyclicFinSlot H) a (periodicBlockAtoms len H b ω) := by
  ext i j
  simp only [Matrix.submatrix_apply, routedBandMatrix, periodicBlockRoute,
    Sigma.mk.inj_iff, heq_eq_eq, true_and, periodicBlockAtoms]

theorem periodicBlockMatrix_off_block [∀ b, NeZero (len b)] (H : ℕ)
    (a : Fin (2 * H + 1) → ℂ)
    (ω : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) → ℂ)
    (i j : (b : Fin q) × Fin (len b)) (hij : i.1 ≠ j.1) :
    routedBandMatrix (periodicBlockRoute len H) a ω i j = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  apply if_neg
  intro h
  exact hij (congrArg Sigma.fst h).symm

theorem periodicization_expected_energy [∀ b, NeZero (len b)] [NeZero (∑ b, len b)]
    {H : ℕ} (hfit : ∀ b, 2 * H + 1 ≤ len b)
    (a : Fin (2 * H + 1) → ℂ) (ha : ∑ s, ‖a s‖ ^ 2 = 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν) (hMoment : (∫ u : ℂ, ‖u‖ ^ 2 ∂ν) = 1) :
    Integrable (fun ω => hilbertSchmidtSq
      (routedBandMatrix (fullBlockRoute len H) a ω -
        routedBandMatrix (periodicBlockRoute len H) a ω))
      (Measure.pi (fun _ : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) => ν)) ∧
      (∫ ω, hilbertSchmidtSq (routedBandMatrix (fullBlockRoute len H) a ω -
        routedBandMatrix (periodicBlockRoute len H) a ω)
        ∂Measure.pi (fun _ : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) => ν)) ≤
          8 * (H : ℝ) * q := by
  have h := routedBand_expected_difference_energy_le
    (fullBlockRoute len H) (periodicBlockRoute len H)
    (fullBlockRoute_injective len hfit) (periodicBlockRoute_injective len hfit)
    (blockBoundaryRows len H) (blockRoutes_eq_off_boundary len hfit) a ha ν hInt hMoment
  refine ⟨h.1, h.2.trans ?_⟩
  have hc : ((blockBoundaryRows len H).card : ℝ) ≤ (q : ℝ) * (2 * (H : ℝ)) := by
    exact_mod_cast blockBoundaryRows_card_le len H
  nlinarith

theorem periodicization_expected_normalized_energy
    [∀ b, NeZero (len b)] [NeZero (∑ b, len b)]
    {H m₀ : ℕ} (hm₀ : 0 < m₀) (hmin : ∀ b, m₀ ≤ len b)
    (hfit : ∀ b, 2 * H + 1 ≤ len b)
    (a : Fin (2 * H + 1) → ℂ) (ha : ∑ s, ‖a s‖ ^ 2 = 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν) (hMoment : (∫ u : ℂ, ‖u‖ ^ 2 ∂ν) = 1) :
    (∫ ω, hilbertSchmidtSq (routedBandMatrix (fullBlockRoute len H) a ω -
      routedBandMatrix (periodicBlockRoute len H) a ω)
      ∂Measure.pi (fun _ : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) => ν)) /
      (∑ b, len b : ℕ) ≤ 8 * (H : ℝ) / m₀ := by
  have hn : (0 : ℝ) < (∑ b, len b : ℕ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hm : (0 : ℝ) < m₀ := Nat.cast_pos.mpr hm₀
  have hc : q * m₀ ≤ ∑ b, len b := by
    calc
      _ = ∑ _ : Fin q, m₀ := by simp
      _ ≤ _ := Finset.sum_le_sum (fun b _ => hmin b)
  have hcr : (q : ℝ) * m₀ ≤ (∑ b, len b : ℕ) := by exact_mod_cast hc
  calc
    _ ≤ (8 * (H : ℝ) * q) / (∑ b, len b : ℕ) :=
      div_le_div_of_nonneg_right (periodicization_expected_energy len hfit a ha ν hInt hMoment).2 hn.le
    _ ≤ _ := by
      apply (div_le_div_iff₀ hn hm).mpr
      nlinarith [mul_le_mul_of_nonneg_left hcr (show (0 : ℝ) ≤ 8 * H by positivity)]

/-- The actual block coupling gives the cutoff error with no supplied
nonsingularity or cutoff-integrability premise. -/
theorem periodicization_expected_cutoff_ae
    [∀ b, NeZero (len b)] [NeZero (∑ b, len b)]
    {H m₀ : ℕ} (hm₀ : 0 < m₀) (hmin : ∀ b, m₀ ≤ len b)
    (hfit : ∀ b, 2 * H + 1 ≤ len b)
    (b : Fin (2 * H + 1) → ℂ) (hb : ∑ s, ‖b s‖ ^ 2 = 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν) (hMoment : (∫ u : ℂ, ‖u‖ ^ 2 ∂ν) = 1) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ a : ℝ, 0 < a →
      Integrable (fun ω =>
        |matrixCutoffPotential (routedBandMatrix (fullBlockRoute len H) b ω - z • 1) a -
          matrixCutoffPotential (routedBandMatrix (periodicBlockRoute len H) b ω - z • 1) a|)
        (Measure.pi (fun _ : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) => ν)) ∧
      (∫ ω,
        |matrixCutoffPotential (routedBandMatrix (fullBlockRoute len H) b ω - z • 1) a -
          matrixCutoffPotential (routedBandMatrix (periodicBlockRoute len H) b ω - z • 1) a|
        ∂Measure.pi (fun _ : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) => ν)) ≤
          Real.sqrt (8 * (H : ℝ) / m₀) / a := by
  letI : Nonempty ((j : Fin q) × Fin (len j)) := Fintype.card_pos_iff.mp (by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using NeZero.pos (∑ j, len j))
  have hE := periodicization_expected_energy len hfit b hb ν hInt hMoment
  have hnorm := periodicization_expected_normalized_energy len hm₀ hmin hfit b hb ν hInt hMoment
  have h := expected_shifted_matrixCutoff_difference_ae
    (Measure.pi (fun _ : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) => ν))
    (routedBandMatrix (fullBlockRoute len H) b) (routedBandMatrix (periodicBlockRoute len H) b)
    (routedBandMatrix_measurable _ _) (routedBandMatrix_measurable _ _) hE.1
  filter_upwards [h] with z hz
  intro a ha
  obtain ⟨hi, hbound⟩ := hz a ha
  refine ⟨hi, hbound.trans ?_⟩
  simp only [Fintype.card_sigma, Fintype.card_fin]
  calc
    _ = Real.sqrt ((∫ ω, hilbertSchmidtSq
        (routedBandMatrix (fullBlockRoute len H) b ω -
          routedBandMatrix (periodicBlockRoute len H) b ω)
        ∂Measure.pi (fun _ : ((j : Fin q) × Fin (len j)) × Fin (2 * H + 1) => ν)) /
          (∑ j, len j : ℕ)) / a := by
      rw [Real.sqrt_div' _ (Nat.cast_nonneg _), div_div, mul_comm _ a]
    _ ≤ _ := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hnorm) ha.le

end CircularLawSection6
