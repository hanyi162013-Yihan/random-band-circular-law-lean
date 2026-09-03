import CircularLawSection6.BlockSingularCutoff
import CircularLawSection6.PeriodicizationEnergy
import CircularLawSection6.CutoffIntegrability

/-! # Actual periodic blocks and their logarithmic cutoff averages

The same-atom periodicized matrix is exactly a dependent block diagonal
matrix. The spectral cutoff is therefore its dimension-weighted block
average. Finite atom second moment also gives cutoff integrability for
each shifted routed block, off a planar null set of spectral parameters.
-/

open MeasureTheory TaoVuReplacement
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem routedBand_shifted_cutoff_integrable_ae
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ]
    (route : ι → κ → ι) (hroute : ∀ i, Function.Injective (route i)) (a : κ → ℂ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ t : ℝ, 0 < t →
      Integrable (fun ω => matrixCutoffPotential (routedBandMatrix route a ω - z • 1) t)
        (Measure.pi (fun _ : ι × κ => ν)) := by
  let μ := Measure.pi (fun _ : ι × κ => ν)
  have hM := routedBandMatrix_measurable route a
  have hE : Integrable (fun ω => hilbertSchmidtSq (routedBandMatrix route a ω)) μ := by
    simpa only [hilbertSchmidtSq, routedBand_row_energy route hroute] using
      (routedAtoms_expected_boundary_energy (Finset.univ : Finset ι) a ν hInt).1
  filter_upwards [ae_shifted_matrix_det_ne_zero μ (routedBandMatrix route a) hM] with z hz
  intro t ht
  exact integrable_matrixCutoffPotential μ (fun ω => routedBandMatrix route a ω - z • 1)
    (hM.sub measurable_const) hz
    (integrable_hilbertSchmidtSq_sub μ (routedBandMatrix route a) (fun _ => z • 1)
      hM measurable_const hE (integrable_const _)) ht

variable {q : ℕ} (len : Fin q → ℕ) [∀ b, NeZero (len b)]

theorem periodicBlockMatrix_eq_blockDiagonal (H : ℕ) (a : Fin (2 * H + 1) → ℂ)
    (ω : ((b : Fin q) × Fin (len b)) × Fin (2 * H + 1) → ℂ) :
    routedBandMatrix (periodicBlockRoute len H) a ω =
      Matrix.blockDiagonal' (fun b => routedBandMatrix (cyclicFinSlot H) a (periodicBlockAtoms len H b ω)) := by
  ext ⟨b, i⟩ ⟨c, j⟩
  by_cases h : b = c
  · subst c
    simpa only [Matrix.submatrix_apply, Matrix.blockDiagonal'_apply_eq] using
      congrArg (fun A : Matrix (Fin (len b)) (Fin (len b)) ℂ => A i j)
        (periodicBlockMatrix_diagonal_block len H b a ω)
  · rw [periodicBlockMatrix_off_block len H a ω ⟨b, i⟩ ⟨c, j⟩ h,
      Matrix.blockDiagonal'_apply_ne _ _ _ h]

theorem periodicBlockMatrix_shift_eq_blockDiagonal (H : ℕ) (a : Fin (2 * H + 1) → ℂ)
    (ω : ((b : Fin q) × Fin (len b)) × Fin (2 * H + 1) → ℂ) (z : ℂ) :
    routedBandMatrix (periodicBlockRoute len H) a ω - z • 1 =
      Matrix.blockDiagonal' (fun b =>
        routedBandMatrix (cyclicFinSlot H) a (periodicBlockAtoms len H b ω) - z • 1) := by
  rw [periodicBlockMatrix_eq_blockDiagonal len H a ω]
  have h := Matrix.blockDiagonal'_sub
    (fun b => routedBandMatrix (cyclicFinSlot H) a (periodicBlockAtoms len H b ω))
    (z • (1 : ∀ b : Fin q, Matrix (Fin (len b)) (Fin (len b)) ℂ))
  rw [Matrix.blockDiagonal'_smul, Matrix.blockDiagonal'_one] at h
  exact h.symm

theorem periodicBlockMatrix_cutoff_average (H : ℕ) (a : Fin (2 * H + 1) → ℂ)
    (ω : ((b : Fin q) × Fin (len b)) × Fin (2 * H + 1) → ℂ) (z : ℂ)
    (hdet : ∀ b, (routedBandMatrix (cyclicFinSlot H) a (periodicBlockAtoms len H b ω) - z • 1).det ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    matrixCutoffPotential (routedBandMatrix (periodicBlockRoute len H) a ω - z • 1) t =
      (∑ b, (len b : ℝ) * matrixCutoffPotential
        (routedBandMatrix (cyclicFinSlot H) a (periodicBlockAtoms len H b ω) - z • 1) t) /
        (∑ b, len b : ℕ) := by
  rw [periodicBlockMatrix_shift_eq_blockDiagonal len H a ω z]
  simpa only [Fintype.card_fin] using matrixCutoffPotential_blockDiagonal
    (fun b => routedBandMatrix (cyclicFinSlot H) a (periodicBlockAtoms len H b ω) - z • 1) hdet ht

theorem periodicBlockMatrix_expected_cutoff_average_ae {H : ℕ}
    (hfit : ∀ b, 2 * H + 1 ≤ len b) (a : Fin (2 * H + 1) → ℂ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ t : ℝ, 0 < t →
      Integrable (fun ω => matrixCutoffPotential (routedBandMatrix (periodicBlockRoute len H) a ω - z • 1) t)
        (Measure.pi (fun _ : ((b : Fin q) × Fin (len b)) × Fin (2 * H + 1) => ν)) ∧
      (∫ ω, matrixCutoffPotential (routedBandMatrix (periodicBlockRoute len H) a ω - z • 1) t
        ∂Measure.pi (fun _ : ((b : Fin q) × Fin (len b)) × Fin (2 * H + 1) => ν)) =
        (∑ b, (len b : ℝ) * ∫ η, matrixCutoffPotential
          (routedBandMatrix (cyclicFinSlot H) a η - z • (1 : Matrix (Fin (len b)) (Fin (len b)) ℂ)) t
            ∂Measure.pi (fun _ : Fin (len b) × Fin (2 * H + 1) => ν)) /
          (∑ b, len b : ℕ) := by
  let μ := Measure.pi (fun _ : ((b : Fin q) × Fin (len b)) × Fin (2 * H + 1) => ν)
  let μb (b : Fin q) := Measure.pi (fun _ : Fin (len b) × Fin (2 * H + 1) => ν)
  have hdet : ∀ᵐ z ∂(volume : Measure ℂ), ∀ b : Fin q, ∀ᵐ η ∂μb b,
      (routedBandMatrix (cyclicFinSlot H) a η - z • (1 : Matrix (Fin (len b)) (Fin (len b)) ℂ)).det ≠ 0 :=
    ae_all_iff.2 (fun b => ae_shifted_matrix_det_ne_zero (μb b)
      (routedBandMatrix (cyclicFinSlot H) a) (routedBandMatrix_measurable _ _))
  have hint : ∀ᵐ z ∂(volume : Measure ℂ), ∀ b : Fin q, ∀ t : ℝ, 0 < t →
      Integrable (fun η => matrixCutoffPotential
        (routedBandMatrix (cyclicFinSlot H) a η - z • (1 : Matrix (Fin (len b)) (Fin (len b)) ℂ)) t) (μb b) :=
    ae_all_iff.2 (fun b => routedBand_shifted_cutoff_integrable_ae (cyclicFinSlot H)
      (cyclicFinSlot_injective (hfit b)) a ν hInt)
  filter_upwards [hdet, hint] with z hz hi
  intro t ht
  let F (b : Fin q) (η : Fin (len b) × Fin (2 * H + 1) → ℂ) :=
    matrixCutoffPotential (routedBandMatrix (cyclicFinSlot H) a η - z • 1) t
  have hiF (b : Fin q) : Integrable (F b) (μb b) := hi b t ht
  have hiComp (b : Fin q) : Integrable (fun ω => F b (periodicBlockAtoms len H b ω)) μ :=
    (periodicBlockAtoms_measurePreserving len H b ν).integrable_comp_of_integrable (hiF b)
  have hall : ∀ᵐ ω ∂μ, ∀ b : Fin q,
      (routedBandMatrix (cyclicFinSlot H) a (periodicBlockAtoms len H b ω) - z • 1).det ≠ 0 :=
    ae_all_iff.2 (fun b => (periodicBlockAtoms_measurePreserving len H b ν).quasiMeasurePreserving.ae (hz b))
  have heq : (fun ω => matrixCutoffPotential (routedBandMatrix (periodicBlockRoute len H) a ω - z • 1) t) =ᵐ[μ]
      (fun ω => (∑ b, (len b : ℝ) * F b (periodicBlockAtoms len H b ω)) / (∑ b, len b : ℕ)) := by
    filter_upwards [hall] with ω hω
    exact periodicBlockMatrix_cutoff_average len H a ω z hω ht
  have hisum := (integrable_finsetSum Finset.univ (fun b _ => (hiComp b).const_mul (len b : ℝ))).div_const
    (∑ b, len b : ℕ)
  refine ⟨hisum.congr heq.symm, ?_⟩
  have hmean (b : Fin q) : (∫ ω, F b (periodicBlockAtoms len H b ω) ∂μ) = ∫ η, F b η ∂μb b := by
    have hmp := periodicBlockAtoms_measurePreserving len H b ν
    have hm : AEStronglyMeasurable (F b) (μ.map (periodicBlockAtoms len H b)) := by
      rw [hmp.map_eq]
      exact (hiF b).aestronglyMeasurable
    calc
      _ = ∫ η, F b η ∂μ.map (periodicBlockAtoms len H b) :=
        (integral_map hmp.measurable.aemeasurable hm).symm
      _ = _ := by rw [hmp.map_eq]
  rw [integral_congr_ae heq, integral_div,
    integral_finsetSum _ (fun b _ => (hiComp b).const_mul (len b : ℝ))]
  simp only [integral_const_mul, hmean]
  rfl

end CircularLawSection6
