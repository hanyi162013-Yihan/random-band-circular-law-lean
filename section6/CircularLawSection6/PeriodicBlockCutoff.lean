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

end CircularLawSection6
