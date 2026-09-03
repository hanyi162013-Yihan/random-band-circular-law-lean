import BernoulliSection10Complex.PhysicalIIDEmbedding
import BernoulliSection10.PhysicalProfile
import BernoulliSection10Complex.PhysicalAtomEnergy

/-! # Entrywise identification and the physical Hilbert--Schmidt energy -/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open BernoulliLinearAlgebra

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem densityCyclicMatrix_from_square (W s : ℕ)
    (x : Fin ((s + 3) * W) × Fin ((s + 3) * W) → ℂ)
    (i j : Fin ((s + 3) * W)) :
    densityCyclicMatrix W s (physicalRowsFromSquare W s x) i j =
      (physicalProfile W s i j : ℂ) * x (i, j) := by
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp only [densityCyclicMatrix, densityShiftedCyclicMatrix, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, physicalCyclicMatrix_entry]
  simp only [intervalSiteBlocks, intervalPhysicalRow, physicalRowGroupOfAtoms,
    normalizedPhysicalAtom, physicalRowsFromSquare, physicalColumn,
    intervalRowIndex, physicalAtomIndex, Equiv.symm_apply_apply,
    physicalProfile, sub_zero, ite_self]
  obtain ⟨h1, h2, h3⟩ := cyclic_three_positions_distinct s i
  by_cases hd : j = i
  · subst j
    simp [h1.symm, h2.symm, physicalSiteAdjacent, physicalNeighborSite]
  · by_cases hb : j = cyclicSiteSucc i
    · subst j
      simp [h1, h3, physicalSiteAdjacent, physicalNeighborSite]
    · by_cases hc : j = (cyclicSiteSucc (m := s + 2)).symm i
      · subst j
        simp [h2, h3.symm, physicalSiteAdjacent, physicalNeighborSite]
      · simp [hd, hb, hc, physicalSiteAdjacent, physicalNeighborSite]

theorem densityCyclicMatrix_from_sequence (W s : ℕ) (ω : ℕ → ℂ)
    (i j : Fin ((s + 3) * W)) :
    densityCyclicMatrix W s (physicalRowsFromSequence W s ω) i j =
      (physicalProfile W s i j : ℂ) * ω (finProdFinEquiv (i, j)).val :=
  densityCyclicMatrix_from_square W s (squareIIDFromSequence ((s + 3) * W) ω) i j

theorem normalizedPhysicalAtom_norm_sq {W : ℕ} (x : PhysicalRowAtoms W)
    (b : Fin 3) (c : Fin W) :
    ‖normalizedPhysicalAtom x b c‖ ^ 2 =
      (3 * (W : ℝ))⁻¹ * ‖x (physicalAtomIndex b c)‖ ^ 2 := by
  simp only [normalizedPhysicalAtom, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, blockNormalization_sq]

theorem densityCyclicMatrix_squared_entry_sum (W s : ℕ)
    (x : IntervalRows W (s + 3)) :
    (∑ i, ∑ j, ‖densityCyclicMatrix W s x i j‖ ^ 2) =
      (3 * (W : ℝ))⁻¹ * ∑ i, ∑ a, ‖x i a‖ ^ 2 := by
  simp only [densityCyclicMatrix, densityShiftedCyclicMatrix, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  rw [← (finProdFinEquiv : Fin (s + 3) × Fin W ≃ Fin ((s + 3) * W)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  simp_rw [← (finProdFinEquiv : Fin (s + 3) × Fin W ≃ Fin ((s + 3) * W)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [physicalCyclicMatrix_squared_entry_sum]
  simp only [Fintype.sum_prod_type]
  simp only [intervalSiteBlocks, intervalPhysicalRow, physicalRowGroupOfAtoms,
    ite_self, sub_zero, normalizedPhysicalAtom_norm_sq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← (finProdFinEquiv : Fin 3 × Fin W ≃ Fin (3 * W)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, add_zero]
  simp only [physicalAtomIndex, intervalRowIndex,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem densityCyclicMatrix_normalized_energy (W s : ℕ) (hW : 0 < W)
    (x : IntervalRows W (s + 3)) :
    (∑ i, ∑ j, ‖densityCyclicMatrix W s x i j‖ ^ 2) / (((s + 3) * W : ℕ) : ℝ) =
      intervalMeanAtomSquare W (s + 3) x := by
  rw [densityCyclicMatrix_squared_entry_sum]
  simp only [intervalMeanAtomSquare, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  field_simp

end BernoulliSection10Complex

