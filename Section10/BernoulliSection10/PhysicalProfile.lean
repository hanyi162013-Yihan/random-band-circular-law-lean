import BernoulliSection10.PhysicalIIDEmbedding

/-! # The literal cyclic variance profile and its stochastic normalization -/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliSection10

open BernoulliLinearAlgebra

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def physicalSiteAdjacent {s : ℕ} (i j : Fin (s + 3)) : Prop :=
  j = i ∨ j = cyclicSiteSucc i ∨ j = (cyclicSiteSucc (m := s + 2)).symm i

instance {s : ℕ} (i j : Fin (s + 3)) : Decidable (physicalSiteAdjacent i j) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem physicalSiteAdjacent_symm {s : ℕ} {i j : Fin (s + 3)} :
    physicalSiteAdjacent i j ↔ physicalSiteAdjacent j i := by
  simp only [physicalSiteAdjacent, Equiv.eq_symm_apply, Equiv.symm_apply_eq]
  aesop

def physicalProfile (W s : ℕ) :
    Matrix (Fin ((s + 3) * W)) (Fin ((s + 3) * W)) ℝ :=
  fun i j => if physicalSiteAdjacent (finProdFinEquiv.symm i).1
    (finProdFinEquiv.symm j).1 then blockNormalization W else 0

theorem physicalProfile_nonnegative (W s : ℕ) (i j : Fin ((s + 3) * W)) :
    0 ≤ physicalProfile W s i j := by
  unfold physicalProfile blockNormalization
  split_ifs <;> positivity

theorem physicalProfile_symm (W s : ℕ) (i j : Fin ((s + 3) * W)) :
    physicalProfile W s i j = physicalProfile W s j i := by
  simp only [physicalProfile, physicalSiteAdjacent_symm]

theorem blockNormalization_sq (W : ℕ) :
    blockNormalization W ^ 2 = (3 * (W : ℝ))⁻¹ := by
  rw [blockNormalization, inv_pow, Real.sq_sqrt (by positivity)]

theorem physicalProfile_square_three_positions (W s : ℕ)
    (i j : Fin (s + 3)) (a b : Fin W) :
    physicalProfile W s (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) ^ 2 =
      (if j = i then (3 * (W : ℝ))⁻¹ else 0) +
      (if j = cyclicSiteSucc i then (3 * (W : ℝ))⁻¹ else 0) +
      (if j = (cyclicSiteSucc (m := s + 2)).symm i then (3 * (W : ℝ))⁻¹ else 0) := by
  obtain ⟨h1, h2, h3⟩ := cyclic_three_positions_distinct s i
  simp only [physicalProfile, Equiv.symm_apply_apply, physicalSiteAdjacent]
  by_cases hd : j = i
  · subst j
    simp [h1.symm, h2.symm, blockNormalization_sq]
  · by_cases hb : j = cyclicSiteSucc i
    · subst j
      simp [h1, h3, blockNormalization_sq]
    · by_cases hc : j = (cyclicSiteSucc (m := s + 2)).symm i
      · subst j
        simp [h2, h3.symm, blockNormalization_sq]
      · simp [hd, hb, hc]

theorem physicalProfile_row (W s : ℕ) (hW : 0 < W)
    (i : Fin ((s + 3) * W)) : ∑ j, physicalProfile W s i j ^ 2 = 1 := by
  obtain ⟨⟨j, a⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [← (finProdFinEquiv : Fin (s + 3) × Fin W ≃ Fin ((s + 3) * W)).sum_comp]
  simp only [Fintype.sum_prod_type, physicalProfile_square_three_positions]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib]
  simp
  field_simp
  <;> ring

theorem physicalProfile_column (W s : ℕ) (hW : 0 < W)
    (j : Fin ((s + 3) * W)) : ∑ i, physicalProfile W s i j ^ 2 = 1 := by
  simp_rw [physicalProfile_symm W s _ j]
  exact physicalProfile_row W s hW j

theorem physicalColumn_adjacent (W s : ℕ) (i : Fin ((s + 3) * W))
    (a : Fin (3 * W)) :
    physicalSiteAdjacent (finProdFinEquiv.symm i).1
      (finProdFinEquiv.symm (physicalColumn W s i a)).1 := by
  simp only [physicalColumn, Equiv.symm_apply_apply, physicalNeighborSite]
  split_ifs <;> simp_all [physicalSiteAdjacent]

theorem physicalProfile_at_column (W s : ℕ) (i : Fin ((s + 3) * W))
    (a : Fin (3 * W)) : physicalProfile W s i (physicalColumn W s i a) =
      blockNormalization W := by
  exact if_pos (physicalColumn_adjacent W s i a)

theorem physicalProfile_sq_le (W s : ℕ) (i j : Fin ((s + 3) * W)) :
    physicalProfile W s i j ^ 2 ≤ (3 * (W : ℝ))⁻¹ := by
  unfold physicalProfile
  split_ifs
  · exact (blockNormalization_sq W).le
  · simp only [zero_pow (by omega : 2 ≠ 0)]
    positivity

end BernoulliSection10
