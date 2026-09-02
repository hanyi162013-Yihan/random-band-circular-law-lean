import BernoulliSection10.CyclicPhysicalModel

/-! # The three distinct physical block positions in every cyclic row -/

open scoped Matrix BigOperators

noncomputable section

namespace BernoulliSection10

open BernoulliLinearAlgebra Matrix

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem cyclicSiteSucc_val {m : ℕ} (j : Fin (m + 1)) :
    (cyclicSiteSucc j).val = if j.val = m then 0 else j.val + 1 := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · simp [Nat.ne_of_lt i.isLt]

theorem cyclicSiteSucc_twice_ne_self (s : ℕ) (j : Fin (s + 3)) :
    cyclicSiteSucc (cyclicSiteSucc j) ≠ j := by
  intro h
  have hv := congrArg Fin.val h
  have h1 := cyclicSiteSucc_val (m := s + 2) j
  have h2 := cyclicSiteSucc_val (m := s + 2) (cyclicSiteSucc j)
  split_ifs at h1 h2 <;> omega

theorem cyclic_three_positions_distinct (s : ℕ) (j : Fin (s + 3)) :
    cyclicSiteSucc j ≠ j ∧ (cyclicSiteSucc (m := s + 2)).symm j ≠ j ∧
      cyclicSiteSucc j ≠ (cyclicSiteSucc (m := s + 2)).symm j := by
  have h1 : cyclicSiteSucc j ≠ j := periodicSiteSucc_ne_self (by omega) j
  refine ⟨h1, ?_, ?_⟩
  · intro h
    have hv := congrArg (cyclicSiteSucc (m := s + 2)) h
    simp only [Equiv.apply_symm_apply] at hv
    exact h1 hv.symm
  · intro h
    apply cyclicSiteSucc_twice_ne_self s j
    have hv := congrArg (cyclicSiteSucc (m := s + 2)) h
    simpa only [Equiv.apply_symm_apply] using hv

theorem cyclicShift_inv_eq_permMatrix (W m : ℕ) :
    (cyclicShift (R := ℂ) (m := m) (w := Fin W))⁻¹ =
      Equiv.Perm.permMatrix ℂ (cyclicScalarSucc (m := m) (w := Fin W)).symm := by
  apply Matrix.inv_eq_right_inv
  change (cyclicScalarSucc (m := m) (w := Fin W)).permMatrix ℂ *
    (cyclicScalarSucc (m := m) (w := Fin W) : Equiv.Perm _)⁻¹.permMatrix ℂ = 1
  rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

theorem siteBlockDiagonal_mul_cyclicShift_inv_apply
    (W m : ℕ) (A : Fin (m + 1) → Matrix (Fin W) (Fin W) ℂ)
    (j k : Fin (m + 1)) (a b : Fin W) :
    (siteBlockDiagonal A * (cyclicShift (R := ℂ) (m := m) (w := Fin W))⁻¹)
      (j, a) (k, b) =
        if k = (cyclicSiteSucc (m := m)).symm j then A j a b else 0 := by
  rw [cyclicShift_inv_eq_permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  simp only [Matrix.submatrix_apply, siteBlockDiagonal, Matrix.comp_apply,
    Matrix.diagonal, cyclicScalarSucc]
  by_cases h : k = (cyclicSiteSucc (m := m)).symm j
  · subst k
    simp
  · have hs : j ≠ cyclicSiteSucc k := by
      intro hj
      exact h ((cyclicSiteSucc (m := m)).symm_apply_eq.mpr hj).symm
    simp [h, hs]

theorem physicalCyclicMatrix_entry
    (W m : ℕ) (B D C : Fin (m + 1) → Matrix (Fin W) (Fin W) ℂ)
    (j k : Fin (m + 1)) (a b : Fin W) :
    physicalCyclicMatrix B D C (j, a) (k, b) =
      (if k = j then D j a b else 0) +
        (if k = cyclicSiteSucc j then B j a b else 0) +
        (if k = (cyclicSiteSucc (m := m)).symm j then C j a b else 0) := by
  simp only [physicalCyclicMatrix, Matrix.add_apply]
  rw [siteBlockDiagonal_apply, siteBlockDiagonal_mul_cyclicShift_apply,
    siteBlockDiagonal_mul_cyclicShift_inv_apply]
  simp only [eq_comm]

theorem physicalCyclicMatrix_entry_norm_sq
    (W s : ℕ) (B D C : Fin (s + 3) → Matrix (Fin W) (Fin W) ℂ)
    (j k : Fin (s + 3)) (a b : Fin W) :
    ‖physicalCyclicMatrix B D C (j, a) (k, b)‖ ^ 2 =
      (if k = j then ‖D j a b‖ ^ 2 else 0) +
        (if k = cyclicSiteSucc j then ‖B j a b‖ ^ 2 else 0) +
        (if k = (cyclicSiteSucc (m := s + 2)).symm j then ‖C j a b‖ ^ 2 else 0) := by
  rw [physicalCyclicMatrix_entry]
  obtain ⟨h1, h2, h3⟩ := cyclic_three_positions_distinct s j
  by_cases hd : k = j
  · subst k
    simp [h1.symm, h2.symm]
  · by_cases hb : k = cyclicSiteSucc j
    · subst k
      simp [h1, h3]
    · by_cases hc : k = (cyclicSiteSucc (m := s + 2)).symm j
      · subst k
        simp [h2, h3.symm]
      · simp [hd, hb, hc]

theorem physicalCyclicMatrix_squared_entry_sum
    (W s : ℕ) (B D C : Fin (s + 3) → Matrix (Fin W) (Fin W) ℂ) :
    (∑ i, ∑ k, ‖physicalCyclicMatrix B D C i k‖ ^ 2) =
      ∑ j, ∑ a, ∑ b, (‖D j a b‖ ^ 2 + ‖B j a b‖ ^ 2 + ‖C j a b‖ ^ 2) := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [physicalCyclicMatrix_entry_norm_sq, Finset.sum_add_distrib]
  simp

end BernoulliSection10
