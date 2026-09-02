import BernoulliSection10.PhysicalProfile

/-! # Every scalar distance at most W lies in one of the three physical blocks -/

noncomputable section

namespace BernoulliSection10

open BernoulliLinearAlgebra

theorem physicalSiteAdjacent_of_val_succ {s : ℕ} {i j : Fin (s + 3)}
    (h : j.val = i.val + 1) : physicalSiteAdjacent i j := by
  apply Or.inr
  apply Or.inl
  apply Fin.ext
  rw [cyclicSiteSucc_val (m := s + 2)]
  split_ifs <;> omega

theorem physicalSiteAdjacent_first_last {s : ℕ} {i j : Fin (s + 3)}
    (hi : i.val = 0) (hj : j.val = s + 2) : physicalSiteAdjacent i j := by
  apply Or.inr
  apply Or.inr
  apply (cyclicSiteSucc (m := s + 2)).eq_symm_apply.mpr
  apply Fin.ext
  rw [cyclicSiteSucc_val (m := s + 2)]
  simp [hi, hj]

theorem physicalSiteAdjacent_of_ordered_scalar_distance
    (W s : ℕ) (hW : 0 < W) (i j : Fin ((s + 3) * W))
    (hij : i.val ≤ j.val)
    (hd : min (j.val - i.val) (((s + 3) * W) - (j.val - i.val)) ≤ W) :
    physicalSiteAdjacent (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 := by
  let a : Fin (s + 3) := (finProdFinEquiv.symm i).1
  let b : Fin (s + 3) := (finProdFinEquiv.symm j).1
  have ha : a.val = i.val / W := rfl
  have hb : b.val = j.val / W := rfl
  change physicalSiteAdjacent a b
  rcases min_le_iff.mp hd with hnear | hwrap
  · have hle : a.val ≤ b.val := by
      rw [ha, hb]
      exact Nat.div_le_div_right hij
    have hsucc : b.val ≤ a.val + 1 := by
      rw [ha, hb, ← Nat.add_div_right i.val hW]
      exact Nat.div_le_div_right (by omega)
    have hcases : b.val = a.val ∨ b.val = a.val + 1 := by omega
    rcases hcases with hsame | hstep
    · exact Or.inl (Fin.ext hsame)
    · exact physicalSiteAdjacent_of_val_succ hstep
  · have hsize : (s + 3) * W = (s + 2) * W + W := by ring
    have hilow : i.val < W := by have := j.isLt; omega
    have hjhigh : (s + 2) * W ≤ j.val := by omega
    have hazero : a.val = 0 := by rw [ha]; exact Nat.div_eq_of_lt hilow
    have hblast : b.val = s + 2 := by
      have hlow : s + 2 ≤ b.val := by
        rw [hb]
        exact (Nat.le_div_iff_mul_le hW).mpr hjhigh
      have hhigh := b.isLt
      omega
    exact physicalSiteAdjacent_first_last hazero hblast

theorem physicalSiteAdjacent_of_scalar_distance
    (W s : ℕ) (hW : 0 < W) (i j : Fin ((s + 3) * W))
    (hd : min (i.val - j.val + (j.val - i.val))
      (((s + 3) * W) - (i.val - j.val + (j.val - i.val))) ≤ W) :
    physicalSiteAdjacent (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 := by
  rcases le_total i.val j.val with hij | hji
  · apply physicalSiteAdjacent_of_ordered_scalar_distance W s hW i j hij
    simpa only [Nat.sub_eq_zero_of_le hij, zero_add] using hd
  · apply physicalSiteAdjacent_symm.mpr
    apply physicalSiteAdjacent_of_ordered_scalar_distance W s hW j i hji
    simpa only [Nat.sub_eq_zero_of_le hji, add_zero] using hd

theorem physicalProfile_scalar_band_value
    (W s : ℕ) (hW : 0 < W) (i j : Fin ((s + 3) * W))
    (hd : min (i.val - j.val + (j.val - i.val))
      (((s + 3) * W) - (i.val - j.val + (j.val - i.val))) ≤ W) :
    physicalProfile W s i j ^ 2 = (3 * (W : ℝ))⁻¹ := by
  rw [physicalProfile, if_pos (physicalSiteAdjacent_of_scalar_distance W s hW i j hd),
    blockNormalization_sq]

end BernoulliSection10
