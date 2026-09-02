import CircularLawSection4.OrderedRowLinearity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.Rev

/-! # Dimension-free inverse bounds for cleared companion exterior powers

Reversing the coordinates turns the inverse companion into another companion.
Its row-linear expansion has the same total coefficient size, with the two
edge coefficients interchanged.  This proves the complementary inverse bound
without introducing a factor depending on the exterior dimension.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CircularLawSections56.Section5

open CircularLawSection4 Matrix

def reversedCompanionCoefficients (d : ℕ) (β : ℂ) (c : Fin (d + 1) → ℂ) :
    Fin (d + 1) → ℂ :=
  Fin.cases β (fun i => c i.rev.succ)

private theorem companion_mulVec_castSucc (d : ℕ) (β : ℂ)
    (c v : Fin (d + 1) → ℂ) (i : Fin d) :
    (rowCompanion (finLeftShift d) (Fin.last d) β c *ᵥ v) i.castSucc = v i.succ := by
  classical
  change (∑ j, (Function.update (finLeftShift d) (Fin.last d) (-β⁻¹ • c)
    i.castSucc) j * v j) = _
  rw [Function.update_of_ne (Fin.castSucc_ne_last i)]
  have he : ∀ j : Fin (d + 1), i.val + 1 = j.val ↔ j = i.succ := by
    intro j
    constructor
    · intro h
      exact Fin.ext h.symm
    · rintro rfl
      rfl
  simp [finLeftShift, he]

private theorem companion_mulVec_last (d : ℕ) (β : ℂ)
    (c v : Fin (d + 1) → ℂ) :
    (rowCompanion (finLeftShift d) (Fin.last d) β c *ᵥ v) (Fin.last d) =
      -β⁻¹ * ∑ j, c j * v j := by
  classical
  change (∑ j, (Function.update (finLeftShift d) (Fin.last d) (-β⁻¹ • c)
    (Fin.last d)) j * v j) = _
  rw [Function.update_self]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

private theorem reversedCompanion_mulVec_zero (d : ℕ) (β : ℂ)
    (c v : Fin (d + 1) → ℂ) :
    ((Fin.revPerm.permMatrix ℂ *
      rowCompanion (finLeftShift d) (Fin.last d) (c 0)
        (reversedCompanionCoefficients d β c) * Fin.revPerm.permMatrix ℂ) *ᵥ v) 0 =
      -(c 0)⁻¹ * (β * v (Fin.last d) + ∑ i : Fin d, c i.succ * v i.castSucc) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, permMatrix_mulVec, permMatrix_mulVec]
  change (rowCompanion _ _ _ _ *ᵥ (v ∘ Fin.rev)) (Fin.rev 0) = _
  rw [Fin.rev_zero, companion_mulVec_last, Fin.sum_univ_succ]
  simp only [reversedCompanionCoefficients, Fin.cases_zero, Fin.cases_succ,
    Function.comp_apply, Fin.rev_zero, Fin.rev_succ]
  congr 2
  exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin d)) (fun i => c i.succ * v i.castSucc)

private theorem reversedCompanion_mulVec_succ (d : ℕ) (β : ℂ)
    (c v : Fin (d + 1) → ℂ) (i : Fin d) :
    ((Fin.revPerm.permMatrix ℂ *
      rowCompanion (finLeftShift d) (Fin.last d) (c 0)
        (reversedCompanionCoefficients d β c) * Fin.revPerm.permMatrix ℂ) *ᵥ v) i.succ =
      v i.castSucc := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, permMatrix_mulVec, permMatrix_mulVec]
  change (rowCompanion _ _ _ _ *ᵥ (v ∘ Fin.rev)) (Fin.rev i.succ) = _
  rw [Fin.rev_succ, companion_mulVec_castSucc]
  simp only [Function.comp_apply, Fin.rev_succ, Fin.rev_rev]

theorem reversedCompanion_mul_companion (d : ℕ) (β : ℂ) (c : Fin (d + 1) → ℂ)
    (hβ : β ≠ 0) (hc : c 0 ≠ 0) :
    (Fin.revPerm.permMatrix ℂ *
        rowCompanion (finLeftShift d) (Fin.last d) (c 0)
          (reversedCompanionCoefficients d β c) * Fin.revPerm.permMatrix ℂ) *
      rowCompanion (finLeftShift d) (Fin.last d) β c = 1 := by
  apply Matrix.mulVec_injective
  funext v
  rw [← mulVec_mulVec, one_mulVec]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [reversedCompanion_mulVec_zero, companion_mulVec_last]
    simp_rw [companion_mulVec_castSucc]
    rw [Fin.sum_univ_succ]
    field_simp [hβ, hc]
    ring
  · rw [reversedCompanion_mulVec_succ, companion_mulVec_castSucc]

theorem companion_inverse_eq_reversed (d : ℕ) (β : ℂ) (c : Fin (d + 1) → ℂ)
    (hβ : β ≠ 0) (hc : c 0 ≠ 0) :
    (rowCompanion (finLeftShift d) (Fin.last d) β c)⁻¹ =
      Fin.revPerm.permMatrix ℂ *
        rowCompanion (finLeftShift d) (Fin.last d) (c 0)
          (reversedCompanionCoefficients d β c) * Fin.revPerm.permMatrix ℂ :=
  Matrix.inv_eq_left_inv (reversedCompanion_mul_companion d β c hβ hc)

theorem compound_identity (d k : ℕ) :
    compound k (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = 1 := by
  simp [compound]
  rw [← exteriorPower.coe_basis]
  exact ((Pi.basisFun ℂ (Fin (d + 1))).exteriorPower k).toMatrix_self

theorem compound_conjTranspose (d k : ℕ)
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    compound k Aᴴ = (compound k A)ᴴ := by
  ext s t
  simp only [compound_apply, conjTranspose_apply, minor]
  rw [← Matrix.det_conjTranspose]
  rfl

theorem compound_permMatrix_norm_le_one (d : ℕ) (q : ExteriorDegree (d + 1))
    (σ : Equiv.Perm (Fin (d + 1))) :
    ‖compound q.val (σ.permMatrix ℂ)‖ ≤ 1 := by
  let : Nonempty (ExteriorIndex (d + 1) q) := by
    obtain ⟨s, hs⟩ : ((Finset.univ : Finset (Fin (d + 1))).powersetCard q.val).Nonempty :=
      Finset.powersetCard_nonempty.2 (by simpa using Nat.le_of_lt_succ q.isLt)
    exact ⟨⟨s, (Finset.mem_powersetCard.1 hs).2⟩⟩
  have hunit : (compound q.val (σ.permMatrix ℂ))ᴴ *
      compound q.val (σ.permMatrix ℂ) = 1 := by
    rw [← compound_conjTranspose, ← compound_mul, conjTranspose_permMatrix,
      ← permMatrix_mul, mul_inv_cancel, permMatrix_one, compound_identity]
  have hnorm := Matrix.l2_opNorm_conjTranspose_mul_self (compound q.val (σ.permMatrix ℂ))
  rw [hunit] at hnorm
  have hone : ‖(1 : Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)‖ ≤ 1 :=
    (norm_one).le
  nlinarith [norm_nonneg (compound q.val (σ.permMatrix ℂ))]

theorem norm_clearedCompanion_le (d : ℕ) (q : ExteriorDegree (d + 1))
    (β : ℂ) (c : Fin (d + 1) → ℂ) (hβ : β ≠ 0) :
    ‖β • compound q.val (rowCompanion (finLeftShift d) (Fin.last d) β c)‖ ≤
      ‖β‖ + ∑ j, ‖c j‖ := by
  change ‖clearedRowCompanionCompound _ _ _ _ _‖ ≤ _
  rw [clearedRowCompanionCompound_eq_orderedCoefficient d q β c hβ]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (orderedCoefficient_l2_opNorm_le_one d q none)
      (norm_nonneg β)).trans_eq (mul_one _)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (orderedCoefficient_l2_opNorm_le_one d q (some j))
      (norm_nonneg (c j))).trans_eq (mul_one _)

theorem reversedCompanion_coefficient_size (d : ℕ) (β : ℂ) (c : Fin (d + 1) → ℂ) :
    ‖c 0‖ + ∑ j, ‖reversedCompanionCoefficients d β c j‖ = ‖β‖ + ∑ j, ‖c j‖ := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [reversedCompanionCoefficients, Fin.cases_zero, Fin.cases_succ]
  have hs := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin d)) (fun i => ‖c i.succ‖)
  change (∑ i : Fin d, ‖c i.rev.succ‖) = ∑ i : Fin d, ‖c i.succ‖ at hs
  rw [hs]
  ring

/-- All exterior degrees, including zero and the top degree, share the same
two-edge denominator and the same linear coefficient majorant. -/
theorem norm_clearedCompanion_inverse_le (d : ℕ) (q : ExteriorDegree (d + 1))
    (β : ℂ) (c : Fin (d + 1) → ℂ) (hβ : β ≠ 0) (hc : c 0 ≠ 0) :
    ‖(β • compound q.val (rowCompanion (finLeftShift d) (Fin.last d) β c))⁻¹‖ ≤
      (‖β‖ + ∑ j, ‖c j‖) / (‖c 0‖ * ‖β‖) := by
  let T := rowCompanion (finLeftShift d) (Fin.last d) β c
  let T' := rowCompanion (finLeftShift d) (Fin.last d) (c 0)
    (reversedCompanionCoefficients d β c)
  let U := compound q.val (Fin.revPerm.permMatrix ℂ : Matrix (Fin (d + 1)) _ ℂ)
  have hU : ‖U‖ ≤ 1 := compound_permMatrix_norm_le_one d q _
  have hT : IsUnit T.det :=
    Matrix.isUnit_det_of_left_inverse (reversedCompanion_mul_companion d β c hβ hc)
  have hclear : (β • compound q.val T)⁻¹ = β⁻¹ • compound q.val T⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← compound_mul, Matrix.nonsing_inv_mul _ hT,
      compound_identity, inv_mul_cancel₀ hβ, one_smul]
  have hconj : compound q.val T⁻¹ = U * compound q.val T' * U := by
    dsimp only [T, T', U]
    rw [companion_inverse_eq_reversed d β c hβ hc, compound_mul, compound_mul]
  have hnorm : ‖compound q.val T⁻¹‖ ≤ ‖compound q.val T'‖ := by
    rw [hconj]
    calc
      _ ≤ (‖U‖ * ‖compound q.val T'‖) * ‖U‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg U))
      _ ≤ (1 * ‖compound q.val T'‖) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hU (norm_nonneg _)) hU
          (norm_nonneg U) (by positivity)
      _ = _ := by ring
  have hrow := norm_clearedCompanion_le d q (c 0) (reversedCompanionCoefficients d β c) hc
  rw [reversedCompanion_coefficient_size, norm_smul] at hrow
  have hbound : ‖compound q.val T'‖ ≤ (‖β‖ + ∑ j, ‖c j‖) / ‖c 0‖ :=
    (le_div_iff₀ (norm_pos_iff.2 hc)).2 (by simpa only [mul_comm] using hrow)
  change ‖(β • compound q.val T)⁻¹‖ ≤ _
  rw [hclear, norm_smul, norm_inv]
  calc
    _ ≤ ‖β‖⁻¹ * ((‖β‖ + ∑ j, ‖c j‖) / ‖c 0‖) :=
      mul_le_mul_of_nonneg_left (hnorm.trans hbound) (by positivity)
    _ = _ := by ring

end CircularLawSections56.Section5
