import CircularLawSection4.StateCopyElimination

/-!
# Raw rows of the cyclic companion state matrix

This module identifies each early row of the cyclic companion matrix with the
literal two-term equation `s_{i+1,k} - s_{i,k+1} = 0` in the original raw
coordinates.
-/

open scoped Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

section GenericIdentificationRow

variable {R : Type*} [CommRing R]

private theorem sumInl_eq_splitStateCopyEquiv_succ_iff
    (N m : ℕ) (j : Fin N) (k : Fin m)
    (c : StateDifferenceIndex N m) :
    Sum.inl c = splitStateCopyEquiv N m (j, k.succ) ↔
      j = (ofLex c).1 ∧ (ofLex c).2.val = k.val + 1 := by
  constructor
  · intro h
    have h' :
        splitStateCopyEquiv N m ((ofLex c).1, (ofLex c).2.castSucc) =
          splitStateCopyEquiv N m (j, k.succ) := by
      simpa using h
    have hp := (splitStateCopyEquiv N m).injective h'
    constructor
    · exact (congrArg Prod.fst hp).symm
    · have hv := congrArg (fun x : Fin N × Fin (m + 1) => x.2.val) hp
      simpa using hv
  · rintro ⟨hj, hk⟩
    have hp : ((ofLex c).1, (ofLex c).2.castSucc) = (j, k.succ) := by
      apply Prod.ext
      · exact hj.symm
      · apply Fin.ext
        simpa using hk
    have hs := congrArg (splitStateCopyEquiv N m) hp
    simpa using hs

private theorem sumInr_eq_splitStateCopyEquiv_succ_iff
    (N m : ℕ) (j : Fin N) (k : Fin m) (c : Fin N) :
    Sum.inr c = splitStateCopyEquiv N m (j, k.succ) ↔
      j = c ∧ k.val + 1 = m := by
  constructor
  · intro h
    have h' :
        splitStateCopyEquiv N m (c, Fin.last m) =
          splitStateCopyEquiv N m (j, k.succ) := by
      simpa using h
    have hp := (splitStateCopyEquiv N m).injective h'
    constructor
    · exact (congrArg Prod.fst hp).symm
    · have hv := congrArg (fun x : Fin N × Fin (m + 1) => x.2.val) hp
      simpa using hv.symm
  · rintro ⟨hj, hk⟩
    have hp : (c, Fin.last m) = (j, k.succ) := by
      apply Prod.ext
      · exact hj.symm
      · apply Fin.ext
        simpa using hk.symm
    rw [← splitStateCopyEquiv_last N m c]
    exact congrArg (splitStateCopyEquiv N m) hp

/-- A row of the ordered state-identification matrix is the difference of the
current copy and its successor copy. -/
theorem stateIdentificationMatrix_row_eq_single_sub_single
    (N m : ℕ) (j : Fin N) (k : Fin m) :
    stateIdentificationMatrix (R := R) N m (toLex (j, k)) =
      Pi.single (splitStateCopyEquiv N m (j, k.castSucc)) 1 -
        Pi.single (splitStateCopyEquiv N m (j, k.succ)) 1 := by
  classical
  funext c
  rcases c with c | c
  · rw [stateIdentificationMatrix, differenceAnchorMatrix]
    simp only [Matrix.fromBlocks_apply₁₁, Pi.sub_apply, Pi.single_apply]
    rw [splitStateCopyEquiv_castSucc]
    simp only [sumInl_eq_splitStateCopyEquiv_succ_iff]
    simp only [Sum.inl.injEq]
    obtain ⟨⟨j', k'⟩, rfl⟩ :=
      (toLex : (Fin N × Fin m) ≃ StateDifferenceIndex N m).surjective c
    change
      (if (j, k) = (j', k') then 1
        else if j = j' ∧ k'.val = k.val + 1 then -1 else 0) =
      (if (j', k') = (j, k) then 1 else 0) -
        if j = j' ∧ k'.val = k.val + 1 then 1 else 0
    by_cases hcur : (j, k) = (j', k')
    · have hj : j = j' := congrArg Prod.fst hcur
      have hk : k = k' := congrArg Prod.snd hcur
      subst j'
      subst k'
      simp
    · have hcur' : (j', k') ≠ (j, k) := fun h => hcur h.symm
      by_cases hnext : j = j' ∧ k'.val = k.val + 1
      · have hkne : k ≠ k' := by
          intro hk
          apply hcur
          exact Prod.ext hnext.1 hk
        have hkne' : k' ≠ k := fun hk => hkne hk.symm
        simp [hnext, hkne, hkne']
      · simp [hcur, hcur', hnext]
  · rw [stateIdentificationMatrix, differenceAnchorMatrix]
    simp only [Matrix.fromBlocks_apply₁₂, Pi.sub_apply, Pi.single_apply]
    rw [splitStateCopyEquiv_castSucc]
    simp only [sumInr_eq_splitStateCopyEquiv_succ_iff]
    simp only [Sum.inr_ne_inl, ↓reduceIte, zero_sub]
    rw [stateAnchorCoupling]
    change
      (if j = c ∧ k.val + 1 = m then (-1 : R) else 0) =
        -(if j = c ∧ k.val + 1 = m then 1 else 0)
    by_cases h : j = c ∧ k.val + 1 = m <;> simp [h]

end GenericIdentificationRow

section RawCyclicRows

variable {R : Type*} [CommRing R]

private theorem cyclicStateCopyRelabel_next_castSucc
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (i : ZMod N) (k : Fin m) :
    cyclicStateCopyRelabel N m offset (i + 1, k.castSucc) =
      splitStateCopyEquiv N m
        ((ZMod.finEquiv N).symm
          (i + offset + 1 + (k.val : ZMod N)), k.castSucc) := by
  rw [cyclicStateCopyRelabel_castSucc, splitStateCopyEquiv_castSucc]
  apply congrArg (fun p : Fin N × Fin m =>
    (Sum.inl (toLex p) : StateCopyIndex N m))
  apply Prod.ext
  · apply (ZMod.finEquiv N).injective
    abel_nf
  · rfl

private theorem cyclicStateCopyRelabel_succ
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (i : ZMod N) (k : Fin m) :
    cyclicStateCopyRelabel N m offset (i, k.succ) =
      splitStateCopyEquiv N m
        ((ZMod.finEquiv N).symm
          (i + offset + 1 + (k.val : ZMod N)), k.succ) := by
  change
    splitStateCopyEquiv N m
        ((ZMod.finEquiv N).symm
          (i + offset + ((k.succ).val : ZMod N)), k.succ) = _
  apply congrArg (splitStateCopyEquiv N m)
  apply Prod.ext
  · apply (ZMod.finEquiv N).injective
    simp only [Fin.val_succ]
    push_cast
    abel_nf
  · rfl

/-- Every early raw row of the cyclic companion state matrix is literally
the coefficient row of `s_{i+1,k} - s_{i,k+1} = 0`.  In particular, this
theorem verifies the raw equation independently of the later row and column
reindexings used for determinant elimination. -/
theorem cyclicCompanionStateMatrix_castSucc_row
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R))
    (i : ZMod N) (k : Fin m) :
    cyclicCompanionStateMatrix N m offset lastRow (i, k.castSucc) =
      Pi.single (i + 1, k.castSucc) 1 - Pi.single (i, k.succ) 1 := by
  classical
  funext col
  rw [cyclicCompanionStateMatrix_castSucc]
  rw [cyclicEquationDifferenceIndex]
  rw [stateIdentificationMatrix_row_eq_single_sub_single]
  rw [← cyclicStateCopyRelabel_next_castSucc N m offset i k]
  rw [← cyclicStateCopyRelabel_succ N m offset i k]
  simp only [Pi.sub_apply, Pi.single_apply]
  simp only [(cyclicStateCopyRelabel N m offset).apply_eq_iff_eq]

end RawCyclicRows

end CircularLawSection4
