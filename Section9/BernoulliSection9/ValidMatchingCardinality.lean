import BernoulliLinearAlgebra.ThreeBlockMaskExpansion

/-!
# Cardinality of valid three-block partial matchings

A row-injective matching is encoded by one optional selected variable per
full packet row.  This gives the `exp(O(W log W))`, rather than powerset
`exp(O(W^2))`, counting bound required by the terminal reverse estimate.
-/

noncomputable section

namespace BernoulliSection9

open BernoulliLinearAlgebra

/-- The optional matching entry selected in a given full packet row. -/
def validMatchingRowCode
    {w : Type*} [Fintype w] [DecidableEq w]
    (a : ValidThreeBlockMatching w) (row : ThreeBlockIndex w) :
    Option (ThreeBlockVariable w) :=
  if h : exists e : ThreeBlockVariable w, e ∈ a.1 ∧ e.1.1 = row then
    some (Classical.choose h)
  else none

theorem validMatchingRowCode_eq_some_iff_mem
    {w : Type*} [Fintype w] [DecidableEq w]
    (a : ValidThreeBlockMatching w) (e : ThreeBlockVariable w) :
    validMatchingRowCode a e.1.1 = some e ↔ e ∈ a.1 := by
  classical
  constructor
  · intro hcode
    let hex : exists f : ThreeBlockVariable w,
        f ∈ a.1 ∧ f.1.1 = e.1.1 := by
      by_contra hnot
      simp [validMatchingRowCode, hnot] at hcode
    have hchoice := Classical.choose_spec hex
    have heq : Classical.choose hex = e := by
      exact Option.some.inj (by
        simpa [validMatchingRowCode, hex] using hcode)
    rw [← heq]
    exact hchoice.1
  · intro he
    let hex : exists f : ThreeBlockVariable w,
        f ∈ a.1 ∧ f.1.1 = e.1.1 := ⟨e, he, rfl⟩
    have hchoice := Classical.choose_spec hex
    have heq : Classical.choose hex = e := by
      exact a.property.1 hchoice.1 he hchoice.2
    simp [validMatchingRowCode, hex, heq]

/-- The row code recovers a valid matching, so no matching certificate is
hidden in the counting argument. -/
theorem validMatchingRowCode_injective
    {w : Type*} [Fintype w] [DecidableEq w] :
    Function.Injective
      (fun a : ValidThreeBlockMatching w => validMatchingRowCode a) := by
  classical
  intro a b hab
  change validMatchingRowCode a = validMatchingRowCode b at hab
  apply Subtype.ext
  ext e
  calc
    e ∈ a.1 ↔ validMatchingRowCode a e.1.1 = some e :=
      (validMatchingRowCode_eq_some_iff_mem a e).symm
    _ ↔ validMatchingRowCode b e.1.1 = some e := by
      rw [congrFun hab e.1.1]
    _ ↔ e ∈ b.1 := validMatchingRowCode_eq_some_iff_mem b e

/-- A precise function-space cardinality bound for valid matchings. -/
theorem card_validThreeBlockMatching_le_rowCodes
    {w : Type*} [Fintype w] [DecidableEq w] :
    Fintype.card (ValidThreeBlockMatching w) <=
      (Fintype.card (ThreeBlockVariable w) + 1) ^
        Fintype.card (ThreeBlockIndex w) := by
  calc
    Fintype.card (ValidThreeBlockMatching w) <=
        Fintype.card
          (ThreeBlockIndex w -> Option (ThreeBlockVariable w)) :=
      Fintype.card_le_of_injective _ validMatchingRowCode_injective
    _ = _ := by rw [Fintype.card_fun, Fintype.card_option]

/-- The fresh-variable subtype has at most one label per ordered row-column
pair. -/
theorem card_threeBlockVariable_le_index_sq
    {w : Type*} [Fintype w] [DecidableEq w] :
    Fintype.card (ThreeBlockVariable w) <=
      Fintype.card (ThreeBlockIndex w) *
        Fintype.card (ThreeBlockIndex w) := by
  simpa [ThreeBlockVariable, Fintype.card_prod] using
    (Fintype.card_subtype_le
      (fun e : ThreeBlockIndex w × ThreeBlockIndex w =>
        threeBlockFresh e.1 e.2))

/-- Coarse paper-scale form: with `N=3W`, valid matchings are at most
`(N^2+1)^N`.  Taking logs costs only `O(W log W)`. -/
theorem card_validThreeBlockMatching_le_indexPolynomial
    {w : Type*} [Fintype w] [DecidableEq w] :
    Fintype.card (ValidThreeBlockMatching w) <=
      (Fintype.card (ThreeBlockIndex w) *
          Fintype.card (ThreeBlockIndex w) + 1) ^
        Fintype.card (ThreeBlockIndex w) := by
  exact (card_validThreeBlockMatching_le_rowCodes (w := w)).trans
    (Nat.pow_le_pow_left
      (Nat.add_le_add_right
        (card_threeBlockVariable_le_index_sq (w := w)) 1)
      (Fintype.card (ThreeBlockIndex w)))

end BernoulliSection9
