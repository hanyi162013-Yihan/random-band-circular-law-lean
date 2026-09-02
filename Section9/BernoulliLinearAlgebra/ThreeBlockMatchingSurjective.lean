import BernoulliLinearAlgebra.ThreeBlockMaskComparison
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Tactic

/-!
# Every outer square minor is realized by a valid three-block matching

For prescribed unmatched outer rows and columns, Hall's theorem supplies a
fresh matching on all remaining full coordinates.  The special seven-block
mask makes Hall's condition elementary: a set containing a central column,
or columns from both outer sides, sees every selected row; a set confined to
one outer side injects into the central rows coordinate by coordinate.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard

section TargetMatching

variable {w : Type*} [Fintype w] [DecidableEq w]

local instance threeBlockMatchingSurjectiveVariableDecidableEq :
    DecidableEq (ThreeBlockVariable w) := Classical.decEq _

/-- Full columns which should be occupied when the prescribed unmatched
outer column set is `b.1`. -/
def threeBlockTargetSelectedCols
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    Finset (ThreeBlockIndex w) :=
  Finset.univ \ b.1.image (fun j => (Sum.inl j : ThreeBlockIndex w))

/-- Full rows which should be occupied when the prescribed unmatched outer
row set is `b.2.1`. -/
def threeBlockTargetSelectedRows
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    Finset (ThreeBlockIndex w) :=
  Finset.univ \ b.2.1.image (fun i => (Sum.inl i : ThreeBlockIndex w))

theorem threeBlockTargetSelectedCols_mem_outer
    (b : SquareMinorIndex (ThreeBlockOuter w))
    (j : ThreeBlockOuter w) :
    (Sum.inl j : ThreeBlockIndex w) ∈ threeBlockTargetSelectedCols b ↔
      j ∉ b.1 := by
  simp [threeBlockTargetSelectedCols]

theorem threeBlockTargetSelectedRows_mem_outer
    (b : SquareMinorIndex (ThreeBlockOuter w))
    (i : ThreeBlockOuter w) :
    (Sum.inl i : ThreeBlockIndex w) ∈ threeBlockTargetSelectedRows b ↔
      i ∉ b.2.1 := by
  simp [threeBlockTargetSelectedRows]

@[simp] theorem threeBlockTargetSelectedCols_mem_center
    (b : SquareMinorIndex (ThreeBlockOuter w)) (j : w) :
    (Sum.inr j : ThreeBlockIndex w) ∈ threeBlockTargetSelectedCols b := by
  simp [threeBlockTargetSelectedCols]

@[simp] theorem threeBlockTargetSelectedRows_mem_center
    (b : SquareMinorIndex (ThreeBlockOuter w)) (i : w) :
    (Sum.inr i : ThreeBlockIndex w) ∈ threeBlockTargetSelectedRows b := by
  simp [threeBlockTargetSelectedRows]

theorem threeBlockTargetSelectedCols_card
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    (threeBlockTargetSelectedCols b).card =
      Fintype.card (ThreeBlockIndex w) - b.1.card := by
  rw [threeBlockTargetSelectedCols,
    Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ,
    Finset.card_image_of_injective _ Sum.inl_injective]

theorem threeBlockTargetSelectedRows_card
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    (threeBlockTargetSelectedRows b).card =
      Fintype.card (ThreeBlockIndex w) - b.2.1.card := by
  rw [threeBlockTargetSelectedRows,
    Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ,
    Finset.card_image_of_injective _ Sum.inl_injective]

/-- The selected row and column types have equal cardinality because the
prescribed minor is square. -/
theorem threeBlockTargetSelected_card_eq
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    Fintype.card ↑(threeBlockTargetSelectedCols b) =
      Fintype.card ↑(threeBlockTargetSelectedRows b) := by
  rw [Fintype.card_coe, Fintype.card_coe,
    threeBlockTargetSelectedCols_card,
    threeBlockTargetSelectedRows_card]
  exact congrArg (fun k => Fintype.card (ThreeBlockIndex w) - k)
    (mem_iff.mp b.2.2).symm

abbrev ThreeBlockTargetSelectedCol
    (b : SquareMinorIndex (ThreeBlockOuter w)) :=
  ↑(threeBlockTargetSelectedCols b)

abbrev ThreeBlockTargetSelectedRow
    (b : SquareMinorIndex (ThreeBlockOuter w)) :=
  ↑(threeBlockTargetSelectedRows b)

/-- Freshness as a relation from selected columns to selected rows. -/
def threeBlockTargetFreshRel
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    ThreeBlockTargetSelectedCol b → ThreeBlockTargetSelectedRow b → Prop :=
  fun j i => threeBlockFresh i.1 j.1

instance threeBlockTargetFreshRel_decidable
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    DecidableRel (threeBlockTargetFreshRel b) :=
  fun j i => inferInstanceAs (Decidable (threeBlockFresh i.1 j.1))

/-- The common `w`-coordinate of a full index. -/
def threeBlockIndexBase : ThreeBlockIndex w → w
  | Sum.inl (_, i) => i
  | Sum.inr i => i

/-- Every central row belongs to the prescribed selected-row type. -/
def threeBlockTargetCenterRow
    (b : SquareMinorIndex (ThreeBlockOuter w)) (i : w) :
    ThreeBlockTargetSelectedRow b :=
  ⟨Sum.inr i, threeBlockTargetSelectedRows_mem_center b i⟩

/-- Hall's cardinality condition for the selected seven-block mask. -/
theorem threeBlockTargetHallCondition
    (b : SquareMinorIndex (ThreeBlockOuter w))
    (A : Finset (ThreeBlockTargetSelectedCol b)) :
    A.card ≤
      ({i | ∃ j ∈ A, threeBlockTargetFreshRel b j i} :
        Finset (ThreeBlockTargetSelectedRow b)).card := by
  classical
  let N : Finset (ThreeBlockTargetSelectedRow b) :=
    {i | ∃ j ∈ A, threeBlockTargetFreshRel b j i}
  by_cases hcenter : ∃ j ∈ A, ∃ k : w,
      (j.1 : ThreeBlockIndex w) = Sum.inr k
  · rcases hcenter with ⟨j₀, hj₀, k, hk⟩
    have hN : N = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨j₀, hj₀, ?_⟩
      rw [threeBlockTargetFreshRel, hk]
      exact threeBlockFresh_center_col i.1 k
    rw [show ({i | ∃ j ∈ A, threeBlockTargetFreshRel b j i} :
        Finset (ThreeBlockTargetSelectedRow b)) = N by rfl, hN,
      Finset.card_univ]
    calc
      A.card ≤ Fintype.card (ThreeBlockTargetSelectedCol b) := by
        simpa using A.card_le_univ
      _ = Fintype.card (ThreeBlockTargetSelectedRow b) :=
        threeBlockTargetSelected_card_eq b
  · by_cases hleft : ∃ j ∈ A, ∃ k : w,
        (j.1 : ThreeBlockIndex w) = Sum.inl (false, k)
    · by_cases hright : ∃ j ∈ A, ∃ k : w,
          (j.1 : ThreeBlockIndex w) = Sum.inl (true, k)
      · rcases hleft with ⟨jL, hjL, kL, hkL⟩
        rcases hright with ⟨jR, hjR, kR, hkR⟩
        have hN : N = Finset.univ := by
          apply Finset.eq_univ_of_forall
          intro i
          simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hi : (i.1 : ThreeBlockIndex w) with o | k
          · rcases o with ⟨side, k⟩
            cases side
            · refine ⟨jL, hjL, ?_⟩
              simp [threeBlockTargetFreshRel, hi, hkL,
                threeBlockFresh]
            · refine ⟨jR, hjR, ?_⟩
              simp [threeBlockTargetFreshRel, hi, hkR,
                threeBlockFresh]
          · refine ⟨jL, hjL, ?_⟩
            simp [threeBlockTargetFreshRel, hi,
              threeBlockFresh]
        rw [show ({i | ∃ j ∈ A, threeBlockTargetFreshRel b j i} :
            Finset (ThreeBlockTargetSelectedRow b)) = N by rfl,
          hN, Finset.card_univ]
        calc
          A.card ≤ Fintype.card (ThreeBlockTargetSelectedCol b) := by
            simpa using A.card_le_univ
          _ = Fintype.card (ThreeBlockTargetSelectedRow b) :=
            threeBlockTargetSelected_card_eq b
      · have hallLeft : ∀ j ∈ A, ∃ k : w,
            (j.1 : ThreeBlockIndex w) = Sum.inl (false, k) := by
          intro j hj
          rcases hidx : (j.1 : ThreeBlockIndex w) with o | k
          · rcases o with ⟨side, k⟩
            cases side
            · exact ⟨k, rfl⟩
            · exact False.elim (hright ⟨j, hj, k, hidx⟩)
          · exact False.elim (hcenter ⟨j, hj, k, hidx⟩)
        let f : ThreeBlockTargetSelectedCol b →
            ThreeBlockTargetSelectedRow b :=
          fun j => threeBlockTargetCenterRow b (threeBlockIndexBase j.1)
        apply Finset.card_le_card_of_injOn f
        · intro j hj
          rw [Finset.mem_coe, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, ⟨j, hj, by
            simp [f, threeBlockTargetFreshRel,
              threeBlockTargetCenterRow, threeBlockFresh]⟩⟩
        · intro j hj j' hj' heq
          rcases hallLeft j hj with ⟨k, hk⟩
          rcases hallLeft j' hj' with ⟨k', hk'⟩
          have hbase : threeBlockIndexBase j.1 =
              threeBlockIndexBase j'.1 := by
            exact Sum.inr_injective
              (congrArg (fun i : ThreeBlockTargetSelectedRow b => i.1) heq)
          apply Subtype.ext
          rw [hk, hk']
          congr
          calc
            k = threeBlockIndexBase j.1 := by rw [hk]; rfl
            _ = threeBlockIndexBase j'.1 := hbase
            _ = k' := by rw [hk']; rfl
    · have hallRight : ∀ j ∈ A, ∃ k : w,
          (j.1 : ThreeBlockIndex w) = Sum.inl (true, k) := by
        intro j hj
        rcases hidx : (j.1 : ThreeBlockIndex w) with o | k
        · rcases o with ⟨side, k⟩
          cases side
          · exact False.elim (hleft ⟨j, hj, k, hidx⟩)
          · exact ⟨k, rfl⟩
        · exact False.elim (hcenter ⟨j, hj, k, hidx⟩)
      let f : ThreeBlockTargetSelectedCol b →
          ThreeBlockTargetSelectedRow b :=
        fun j => threeBlockTargetCenterRow b (threeBlockIndexBase j.1)
      apply Finset.card_le_card_of_injOn f
      · intro j hj
        rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, ⟨j, hj, by
          simp [f, threeBlockTargetFreshRel,
            threeBlockTargetCenterRow, threeBlockFresh]⟩⟩
      · intro j hj j' hj' heq
        rcases hallRight j hj with ⟨k, hk⟩
        rcases hallRight j' hj' with ⟨k', hk'⟩
        have hbase : threeBlockIndexBase j.1 =
            threeBlockIndexBase j'.1 := by
          exact Sum.inr_injective
            (congrArg (fun i : ThreeBlockTargetSelectedRow b => i.1) heq)
        apply Subtype.ext
        rw [hk, hk']
        congr
        calc
          k = threeBlockIndexBase j.1 := by rw [hk]; rfl
          _ = threeBlockIndexBase j'.1 := hbase
          _ = k' := by rw [hk']; rfl

/-- Hall's theorem supplies an injective fresh matching from all prescribed
selected columns into the selected rows. -/
theorem exists_threeBlockTargetMatchingFunction
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    ∃ f : ThreeBlockTargetSelectedCol b →
        ThreeBlockTargetSelectedRow b,
      Function.Injective f ∧ ∀ j, threeBlockTargetFreshRel b j (f j) := by
  exact (Fintype.all_card_le_filter_rel_iff_exists_injective
    (threeBlockTargetFreshRel b)).1 (threeBlockTargetHallCondition b)

def threeBlockTargetMatchingFunction
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    ThreeBlockTargetSelectedCol b → ThreeBlockTargetSelectedRow b :=
  Classical.choose (exists_threeBlockTargetMatchingFunction b)

theorem threeBlockTargetMatchingFunction_injective
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    Function.Injective (threeBlockTargetMatchingFunction b) :=
  (Classical.choose_spec (exists_threeBlockTargetMatchingFunction b)).1

theorem threeBlockTargetMatchingFunction_fresh
    (b : SquareMinorIndex (ThreeBlockOuter w)) (j) :
    threeBlockFresh (threeBlockTargetMatchingFunction b j).1 j.1 :=
  (Classical.choose_spec (exists_threeBlockTargetMatchingFunction b)).2 j

theorem threeBlockTargetMatchingFunction_surjective
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    Function.Surjective (threeBlockTargetMatchingFunction b) := by
  exact ((Fintype.bijective_iff_injective_and_card
    (threeBlockTargetMatchingFunction b)).2
      ⟨threeBlockTargetMatchingFunction_injective b,
        threeBlockTargetSelected_card_eq b⟩).2

/-- The actual fresh edge associated with a selected target column. -/
def threeBlockTargetMatchingEdge
    (b : SquareMinorIndex (ThreeBlockOuter w))
    (j : ThreeBlockTargetSelectedCol b) : ThreeBlockVariable w :=
  ⟨((threeBlockTargetMatchingFunction b j).1, j.1),
    threeBlockTargetMatchingFunction_fresh b j⟩

theorem threeBlockTargetMatchingEdge_injective
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    Function.Injective (threeBlockTargetMatchingEdge b) := by
  intro j j' h
  apply Subtype.ext
  exact congrArg (fun e : ThreeBlockVariable w => e.1.2) h

/-- The valid matching realizing the prescribed minor, before validity is
packaged. -/
def threeBlockTargetMatching
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    Finset (ThreeBlockVariable w) :=
  Finset.univ.image (threeBlockTargetMatchingEdge b)

theorem threeBlockTargetMatchingCols_eq
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    threeBlockMatchingCols (threeBlockTargetMatching b) =
      threeBlockTargetSelectedCols b := by
  ext j
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨e, he, hcol⟩
    rcases Finset.mem_image.mp he with ⟨j', -, hje⟩
    rw [← hcol, ← hje]
    exact j'.2
  · intro hj
    let j' : ThreeBlockTargetSelectedCol b := ⟨j, hj⟩
    apply Finset.mem_image.mpr
    refine ⟨threeBlockTargetMatchingEdge b j',
      Finset.mem_image.mpr ⟨j', Finset.mem_univ _, rfl⟩, ?_⟩
    rfl

theorem threeBlockTargetMatchingRows_eq
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    threeBlockMatchingRows (threeBlockTargetMatching b) =
      threeBlockTargetSelectedRows b := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨e, he, hrow⟩
    rcases Finset.mem_image.mp he with ⟨j, -, hje⟩
    rw [← hrow, ← hje]
    exact (threeBlockTargetMatchingFunction b j).2
  · intro hi
    let i' : ThreeBlockTargetSelectedRow b := ⟨i, hi⟩
    rcases threeBlockTargetMatchingFunction_surjective b i' with ⟨j, hj⟩
    apply Finset.mem_image.mpr
    refine ⟨threeBlockTargetMatchingEdge b j,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    exact congrArg Subtype.val hj

theorem threeBlockTargetMatching_isValid
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    IsValidThreeBlockMatching (threeBlockTargetMatching b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he e' he' hrow
    rcases Finset.mem_image.mp he with ⟨j, -, hje⟩
    rcases Finset.mem_image.mp he' with ⟨j', -, hje'⟩
    have hf : threeBlockTargetMatchingFunction b j =
        threeBlockTargetMatchingFunction b j' := by
      apply Subtype.ext
      calc
        (threeBlockTargetMatchingFunction b j).1 =
            (threeBlockTargetMatchingEdge b j).1.1 := rfl
        _ = e.1.1 :=
          congrArg (fun x : ThreeBlockVariable w => x.1.1) hje
        _ = e'.1.1 := hrow
        _ = (threeBlockTargetMatchingEdge b j').1.1 :=
          (congrArg (fun x : ThreeBlockVariable w => x.1.1) hje').symm
        _ = (threeBlockTargetMatchingFunction b j').1 := rfl
    have hj := threeBlockTargetMatchingFunction_injective b hf
    rw [← hje, ← hje', hj]
  · intro e he e' he' hcol
    rcases Finset.mem_image.mp he with ⟨j, -, hje⟩
    rcases Finset.mem_image.mp he' with ⟨j', -, hje'⟩
    have hj : j = j' := by
      apply Subtype.ext
      calc
        j.1 = (threeBlockTargetMatchingEdge b j).1.2 := rfl
        _ = e.1.2 :=
          congrArg (fun x : ThreeBlockVariable w => x.1.2) hje
        _ = e'.1.2 := hcol
        _ = (threeBlockTargetMatchingEdge b j').1.2 :=
          (congrArg (fun x : ThreeBlockVariable w => x.1.2) hje').symm
        _ = j'.1 := rfl
    rw [← hje, ← hje', hj]
  · intro i
    rw [threeBlockTargetMatchingRows_eq]
    exact threeBlockTargetSelectedRows_mem_center b i
  · intro j
    rw [threeBlockTargetMatchingCols_eq]
    exact threeBlockTargetSelectedCols_mem_center b j

def threeBlockTargetValidMatching
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    ValidThreeBlockMatching w :=
  ⟨threeBlockTargetMatching b, threeBlockTargetMatching_isValid b⟩

theorem threeBlockTargetUnmatchedOuterCols_eq
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    threeBlockUnmatchedOuterCols (threeBlockTargetMatching b) = b.1 := by
  ext j
  rw [threeBlockUnmatchedOuterCols, Finset.mem_filter,
    threeBlockTargetMatchingCols_eq]
  simp [threeBlockTargetSelectedCols_mem_outer]

theorem threeBlockTargetUnmatchedOuterRows_eq
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    threeBlockUnmatchedOuterRows (threeBlockTargetMatching b) = b.2.1 := by
  ext i
  rw [threeBlockUnmatchedOuterRows, Finset.mem_filter,
    threeBlockTargetMatchingRows_eq]
  simp [threeBlockTargetSelectedRows_mem_outer]

theorem threeBlockTargetMatchingMinorIndex_eq
    (b : SquareMinorIndex (ThreeBlockOuter w)) :
    threeBlockMatchingMinorIndex (threeBlockTargetValidMatching b) = b := by
  apply Sigma.subtype_ext
  · exact threeBlockTargetUnmatchedOuterCols_eq b
  · exact threeBlockTargetUnmatchedOuterRows_eq b

/-- Every square minor is represented by at least one genuine valid
three-block matching. -/
theorem threeBlockMatchingMinorIndex_surjective :
    Function.Surjective
      (threeBlockMatchingMinorIndex : ValidThreeBlockMatching w →
        SquareMinorIndex (ThreeBlockOuter w)) := by
  intro b
  exact ⟨threeBlockTargetValidMatching b,
    threeBlockTargetMatchingMinorIndex_eq b⟩

end TargetMatching

end BernoulliLinearAlgebra
