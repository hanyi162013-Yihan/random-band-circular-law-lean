import BernoulliSection9.TwoSquareBlock
import BernoulliLinearAlgebra.ThreeBlockTerminal
import Mathlib.Tactic

/-!
# Canonical reindexing for the terminal RRQR residual

This file contains no RRQR or probabilistic assumption.  Starting from a
row (or column) equivalence whose first summand is the selected outer pivot,
it canonically partitions the complementary outer coordinates into their
left and right packet blocks.  The two partitions are then combined with
the untouched centre and with `balancedResidualRowEquiv` /
`balancedResidualColEquiv`.

The resulting full row and column equivalences put the literal terminal
matrix in exactly the coordinate order required by `TerminalCUR` and the
two conditional Cook squares.  All constructions are definitions from the
RRQR selections; no reindex or mask certificate is requested from a final
caller.
-/

noncomputable section

namespace BernoulliSection9

open BernoulliLinearAlgebra

/-! ## Splitting an outer complement into left and right coordinates -/

/-- A complementary outer coordinate belongs to the left packet block. -/
def OuterResidualIsLeft {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) (j : Fin q) : Prop :=
  ∃ i : Fin W, e (Sum.inr j) = Sum.inl i

/-- Left complementary coordinates, as a finite subtype. -/
abbrev OuterResidualLeft {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :=
  {j : Fin q // OuterResidualIsLeft e j}

/-- Right complementary coordinates, as the complementary finite subtype. -/
abbrev OuterResidualRight {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :=
  {j : Fin q // ¬ OuterResidualIsLeft e j}

noncomputable instance outerResidualLeftFintype {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    Fintype (OuterResidualLeft e) := Fintype.ofFinite _

noncomputable instance outerResidualRightFintype {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    Fintype (OuterResidualRight e) := Fintype.ofFinite _

/-- Number of unselected left outer coordinates. -/
def outerResidualLeftCount {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) : Nat :=
  Fintype.card (OuterResidualLeft e)

/-- Number of unselected right outer coordinates. -/
def outerResidualRightCount {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) : Nat :=
  Fintype.card (OuterResidualRight e)

/-- The left/right subtypes are a disjoint exhaustive partition of the
outer complement. -/
def outerResidualSubtypeEquiv {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    OuterResidualLeft e ⊕ OuterResidualRight e ≃ Fin q :=
  Equiv.ofBijective
    (fun u => match u with
      | Sum.inl j => j.1
      | Sum.inr j => j.1)
    ⟨by
      intro u v huv
      rcases u with u | u <;> rcases v with v | v
      · exact congrArg Sum.inl (Subtype.ext huv)
      · exfalso
        have huv' : (u : Fin q) = (v : Fin q) := by simpa using huv
        exact v.2 (huv' ▸ u.2)
      · exfalso
        have huv' : (u : Fin q) = (v : Fin q) := by simpa using huv
        exact u.2 (huv' ▸ v.2)
      · exact congrArg Sum.inr (Subtype.ext huv),
    by
      intro j
      by_cases hj : OuterResidualIsLeft e j
      · exact ⟨Sum.inl ⟨j, hj⟩, rfl⟩
      · exact ⟨Sum.inr ⟨j, hj⟩, rfl⟩⟩

/-- Canonical finite-coordinate version of the left/right partition. -/
def outerResidualFinEquiv {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    Fin (outerResidualLeftCount e) ⊕
        Fin (outerResidualRightCount e) ≃ Fin q :=
  (Equiv.sumCongr
      (Fintype.equivFin (OuterResidualLeft e)).symm
      (Fintype.equivFin (OuterResidualRight e)).symm).trans
    (outerResidualSubtypeEquiv e)

theorem outerResidualFinEquiv_inl_isLeft {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i : Fin (outerResidualLeftCount e)) :
    OuterResidualIsLeft e (outerResidualFinEquiv e (Sum.inl i)) := by
  change OuterResidualIsLeft e
    ((Fintype.equivFin (OuterResidualLeft e)).symm i).1
  exact ((Fintype.equivFin (OuterResidualLeft e)).symm i).property

theorem outerResidualFinEquiv_inr_isRight {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i : Fin (outerResidualRightCount e)) :
    ¬ OuterResidualIsLeft e (outerResidualFinEquiv e (Sum.inr i)) := by
  change ¬ OuterResidualIsLeft e
    ((Fintype.equivFin (OuterResidualRight e)).symm i).1
  exact ((Fintype.equivFin (OuterResidualRight e)).symm i).property

/-- The actual complementary outer-coordinate embedding, ordered as
left coordinates followed by right coordinates. -/
def outerResidualEmbedding {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    (Fin (outerResidualLeftCount e) ⊕
      Fin (outerResidualRightCount e)) ↪ (Fin W ⊕ Fin W) where
  toFun u := e (Sum.inr (outerResidualFinEquiv e u))
  inj' := by
    intro u v huv
    apply (outerResidualFinEquiv e).injective
    exact Sum.inr.inj (e.injective huv)

theorem outerResidualEmbedding_inl {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i : Fin (outerResidualLeftCount e)) :
    ∃ j : Fin W, outerResidualEmbedding e (Sum.inl i) = Sum.inl j := by
  exact outerResidualFinEquiv_inl_isLeft e i

theorem outerResidualEmbedding_inr {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i : Fin (outerResidualRightCount e)) :
    ∃ j : Fin W, outerResidualEmbedding e (Sum.inr i) = Sum.inr j := by
  rcases h : e (Sum.inr (outerResidualFinEquiv e (Sum.inr i))) with j | j
  · exfalso
    exact (outerResidualFinEquiv_inr_isRight e i) ⟨j, h⟩
  · refine ⟨j, ?_⟩
    change e (Sum.inr (outerResidualFinEquiv e (Sum.inr i))) = Sum.inr j
    exact h

/-- There are at most `W` remaining coordinates on the left. -/
theorem outerResidualLeftCount_le {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    outerResidualLeftCount e ≤ W := by
  let f : Fin (outerResidualLeftCount e) ↪ Fin W :=
    { toFun := fun i ↦ Classical.choose (outerResidualEmbedding_inl e i)
      inj' := by
        intro i j hij
        apply Sum.inl.inj
        apply (outerResidualEmbedding e).injective
        calc
          outerResidualEmbedding e (Sum.inl i) =
              Sum.inl (Classical.choose (outerResidualEmbedding_inl e i)) :=
            Classical.choose_spec (outerResidualEmbedding_inl e i)
          _ = Sum.inl (Classical.choose (outerResidualEmbedding_inl e j)) :=
            congrArg Sum.inl hij
          _ = outerResidualEmbedding e (Sum.inl j) :=
            (Classical.choose_spec (outerResidualEmbedding_inl e j)).symm }
  simpa using Fintype.card_le_of_injective f f.injective

/-- There are at most `W` remaining coordinates on the right. -/
theorem outerResidualRightCount_le {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    outerResidualRightCount e ≤ W := by
  let f : Fin (outerResidualRightCount e) ↪ Fin W :=
    { toFun := fun i ↦ Classical.choose (outerResidualEmbedding_inr e i)
      inj' := by
        intro i j hij
        apply Sum.inr.inj
        apply (outerResidualEmbedding e).injective
        calc
          outerResidualEmbedding e (Sum.inr i) =
              Sum.inr (Classical.choose (outerResidualEmbedding_inr e i)) :=
            Classical.choose_spec (outerResidualEmbedding_inr e i)
          _ = Sum.inr (Classical.choose (outerResidualEmbedding_inr e j)) :=
            congrArg Sum.inr hij
          _ = outerResidualEmbedding e (Sum.inr j) :=
            (Classical.choose_spec (outerResidualEmbedding_inr e j)).symm }
  simpa using Fintype.card_le_of_injective f f.injective

/-- The two side counts add up to the whole outer complement. -/
theorem outerResidualCount_add {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    outerResidualLeftCount e + outerResidualRightCount e = q := by
  have h := Fintype.card_congr (outerResidualFinEquiv e)
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  exact h

/-- Every outer complement has size at most `2W`. -/
theorem outerResidualCount_add_le_two_mul {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    outerResidualLeftCount e + outerResidualRightCount e ≤ 2 * W := by
  have hcard := Fintype.card_congr e
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  rw [outerResidualCount_add e]
  omega

/-! ## Embedding the residual mask into the literal three-block mask -/

/-- Rebracket the paper-style `(L ⊕ R) ⊕ C` packet coordinates into
the Boolean outer coordinates used by `ThreeBlockIndex`. -/
def packetIndexEquiv (W : Nat) :
    ((Fin W ⊕ Fin W) ⊕ Fin W) ≃ ThreeBlockIndex (Fin W) :=
  Equiv.sumCongr (threeBlockOuterEquiv (Fin W)).symm (Equiv.refl (Fin W))

/-- The complementary outer coordinates together with the untouched centre,
embedded in the literal terminal index type. -/
def terminalResidualIndexEmbedding {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    ResidualIndex (outerResidualLeftCount e)
        (outerResidualRightCount e) W ↪ ThreeBlockIndex (Fin W) where
  toFun u := packetIndexEquiv W <| match u with
    | Sum.inl j => Sum.inl (outerResidualEmbedding e j)
    | Sum.inr k => Sum.inr k
  inj' := by
    intro u v huv
    apply (packetIndexEquiv W).injective at huv
    rcases u with u | u <;> rcases v with v | v
    · exact congrArg Sum.inl ((outerResidualEmbedding e).injective
        (Sum.inl.inj huv))
    · cases huv
    · cases huv
    · exact congrArg Sum.inr (Sum.inr.inj huv)

theorem terminalResidualIndexEmbedding_left {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i : Fin (outerResidualLeftCount e)) :
    ∃ j : Fin W,
      terminalResidualIndexEmbedding e (Sum.inl (Sum.inl i)) =
        Sum.inl (false, j) := by
  rcases outerResidualEmbedding_inl e i with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  change packetIndexEquiv W
      (Sum.inl (outerResidualEmbedding e (Sum.inl i))) =
    Sum.inl (false, j)
  rw [hj]
  rfl

theorem terminalResidualIndexEmbedding_right {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i : Fin (outerResidualRightCount e)) :
    ∃ j : Fin W,
      terminalResidualIndexEmbedding e (Sum.inl (Sum.inr i)) =
        Sum.inl (true, j) := by
  rcases outerResidualEmbedding_inr e i with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  change packetIndexEquiv W
      (Sum.inl (outerResidualEmbedding e (Sum.inr i))) =
    Sum.inl (true, j)
  rw [hj]
  rfl

@[simp] theorem terminalResidualIndexEmbedding_center {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) (i : Fin W) :
    terminalResidualIndexEmbedding e (Sum.inr i) = Sum.inr i := rfl

/-- The abstract residual seven-block mask is literally a submask of the
three-block packet mask after the canonical left/right reindexing. -/
theorem terminalResidual_fresh {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i : ResidualIndex (outerResidualLeftCount rowEquiv)
      (outerResidualRightCount rowEquiv) W)
    (j : ResidualIndex (outerResidualLeftCount colEquiv)
      (outerResidualRightCount colEquiv) W)
    (h : residualFresh i j) :
    threeBlockFresh (terminalResidualIndexEmbedding rowEquiv i)
      (terminalResidualIndexEmbedding colEquiv j) := by
  rcases i with (i | i) | i <;> rcases j with (j | j) | j
  · rcases terminalResidualIndexEmbedding_left rowEquiv i with ⟨i', hi⟩
    rcases terminalResidualIndexEmbedding_left colEquiv j with ⟨j', hj⟩
    rw [hi, hj]
    exact threeBlockFresh_left_left i' j'
  · exact False.elim h
  · rcases terminalResidualIndexEmbedding_left rowEquiv i with ⟨i', hi⟩
    rw [hi, terminalResidualIndexEmbedding_center]
    exact threeBlockFresh_center_col _ _
  · exact False.elim h
  · rcases terminalResidualIndexEmbedding_right rowEquiv i with ⟨i', hi⟩
    rcases terminalResidualIndexEmbedding_right colEquiv j with ⟨j', hj⟩
    rw [hi, hj]
    exact threeBlockFresh_right_right i' j'
  · rcases terminalResidualIndexEmbedding_right rowEquiv i with ⟨i', hi⟩
    rw [hi, terminalResidualIndexEmbedding_center]
    exact threeBlockFresh_center_col _ _
  · rcases terminalResidualIndexEmbedding_left colEquiv j with ⟨j', hj⟩
    rw [terminalResidualIndexEmbedding_center, hj]
    exact threeBlockFresh_center_row _ _
  · rcases terminalResidualIndexEmbedding_right colEquiv j with ⟨j', hj⟩
    rw [terminalResidualIndexEmbedding_center, hj]
    exact threeBlockFresh_center_row _ _
  · simp

/-- Inject every abstract residual fresh entry into the actual iid packet
entry that occupies that row and column. -/
def terminalResidualFreshEntryEmbedding {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    ResidualFreshEntry
        (outerResidualLeftCount rowEquiv)
        (outerResidualRightCount rowEquiv)
        (outerResidualLeftCount colEquiv)
        (outerResidualRightCount colEquiv) W ↪
      ThreeBlockVariable (Fin W) where
  toFun p := ⟨
    (terminalResidualIndexEmbedding rowEquiv p.1.1,
      terminalResidualIndexEmbedding colEquiv p.1.2),
    terminalResidual_fresh rowEquiv colEquiv p.1.1 p.1.2 p.2⟩
  inj' := by
    intro p s hps
    apply Subtype.ext
    apply Prod.ext
    · exact (terminalResidualIndexEmbedding rowEquiv).injective
        (congrArg (fun x : ThreeBlockVariable (Fin W) => x.1.1) hps)
    · exact (terminalResidualIndexEmbedding colEquiv).injective
        (congrArg (fun x : ThreeBlockVariable (Fin W) => x.1.2) hps)

/-- Restriction of the literal packet iid family to all residual fresh
entries.  The two Cook squares are obtained from this family by the already
proved canonical restrictions in `TwoSquareRandomness`. -/
def IidSubgaussianFamily.terminalResidualFamily
    {Omega : Type*} [MeasurableSpace Omega] {mu : MeasureTheory.Measure Omega}
    {W r q : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    IidSubgaussianFamily Omega mu
      (ResidualFreshEntry
        (outerResidualLeftCount rowEquiv)
        (outerResidualRightCount rowEquiv)
        (outerResidualLeftCount colEquiv)
      (outerResidualRightCount colEquiv) W) :=
  X.reindex (terminalResidualFreshEntryEmbedding rowEquiv colEquiv)

/-! ## The full balanced pivot/residual equivalences -/

/-- Remaining left/right row and column counts satisfy the square-residual
identity required by the two-square construction. -/
theorem terminalResidual_sideCount_eq {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    outerResidualLeftCount rowEquiv + outerResidualRightCount rowEquiv =
      outerResidualLeftCount colEquiv + outerResidualRightCount colEquiv := by
  rw [outerResidualCount_add rowEquiv, outerResidualCount_add colEquiv]

/-- The balanced first-square dimension determined by the actual RRQR row
and column complements. -/
def terminalBalancedSize {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) : Nat :=
  balancedSquareSize W
    (outerResidualLeftCount rowEquiv)
    (outerResidualRightCount rowEquiv)
    (outerResidualLeftCount colEquiv)

/-- Canonical balanced ordering of all residual rows. -/
def terminalBalancedResidualRowEquiv {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    Fin (terminalBalancedSize rowEquiv colEquiv) ⊕
        Fin (W + outerResidualLeftCount rowEquiv +
          outerResidualRightCount rowEquiv -
            terminalBalancedSize rowEquiv colEquiv) ≃
      ResidualIndex (outerResidualLeftCount rowEquiv)
        (outerResidualRightCount rowEquiv) W :=
  balancedResidualRowEquiv
    (outerResidualLeftCount_le rowEquiv)
    (outerResidualLeftCount_le colEquiv)
    (terminalResidual_sideCount_eq rowEquiv colEquiv)
    (outerResidualCount_add_le_two_mul rowEquiv)

/-- Canonical balanced ordering of all residual columns. -/
def terminalBalancedResidualColEquiv {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    Fin (terminalBalancedSize rowEquiv colEquiv) ⊕
        Fin (W + outerResidualLeftCount rowEquiv +
          outerResidualRightCount rowEquiv -
            terminalBalancedSize rowEquiv colEquiv) ≃
      ResidualIndex (outerResidualLeftCount colEquiv)
        (outerResidualRightCount colEquiv) W :=
  balancedResidualColEquiv
    (outerResidualLeftCount_le rowEquiv)
    (outerResidualLeftCount_le colEquiv)
    (terminalResidual_sideCount_eq rowEquiv colEquiv)
    (outerResidualCount_add_le_two_mul rowEquiv)

/-- Full row equivalence: pivot first, followed by the two balanced residual
squares. -/
def terminalBalancedRowEquiv {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    Fin r ⊕
        (Fin (terminalBalancedSize rowEquiv colEquiv) ⊕
          Fin (W + outerResidualLeftCount rowEquiv +
            outerResidualRightCount rowEquiv -
              terminalBalancedSize rowEquiv colEquiv)) ≃
      ThreeBlockIndex (Fin W) :=
  (Equiv.sumCongr (Equiv.refl (Fin r))
      (terminalBalancedResidualRowEquiv rowEquiv colEquiv)).trans <|
    (Equiv.sumCongr (Equiv.refl (Fin r))
      (Equiv.sumCongr (outerResidualFinEquiv rowEquiv)
        (Equiv.refl (Fin W)))).trans <|
    (Equiv.sumAssoc (Fin r) (Fin q) (Fin W)).symm.trans <|
    (Equiv.sumCongr rowEquiv (Equiv.refl (Fin W))).trans <|
    packetIndexEquiv W

/-- Full column equivalence in the same balanced residual dimensions. -/
def terminalBalancedColEquiv {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    Fin r ⊕
        (Fin (terminalBalancedSize rowEquiv colEquiv) ⊕
          Fin (W + outerResidualLeftCount rowEquiv +
            outerResidualRightCount rowEquiv -
              terminalBalancedSize rowEquiv colEquiv)) ≃
      ThreeBlockIndex (Fin W) :=
  (Equiv.sumCongr (Equiv.refl (Fin r))
      (terminalBalancedResidualColEquiv rowEquiv colEquiv)).trans <|
    (Equiv.sumCongr (Equiv.refl (Fin r))
      (Equiv.sumCongr (outerResidualFinEquiv colEquiv)
        (Equiv.refl (Fin W)))).trans <|
    (Equiv.sumAssoc (Fin r) (Fin q) (Fin W)).symm.trans <|
    (Equiv.sumCongr colEquiv (Equiv.refl (Fin W))).trans <|
    packetIndexEquiv W

@[simp] theorem terminalBalancedRowEquiv_inl {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i : Fin r) :
    terminalBalancedRowEquiv rowEquiv colEquiv (Sum.inl i) =
      packetIndexEquiv W (Sum.inl (rowEquiv (Sum.inl i))) := rfl

@[simp] theorem terminalBalancedColEquiv_inl {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i : Fin r) :
    terminalBalancedColEquiv rowEquiv colEquiv (Sum.inl i) =
      packetIndexEquiv W (Sum.inl (colEquiv (Sum.inl i))) := rfl

@[simp] theorem terminalBalancedRowEquiv_inr {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i : Fin (terminalBalancedSize rowEquiv colEquiv) ⊕
      Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv)) :
    terminalBalancedRowEquiv rowEquiv colEquiv (Sum.inr i) =
      terminalResidualIndexEmbedding rowEquiv
        (terminalBalancedResidualRowEquiv rowEquiv colEquiv i) := by
  rcases hres : terminalBalancedResidualRowEquiv rowEquiv colEquiv i with j | j
  · simp [terminalBalancedRowEquiv, terminalResidualIndexEmbedding,
      outerResidualEmbedding, hres]
    rfl
  · simp [terminalBalancedRowEquiv, terminalResidualIndexEmbedding, hres]
    rfl

@[simp] theorem terminalBalancedColEquiv_inr {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i : Fin (terminalBalancedSize rowEquiv colEquiv) ⊕
      Fin (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv)) :
    terminalBalancedColEquiv rowEquiv colEquiv (Sum.inr i) =
      terminalResidualIndexEmbedding colEquiv
        (terminalBalancedResidualColEquiv rowEquiv colEquiv i) := by
  rcases hres : terminalBalancedResidualColEquiv rowEquiv colEquiv i with j | j
  · simp [terminalBalancedColEquiv, terminalResidualIndexEmbedding,
      outerResidualEmbedding, hres]
    rfl
  · simp [terminalBalancedColEquiv, terminalResidualIndexEmbedding, hres]
    rfl

end BernoulliSection9
