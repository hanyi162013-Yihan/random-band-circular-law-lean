import Mathlib.Tactic

/-!
# The two complete residual squares

This is the arithmetic core of (9.24)--(9.27).  After deleting equally many
outer rows and columns, `a,b` are the left/right row counts and `c,e` the
left/right column counts.  The explicit `balancedSquareSize` below is an
integer in the intersection (9.26); it avoids any choice principle at the
probabilistic exposure step.
-/

namespace BernoulliSection9

/-- An explicit choice for `n₁` in (9.26). -/
def balancedSquareSize (W a b c : ℕ) : ℕ :=
  max (max a c) ((W + a + b) / 3)

theorem balancedSquareSize_ge_leftRows (W a b c : ℕ) :
    a ≤ balancedSquareSize W a b c := by
  exact (le_max_left a c).trans (le_max_left (max a c) ((W + a + b) / 3))

theorem balancedSquareSize_ge_leftCols (W a b c : ℕ) :
    c ≤ balancedSquareSize W a b c := by
  exact (le_max_right a c).trans (le_max_left (max a c) ((W + a + b) / 3))

/-- The explicit choice lies in the mask-feasible interval
`[max(a,c), W + min(a,c)]`. -/
theorem balancedSquareSize_le_maskUpper
    {W a b c e : ℕ}
    (ha : a ≤ W) (hc : c ≤ W)
    (hs : a + b = c + e) (hsW : a + b ≤ 2 * W) :
    balancedSquareSize W a b c ≤ W + min a c := by
  unfold balancedSquareSize
  rw [max_le_iff]
  constructor
  · rw [max_le_iff]
    omega
  · have hres : W + a + b ≤ 3 * W := by omega
    have hthird : (W + a + b) / 3 ≤ W := by omega
    omega

/-- Lower balanced-size inequality, equivalent to
`n_res / 3 - 1 ≤ n₁` up to the paper's integer rounding allowance. -/
theorem residualSize_le_three_mul_balanced_add_two
    (W a b c : ℕ) :
    W + a + b ≤ 3 * balancedSquareSize W a b c + 2 := by
  unfold balancedSquareSize
  have h : (W + a + b) / 3 ≤
      max (max a c) ((W + a + b) / 3) := le_max_right _ _
  omega

/-- Upper balanced-size inequality, stronger than the upper endpoint in
(9.26): `3 n₁ ≤ 2 n_res`. -/
theorem three_mul_balanced_le_two_mul_residual
    {W a b c e : ℕ}
    (hs : a + b = c + e) (hsW : a + b ≤ 2 * W) :
    3 * balancedSquareSize W a b c ≤ 2 * (W + a + b) := by
  unfold balancedSquareSize
  rw [max_def]
  split_ifs with h
  · have hac : max a c ≤ a + b := by
      rw [max_le_iff]
      constructor
      · omega
      · omega
    omega
  · have hdiv : 3 * ((W + a + b) / 3) ≤ W + a + b := by omega
    omega

/-- Package of the two square sizes and the central row/column counts used
to form the first square. -/
structure TwoSquareDimensions where
  nResidual : ℕ
  nFirst : ℕ
  nSecond : ℕ
  centralRowsFirst : ℕ
  centralColsFirst : ℕ
  nResidual_eq : nResidual = nFirst + nSecond
  firstRows_eq : nFirst = centralRowsFirst
  firstCols_eq : nFirst = centralColsFirst

/-- The actual dimension data from (9.24)--(9.27).  `centralRowsFirst` and
`centralColsFirst` include the already-retained left outer coordinates; the
subtraction lemmas below recover the numbers of central coordinates added. -/
def twoSquareDimensions (W a b c : ℕ) (hc : c ≤ W) : TwoSquareDimensions where
  nResidual := W + a + b
  nFirst := balancedSquareSize W a b c
  nSecond := W + a + b - balancedSquareSize W a b c
  centralRowsFirst := balancedSquareSize W a b c
  centralColsFirst := balancedSquareSize W a b c
  nResidual_eq := by
    have h : balancedSquareSize W a b c ≤ W + a + b := by
      unfold balancedSquareSize
      rw [max_le_iff, max_le_iff]
      constructor
      · omega
      · exact Nat.div_le_self _ _
    omega
  firstRows_eq := rfl
  firstCols_eq := rfl

/-- `x = n₁-a` and `y = n₁-c` are genuine natural counts. -/
theorem centralCounts_spec (W a b c : ℕ) :
    a + (balancedSquareSize W a b c - a) = balancedSquareSize W a b c ∧
    c + (balancedSquareSize W a b c - c) = balancedSquareSize W a b c := by
  have ha := balancedSquareSize_ge_leftRows W a b c
  have hc := balancedSquareSize_ge_leftCols W a b c
  constructor
  · omega
  · omega

/-- Neither first-square central count exceeds the available `W` central
coordinates. -/
theorem centralCounts_le_W
    {W a b c e : ℕ}
    (ha : a ≤ W) (hc : c ≤ W)
    (hs : a + b = c + e) (hsW : a + b ≤ 2 * W) :
    balancedSquareSize W a b c - a ≤ W ∧
    balancedSquareSize W a b c - c ≤ W := by
  have hupper := balancedSquareSize_le_maskUpper ha hc hs hsW
  have hmin_a : min a c ≤ a := min_le_left _ _
  have hmin_c : min a c ≤ c := min_le_right _ _
  constructor <;> omega

/-! ## Literal row/column partitions and the fresh mask -/

/-- Residual coordinates: remaining left coordinates, remaining right
coordinates, and the full central block. -/
abbrev ResidualIndex (left right W : ℕ) :=
  (Fin left ⊕ Fin right) ⊕ Fin W

/-- The residual seven-block mask.  Its only forbidden rectangles are
left-row/right-column and right-row/left-column. -/
def residualFresh {a b c e W : ℕ} :
    ResidualIndex a b W → ResidualIndex c e W → Prop
  | Sum.inl (Sum.inl _), Sum.inl (Sum.inr _) => False
  | Sum.inl (Sum.inr _), Sum.inl (Sum.inl _) => False
  | _, _ => True

/-- The first `x` central coordinates. -/
def centralInitialEmbedding {W x : ℕ} (hx : x ≤ W) : Fin x ↪ Fin W :=
  Fin.castLEEmb hx

/-- The complementary tail of the central coordinates. -/
def centralTailEmbedding {W x : ℕ} (hx : x ≤ W) : Fin (W - x) ↪ Fin W where
  toFun i := ⟨x + i, by omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val hij)

/-- First-square rows (or columns): all left residual coordinates followed
by the first `x` central coordinates. -/
def firstPartitionEmbedding {a b W x : ℕ} (hx : x ≤ W) :
    (Fin a ⊕ Fin x) ↪ ResidualIndex a b W where
  toFun
    | Sum.inl i => Sum.inl (Sum.inl i)
    | Sum.inr i => Sum.inr (centralInitialEmbedding hx i)
  inj' := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · simpa using hij
    · cases hij
    · cases hij
    · simpa using hij

/-- Second-square rows (or columns): all right residual coordinates followed
by the complementary central tail. -/
def secondPartitionEmbedding {a b W x : ℕ} (hx : x ≤ W) :
    (Fin b ⊕ Fin (W - x)) ↪ ResidualIndex a b W where
  toFun
    | Sum.inl i => Sum.inl (Sum.inr i)
    | Sum.inr i => Sum.inr (centralTailEmbedding hx i)
  inj' := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · simpa using hij
    · cases hij
    · cases hij
    · simpa using hij

theorem centralInitial_ne_centralTail {W x : ℕ} (hx : x ≤ W)
    (i : Fin x) (j : Fin (W - x)) :
    centralInitialEmbedding hx i ≠ centralTailEmbedding hx j := by
  intro hij
  have hval := congrArg Fin.val hij
  change i.val = x + j.val at hval
  omega

/-- The two row (or column) embeddings are disjoint. -/
theorem partitionEmbedding_disjoint {a b W x : ℕ} (hx : x ≤ W) :
    Disjoint (Set.range (firstPartitionEmbedding (a := a) (b := b) hx))
      (Set.range (secondPartitionEmbedding (a := a) (b := b) hx)) := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  rcases hz₁ with ⟨i, rfl⟩
  rcases hz₂ with ⟨j, hij⟩
  rcases i with i | i <;> rcases j with j | j
  · cases hij
  · cases hij
  · cases hij
  · exact centralInitial_ne_centralTail hx i j ((Sum.inr.inj hij).symm)

/-- The two row (or column) embeddings cover every residual coordinate. -/
theorem partitionEmbedding_cover {a b W x : ℕ} (hx : x ≤ W) :
    Set.range (firstPartitionEmbedding (a := a) (b := b) hx) ∪
      Set.range (secondPartitionEmbedding (a := a) (b := b) hx) = Set.univ := by
  ext z
  simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
  rcases z with (i | i) | k
  · exact Or.inl ⟨Sum.inl i, rfl⟩
  · exact Or.inr ⟨Sum.inl i, rfl⟩
  · by_cases hk : k.val < x
    · let i : Fin x := ⟨k.val, hk⟩
      exact Or.inl ⟨Sum.inr i, by
        apply congrArg Sum.inr
        apply Fin.ext
        rfl⟩
    · have hxk : x ≤ k.val := Nat.le_of_not_gt hk
      let j : Fin (W - x) := ⟨k.val - x, by omega⟩
      exact Or.inr ⟨Sum.inr j, by
        apply congrArg Sum.inr
        apply Fin.ext
        change x + (k.val - x) = k.val
        omega⟩

/-- The first retained block is a complete square in the fresh mask. -/
theorem residualFresh_firstSquare
    {a b c e W x y : ℕ} (hx : x ≤ W) (hy : y ≤ W)
    (i : Fin a ⊕ Fin x) (j : Fin c ⊕ Fin y) :
    residualFresh
      (firstPartitionEmbedding (a := a) (b := b) hx i)
      (firstPartitionEmbedding (a := c) (b := e) hy j) := by
  rcases i with i | i <;> rcases j with j | j <;> trivial

/-- The complementary retained block is also complete in the fresh mask. -/
theorem residualFresh_secondSquare
    {a b c e W x y : ℕ} (hx : x ≤ W) (hy : y ≤ W)
    (i : Fin b ⊕ Fin (W - x)) (j : Fin e ⊕ Fin (W - y)) :
    residualFresh
      (secondPartitionEmbedding (a := a) (b := b) hx i)
      (secondPartitionEmbedding (a := c) (b := e) hy j) := by
  rcases i with i | i <;> rcases j with j | j <;> trivial

/-- With `x=n₁-a` and `y=n₁-c`, the first row and column domains both
have size `n₁`, and their complements both have size `n_res-n₁`. -/
theorem twoSquare_cardinalities
    {W a b c e : ℕ}
    (ha : a ≤ W) (hc : c ≤ W)
    (hs : a + b = c + e) (hsW : a + b ≤ 2 * W) :
    let n₁ := balancedSquareSize W a b c
    let x := n₁ - a
    let y := n₁ - c
    Fintype.card (Fin a ⊕ Fin x) = n₁ ∧
      Fintype.card (Fin c ⊕ Fin y) = n₁ ∧
      Fintype.card (Fin b ⊕ Fin (W - x)) = W + a + b - n₁ ∧
      Fintype.card (Fin e ⊕ Fin (W - y)) = W + a + b - n₁ := by
  dsimp
  have hspec := centralCounts_spec W a b c
  have hcounts := centralCounts_le_W ha hc hs hsW
  have hnupper := balancedSquareSize_le_maskUpper ha hc hs hsW
  simp only [Fintype.card_sum, Fintype.card_fin]
  constructor
  · exact hspec.1
  constructor
  · exact hspec.2
  constructor <;> omega

end BernoulliSection9
