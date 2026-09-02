import BernoulliSection9.TwoSquareRandomness

/-!
# Reindexing the residual mask as two square diagonal blocks

The row and column partitions from `TwoSquares` are upgraded here to actual
equivalences.  Consequently every residual matrix has the literal `2 x 2`
block form used in (9.27), with the two complete Cook squares on its diagonal.
-/

open scoped Matrix

noncomputable section

namespace BernoulliSection9

/-- The disjoint first/tail coordinate embeddings form an equivalence onto
all residual coordinates. -/
def partitionEquiv {a b W x : Nat} (hx : x <= W) :
    (Fin a ⊕ Fin x) ⊕ (Fin b ⊕ Fin (W - x)) ≃
      ResidualIndex a b W :=
  Equiv.ofBijective
    (fun u => match u with
      | Sum.inl i => firstPartitionEmbedding hx i
      | Sum.inr j => secondPartitionEmbedding hx j)
    ⟨by
      intro u v huv
      rcases u with i | j <;> rcases v with i' | j'
      · exact congrArg Sum.inl ((firstPartitionEmbedding hx).injective huv)
      · exfalso
        exact Set.disjoint_left.mp (partitionEmbedding_disjoint hx)
          ⟨i, rfl⟩ ⟨j', huv.symm⟩
      · exfalso
        exact Set.disjoint_left.mp (partitionEmbedding_disjoint hx)
          ⟨i', rfl⟩ ⟨j, huv⟩
      · exact congrArg Sum.inr ((secondPartitionEmbedding hx).injective huv),
    by
      intro z
      have hz : z ∈
          Set.range (firstPartitionEmbedding (a := a) (b := b) hx) ∪
            Set.range (secondPartitionEmbedding (a := a) (b := b) hx) := by
        rw [partitionEmbedding_cover hx]
        trivial
      rcases hz with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr j, rfl⟩⟩

/-- Balanced residual row equivalence, with the first and complementary
Cook-square row coordinates in the two summands. -/
def balancedResidualRowEquiv
    {W a b c e : Nat}
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W) :
    Fin (balancedSquareSize W a b c) ⊕
        Fin (W + a + b - balancedSquareSize W a b c) ≃
      ResidualIndex a b W :=
  let hx := (centralCounts_le_W ha hc hs hsW).1
  (Equiv.sumCongr (firstSquareRowEquiv W a b c)
    (secondSquareRowEquiv ha hc hs hsW)).trans (partitionEquiv hx)

/-- Balanced residual column equivalence. -/
def balancedResidualColEquiv
    {W a b c e : Nat}
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W) :
    Fin (balancedSquareSize W a b c) ⊕
        Fin (W + a + b - balancedSquareSize W a b c) ≃
      ResidualIndex c e W :=
  let hy := (centralCounts_le_W ha hc hs hsW).2
  (Equiv.sumCongr (firstSquareColEquiv W a b c)
    (secondSquareColEquiv ha hc hs hsW)).trans (partitionEquiv hy)

/-- A residual matrix reindexed so that the two complete squares are its
diagonal blocks. -/
def balancedResidualMatrix
    {W a b c e : Nat}
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (M : Matrix (ResidualIndex a b W) (ResidualIndex c e W) Complex) :
    Matrix
      (Fin (balancedSquareSize W a b c) ⊕
        Fin (W + a + b - balancedSquareSize W a b c))
      (Fin (balancedSquareSize W a b c) ⊕
        Fin (W + a + b - balancedSquareSize W a b c)) Complex :=
  M.submatrix
    (balancedResidualRowEquiv ha hc hs hsW)
    (balancedResidualColEquiv ha hc hs hsW)

/-- Literal four-block identity for the balanced residual reindexing. -/
theorem balancedResidualMatrix_eq_fromBlocks
    {W a b c e : Nat}
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (M : Matrix (ResidualIndex a b W) (ResidualIndex c e W) Complex) :
    balancedResidualMatrix ha hc hs hsW M =
      Matrix.fromBlocks
        (balancedResidualMatrix ha hc hs hsW M).toBlocks₁₁
        (balancedResidualMatrix ha hc hs hsW M).toBlocks₁₂
        (balancedResidualMatrix ha hc hs hsW M).toBlocks₂₁
        (balancedResidualMatrix ha hc hs hsW M).toBlocks₂₂ := by
  exact (Matrix.fromBlocks_toBlocks _).symm

/-- On first-square coordinates, the balanced row equivalence is exactly
the concrete first partition embedding. -/
theorem balancedResidualRowEquiv_inl
    {W a b c e : Nat}
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (i : Fin (balancedSquareSize W a b c)) :
    balancedResidualRowEquiv ha hc hs hsW (Sum.inl i) =
      firstPartitionEmbedding (centralCounts_le_W ha hc hs hsW).1
        (firstSquareRowEquiv W a b c i) := by
  rfl

/-- The analogous first-square column identity. -/
theorem balancedResidualColEquiv_inl
    {W a b c e : Nat}
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (j : Fin (balancedSquareSize W a b c)) :
    balancedResidualColEquiv ha hc hs hsW (Sum.inl j) =
      firstPartitionEmbedding (centralCounts_le_W ha hc hs hsW).2
        (firstSquareColEquiv W a b c j) := by
  rfl

/-- On the complementary coordinates, the row equivalence is the second
partition embedding. -/
theorem balancedResidualRowEquiv_inr
    {W a b c e : Nat}
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (i : Fin (W + a + b - balancedSquareSize W a b c)) :
    balancedResidualRowEquiv ha hc hs hsW (Sum.inr i) =
      secondPartitionEmbedding (centralCounts_le_W ha hc hs hsW).1
        (secondSquareRowEquiv ha hc hs hsW i) := by
  rfl

/-- The analogous complementary column identity. -/
theorem balancedResidualColEquiv_inr
    {W a b c e : Nat}
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (j : Fin (W + a + b - balancedSquareSize W a b c)) :
    balancedResidualColEquiv ha hc hs hsW (Sum.inr j) =
      secondPartitionEmbedding (centralCounts_le_W ha hc hs hsW).2
        (secondSquareColEquiv ha hc hs hsW j) := by
  rfl

end BernoulliSection9
