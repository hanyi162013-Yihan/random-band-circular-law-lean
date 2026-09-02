import BernoulliSection9.ExternalInputs
import BernoulliSection9.FreshIndependence
import BernoulliSection9.TwoSquares

/-!
# The two disjoint iid residual squares

This module turns the literal coordinate partitions from `TwoSquares` into
injective label maps for the fresh packet entries.  Restriction of the global
iid family along these maps is therefore proved iid, and the two label images
are proved disjoint.  No independence or mask certificate is supplied by a
caller.
-/

noncomputable section

namespace BernoulliSection9

/-- Fresh residual entry labels, with membership in the seven-block mask
stored in the subtype. -/
abbrev ResidualFreshEntry (a b c e W : ℕ) :=
  {p : ResidualIndex a b W × ResidualIndex c e W //
    residualFresh p.1 p.2}

noncomputable instance residualFreshEntryFintype (a b c e W : ℕ) :
    Fintype (ResidualFreshEntry a b c e W) :=
  Fintype.ofFinite _

noncomputable instance residualFreshEntryDecidableEq (a b c e W : ℕ) :
    DecidableEq (ResidualFreshEntry a b c e W) :=
  Classical.decEq _

/-- Entry-label injection for the first complete square. -/
def firstSquareEntryEmbedding
    {a b c e W x y : ℕ} (hx : x ≤ W) (hy : y ≤ W) :
    ((Fin a ⊕ Fin x) × (Fin c ⊕ Fin y)) ↪
      ResidualFreshEntry a b c e W where
  toFun p := ⟨
    (firstPartitionEmbedding (a := a) (b := b) hx p.1,
      firstPartitionEmbedding (a := c) (b := e) hy p.2),
    residualFresh_firstSquare hx hy p.1 p.2⟩
  inj' := by
    intro p q hpq
    apply Prod.ext
    · apply (firstPartitionEmbedding (a := a) (b := b) hx).injective
      exact congrArg (fun z : ResidualFreshEntry a b c e W ↦ z.val.1) hpq
    · apply (firstPartitionEmbedding (a := c) (b := e) hy).injective
      exact congrArg (fun z : ResidualFreshEntry a b c e W ↦ z.val.2) hpq

/-- Entry-label injection for the complementary complete square. -/
def secondSquareEntryEmbedding
    {a b c e W x y : ℕ} (hx : x ≤ W) (hy : y ≤ W) :
    ((Fin b ⊕ Fin (W - x)) × (Fin e ⊕ Fin (W - y))) ↪
      ResidualFreshEntry a b c e W where
  toFun p := ⟨
    (secondPartitionEmbedding (a := a) (b := b) hx p.1,
      secondPartitionEmbedding (a := c) (b := e) hy p.2),
    residualFresh_secondSquare hx hy p.1 p.2⟩
  inj' := by
    intro p q hpq
    apply Prod.ext
    · apply (secondPartitionEmbedding (a := a) (b := b) hx).injective
      exact congrArg (fun z : ResidualFreshEntry a b c e W ↦ z.val.1) hpq
    · apply (secondPartitionEmbedding (a := c) (b := e) hy).injective
      exact congrArg (fun z : ResidualFreshEntry a b c e W ↦ z.val.2) hpq

/-- The two complete squares do not share an entry label.  In fact their row
images and their column images are separately disjoint. -/
theorem squareEntryEmbedding_disjoint
    {a b c e W x y : ℕ} (hx : x ≤ W) (hy : y ≤ W) :
    Disjoint
      (Set.range (firstSquareEntryEmbedding
        (a := a) (b := b) (c := c) (e := e) hx hy))
      (Set.range (secondSquareEntryEmbedding
        (a := a) (b := b) (c := c) (e := e) hx hy)) := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  rcases hz₁ with ⟨p, rfl⟩
  rcases hz₂ with ⟨q, hpq⟩
  have hrow :
      secondPartitionEmbedding (a := a) (b := b) hx q.1 =
        firstPartitionEmbedding (a := a) (b := b) hx p.1 :=
    congrArg (fun z : ResidualFreshEntry a b c e W ↦ z.val.1) hpq
  exact Set.disjoint_left.mp (partitionEmbedding_disjoint
    (a := a) (b := b) hx)
      ⟨p.1, rfl⟩ ⟨q.1, hrow⟩

/-- The first retained complete square, as an iid family on its literal row
and column types. -/
def IidSubgaussianFamily.firstResidualSquare
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {a b c e W x y : ℕ}
    (S : IidSubgaussianFamily Ω μ (ResidualFreshEntry a b c e W))
    (hx : x ≤ W) (hy : y ≤ W) :
    IidSubgaussianFamily Ω μ
      ((Fin a ⊕ Fin x) × (Fin c ⊕ Fin y)) :=
  S.reindex (firstSquareEntryEmbedding hx hy)

/-- The complementary retained complete square, likewise iid. -/
def IidSubgaussianFamily.secondResidualSquare
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {a b c e W x y : ℕ}
    (S : IidSubgaussianFamily Ω μ (ResidualFreshEntry a b c e W))
    (hx : x ≤ W) (hy : y ≤ W) :
    IidSubgaussianFamily Ω μ
      ((Fin b ⊕ Fin (W - x)) × (Fin e ⊕ Fin (W - y))) :=
  S.reindex (secondSquareEntryEmbedding hx hy)

/-! ## Reindexing the literal domains as `Fin n × Fin n` Cook squares -/

noncomputable def firstSquareRowEquiv (W a b c : ℕ) :
    Fin (balancedSquareSize W a b c) ≃
      (Fin a ⊕ Fin (balancedSquareSize W a b c - a)) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sum]
    exact (centralCounts_spec W a b c).1.symm)

noncomputable def firstSquareColEquiv (W a b c : ℕ) :
    Fin (balancedSquareSize W a b c) ≃
      (Fin c ⊕ Fin (balancedSquareSize W a b c - c)) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sum]
    exact (centralCounts_spec W a b c).2.symm)

noncomputable def secondSquareRowEquiv
    {W a b c e : ℕ}
    (ha : a ≤ W) (hc : c ≤ W)
    (hs : a + b = c + e) (hsW : a + b ≤ 2 * W) :
    Fin (W + a + b - balancedSquareSize W a b c) ≃
      (Fin b ⊕ Fin (W - (balancedSquareSize W a b c - a))) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sum]
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      (twoSquare_cardinalities ha hc hs hsW).2.2.1.symm)

noncomputable def secondSquareColEquiv
    {W a b c e : ℕ}
    (ha : a ≤ W) (hc : c ≤ W)
    (hs : a + b = c + e) (hsW : a + b ≤ 2 * W) :
    Fin (W + a + b - balancedSquareSize W a b c) ≃
      (Fin e ⊕ Fin (W - (balancedSquareSize W a b c - c))) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sum]
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      (twoSquare_cardinalities ha hc hs hsW).2.2.2.symm)

/-- The first retained square in the exact concrete model expected by the
Cook input. -/
def IidSubgaussianFamily.firstBalancedCookSquare
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {W a b c e : ℕ}
    (S : IidSubgaussianFamily Ω μ (ResidualFreshEntry a b c e W))
    (ha : a ≤ W) (hc : c ≤ W)
    (hs : a + b = c + e) (hsW : a + b ≤ 2 * W) :
    IidSubgaussianSquare Ω μ (balancedSquareSize W a b c) :=
  let hx := (centralCounts_le_W ha hc hs hsW).1
  let hy := (centralCounts_le_W ha hc hs hsW).2
  (S.firstResidualSquare hx hy).squareOfRowColEquiv
    (firstSquareRowEquiv W a b c) (firstSquareColEquiv W a b c)

/-- The complementary retained square in the exact concrete model expected
by the second conditional Cook application. -/
def IidSubgaussianFamily.secondBalancedCookSquare
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {W a b c e : ℕ}
    (S : IidSubgaussianFamily Ω μ (ResidualFreshEntry a b c e W))
    (ha : a ≤ W) (hc : c ≤ W)
    (hs : a + b = c + e) (hsW : a + b ≤ 2 * W) :
    IidSubgaussianSquare Ω μ
      (W + a + b - balancedSquareSize W a b c) :=
  let hx := (centralCounts_le_W ha hc hs hsW).1
  let hy := (centralCounts_le_W ha hc hs hsW).2
  (S.secondResidualSquare hx hy).squareOfRowColEquiv
    (secondSquareRowEquiv ha hc hs hsW)
    (secondSquareColEquiv ha hc hs hsW)

/-! ## Canonical fresh and conditioning sigma-fields -/

/-- The concrete injection which labels every entry of the first balanced
Cook square by its original residual packet coordinate. -/
def firstBalancedEntryEmbedding
    {W a b c e : Nat}
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W) :
    (Fin (balancedSquareSize W a b c) ×
      Fin (balancedSquareSize W a b c)) ↪
      ResidualFreshEntry a b c e W :=
  let hx := (centralCounts_le_W ha hc hs hsW).1
  let hy := (centralCounts_le_W ha hc hs hsW).2
  let pairEmbedding :
      (Fin (balancedSquareSize W a b c) ×
        Fin (balancedSquareSize W a b c)) ↪
        ((Fin a ⊕ Fin (balancedSquareSize W a b c - a)) ×
          (Fin c ⊕ Fin (balancedSquareSize W a b c - c))) :=
    ⟨fun p =>
        (firstSquareRowEquiv W a b c p.1,
          firstSquareColEquiv W a b c p.2),
      fun p q hpq => Prod.ext
        ((firstSquareRowEquiv W a b c).injective
          (congrArg Prod.fst hpq))
        ((firstSquareColEquiv W a b c).injective
          (congrArg Prod.snd hpq))⟩
  pairEmbedding.trans (firstSquareEntryEmbedding hx hy)

/-- The concrete injection which labels every entry of the complementary
balanced Cook square. -/
def secondBalancedEntryEmbedding
    {W a b c e : Nat}
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W) :
    (Fin (W + a + b - balancedSquareSize W a b c) ×
      Fin (W + a + b - balancedSquareSize W a b c)) ↪
      ResidualFreshEntry a b c e W :=
  let hx := (centralCounts_le_W ha hc hs hsW).1
  let hy := (centralCounts_le_W ha hc hs hsW).2
  let pairEmbedding :
      (Fin (W + a + b - balancedSquareSize W a b c) ×
        Fin (W + a + b - balancedSquareSize W a b c)) ↪
        ((Fin b ⊕ Fin (W - (balancedSquareSize W a b c - a))) ×
          (Fin e ⊕ Fin (W - (balancedSquareSize W a b c - c)))) :=
    ⟨fun p =>
        (secondSquareRowEquiv ha hc hs hsW p.1,
          secondSquareColEquiv ha hc hs hsW p.2),
      fun p q hpq => Prod.ext
        ((secondSquareRowEquiv ha hc hs hsW).injective
          (congrArg Prod.fst hpq))
        ((secondSquareColEquiv ha hc hs hsW).injective
          (congrArg Prod.snd hpq))⟩
  pairEmbedding.trans (secondSquareEntryEmbedding hx hy)

/-- Entrywise identification of the first Cook square with its concrete
residual-entry injection. -/
theorem firstBalancedCookSquare_atom
    {Omega : Type*} [MeasurableSpace Omega] {mu : MeasureTheory.Measure Omega}
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (p : Fin (balancedSquareSize W a b c) ×
      Fin (balancedSquareSize W a b c)) :
    (S.firstBalancedCookSquare ha hc hs hsW).atom p =
      S.atom (firstBalancedEntryEmbedding ha hc hs hsW p) := by
  rfl

/-- Entrywise identification of the complementary Cook square. -/
theorem secondBalancedCookSquare_atom
    {Omega : Type*} [MeasurableSpace Omega] {mu : MeasureTheory.Measure Omega}
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (p : Fin (W + a + b - balancedSquareSize W a b c) ×
      Fin (W + a + b - balancedSquareSize W a b c)) :
    (S.secondBalancedCookSquare ha hc hs hsW).atom p =
      S.atom (secondBalancedEntryEmbedding ha hc hs hsW p) := by
  rfl

/-- Sigma-field generated by the first complete Cook square. -/
def IidSubgaussianFamily.firstBalancedFreshSigma
    {Omega : Type*} [MeasurableSpace Omega] {mu : MeasureTheory.Measure Omega}
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W) :
    MeasurableSpace Omega :=
  S.coordinateSigma
    (selectedCoordinateSet (firstBalancedEntryEmbedding ha hc hs hsW))

/-- Sigma-field generated by all residual entries outside the first square. -/
def IidSubgaussianFamily.firstBalancedConditioningSigma
    {Omega : Type*} [MeasurableSpace Omega] {mu : MeasureTheory.Measure Omega}
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W) :
    MeasurableSpace Omega :=
  S.coordinateSigma
    (Finset.univ \
      selectedCoordinateSet (firstBalancedEntryEmbedding ha hc hs hsW))

theorem IidSubgaussianFamily.firstBalancedFreshSigma_le
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega}
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W) :
    S.firstBalancedFreshSigma ha hc hs hsW <= mOmega :=
  S.coordinateSigma_le _

theorem IidSubgaussianFamily.firstBalancedConditioningSigma_le
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega}
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W) :
    S.firstBalancedConditioningSigma ha hc hs hsW <= mOmega :=
  S.coordinateSigma_le _

/-- The first square is independent of every remaining residual coordinate. -/
theorem IidSubgaussianFamily.firstBalancedFresh_indep_conditioning
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega}
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W) :
    ProbabilityTheory.Indep
      (S.firstBalancedFreshSigma ha hc hs hsW)
      (S.firstBalancedConditioningSigma ha hc hs hsW) mu := by
  exact S.selectedSigma_indep_complement
    (firstBalancedEntryEmbedding ha hc hs hsW)

/-- Every atom of the first concrete Cook square is measurable in its
canonical fresh sigma-field. -/
theorem IidSubgaussianFamily.firstBalancedCook_atom_measurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega}
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (p : Fin (balancedSquareSize W a b c) ×
      Fin (balancedSquareSize W a b c)) :
    @Measurable Omega Real (S.firstBalancedFreshSigma ha hc hs hsW) _
      ((S.firstBalancedCookSquare ha hc hs hsW).atom p) := by
  change @Measurable Omega Real
    (S.coordinateSigma
      (selectedCoordinateSet (firstBalancedEntryEmbedding ha hc hs hsW))) _
    (S.atom (firstBalancedEntryEmbedding ha hc hs hsW p))
  simpa [IidSubgaussianFamily.reindex] using
    S.reindexed_atom_measurable_selectedSigma
      (firstBalancedEntryEmbedding ha hc hs hsW) p

/-- Sigma-field generated by the complementary complete Cook square. -/
def IidSubgaussianFamily.secondBalancedFreshSigma
    {Omega : Type*} [MeasurableSpace Omega] {mu : MeasureTheory.Measure Omega}
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W) :
    MeasurableSpace Omega :=
  S.coordinateSigma
    (selectedCoordinateSet (secondBalancedEntryEmbedding ha hc hs hsW))

/-- Sigma-field generated by all residual entries outside the complementary
square. -/
def IidSubgaussianFamily.secondBalancedConditioningSigma
    {Omega : Type*} [MeasurableSpace Omega] {mu : MeasureTheory.Measure Omega}
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W) :
    MeasurableSpace Omega :=
  S.coordinateSigma
    (Finset.univ \
      selectedCoordinateSet (secondBalancedEntryEmbedding ha hc hs hsW))

theorem IidSubgaussianFamily.secondBalancedFreshSigma_le
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega}
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W) :
    S.secondBalancedFreshSigma ha hc hs hsW <= mOmega :=
  S.coordinateSigma_le _

theorem IidSubgaussianFamily.secondBalancedConditioningSigma_le
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega}
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W) :
    S.secondBalancedConditioningSigma ha hc hs hsW <= mOmega :=
  S.coordinateSigma_le _

/-- The complementary square is independent of every remaining residual
coordinate, including the first square. -/
theorem IidSubgaussianFamily.secondBalancedFresh_indep_conditioning
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega}
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W) :
    ProbabilityTheory.Indep
      (S.secondBalancedFreshSigma ha hc hs hsW)
      (S.secondBalancedConditioningSigma ha hc hs hsW) mu := by
  exact S.selectedSigma_indep_complement
    (secondBalancedEntryEmbedding ha hc hs hsW)

/-- Every atom of the second concrete Cook square is measurable in its
canonical fresh sigma-field. -/
theorem IidSubgaussianFamily.secondBalancedCook_atom_measurable
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega}
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (p : Fin (W + a + b - balancedSquareSize W a b c) ×
      Fin (W + a + b - balancedSquareSize W a b c)) :
    @Measurable Omega Real (S.secondBalancedFreshSigma ha hc hs hsW) _
      ((S.secondBalancedCookSquare ha hc hs hsW).atom p) := by
  change @Measurable Omega Real
    (S.coordinateSigma
      (selectedCoordinateSet (secondBalancedEntryEmbedding ha hc hs hsW))) _
    (S.atom (secondBalancedEntryEmbedding ha hc hs hsW p))
  simpa [IidSubgaussianFamily.reindex] using
    S.reindexed_atom_measurable_selectedSigma
      (secondBalancedEntryEmbedding ha hc hs hsW) p

end BernoulliSection9
