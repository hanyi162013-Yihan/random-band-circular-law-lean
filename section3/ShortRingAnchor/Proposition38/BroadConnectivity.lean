import ShortRingAnchor.Proposition38.HeavyBlocks

/-! # Proposition 3.8: the broad-connectivity hypothesis of Cook 1.12

The definition below is Cook's Definition 1.9 for a zero-one mask. Taking
the threshold parameter `σ₀ = 1/2` leaves this mask unchanged. All three
requirements, including the expansion requirement for every column set,
are proved for the actual full-block cyclic mask.
-/

noncomputable section
open scoped BigOperators
namespace ShortRingAnchor.Proposition38

structure BroadlyConnected {I : Type*} [Fintype I] [DecidableEq I]
    (adj : I → I → Prop) [DecidableRel adj] (δ ν : ℝ) : Prop where
  row : ∀ i, δ * (Fintype.card I : ℝ) ≤ ((Finset.univ.filter (adj i)).card : ℝ)
  column : ∀ j, δ * (Fintype.card I : ℝ) ≤
    ((Finset.univ.filter (fun i => adj i j)).card : ℝ)
  expansion : ∀ J : Finset I,
    min (Fintype.card I : ℝ) ((1 + ν) * (J.card : ℝ)) ≤
      ((Finset.univ.filter (fun i => δ * (J.card : ℝ) ≤
        ((J.filter (adj i)).card : ℝ))).card : ℝ)

/-- Proposition 3.8, Cook geometry: every scalar block has exactly `W` entries. -/
theorem block_fiber_card (W s : ℕ) (b : Fin (s + 3)) :
    (Finset.univ.filter (fun i : Fin ((s + 3) * W) =>
      (finProdFinEquiv.symm i).1 = b)).card = W := by
  classical
  have heq : (Finset.univ.filter (fun i : Fin ((s + 3) * W) =>
      (finProdFinEquiv.symm i).1 = b)) =
      Finset.univ.image (fun a : Fin W => finProdFinEquiv (b, a)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨(finProdFinEquiv.symm i).2, ?_⟩
      conv_lhs => rw [← h]
      exact finProdFinEquiv.apply_symm_apply i
    · rintro ⟨a, rfl⟩
      simp
  rw [heq, Finset.card_image_of_injective]
  · simp
  · intro a a' h
    exact congrArg Prod.snd (finProdFinEquiv.injective h)

/-- Proposition 3.8, Cook geometry: an arbitrary set of block labels
represents exactly its cardinality times the common block width. -/
theorem card_label_mem {I B : Type*} [Fintype I] [DecidableEq I]
    [Fintype B] [DecidableEq B] (label : I → B) (W : ℕ)
    (hfiber : ∀ b, (Finset.univ.filter (fun i => label i = b)).card = W)
    (K : Finset B) :
    (Finset.univ.filter (fun i => label i ∈ K)).card = K.card * W := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ K label]
  simp only [hfiber, Finset.sum_const, smul_eq_mul]

/-- Proposition 3.8, Cook geometry: heavy-block expansion supplies all
three broad-connectivity requirements, with no probabilistic premise. -/
theorem broadlyConnected_of_cyclic_blocks
    {I : Type*} [Fintype I] [DecidableEq I] (s W : ℕ)
    (label : I → Fin (s + 3))
    (hfiber : ∀ b, (Finset.univ.filter (fun i => label i = b)).card = W)
    (hcard : Fintype.card I = (s + 3) * W) :
    BroadlyConnected (fun i j => siteAdjacent (label i) (label j))
      (broadDelta s) (broadNu s) := by
  classical
  have hdegree (i : I) : W ≤ (Finset.univ.filter
      (fun j => siteAdjacent (label i) (label j))).card := by
    rw [← hfiber (label i)]
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact Or.inl hj
  have hδ : broadDelta s * (Fintype.card I : ℝ) ≤ (W : ℝ) := by
    rw [hcard, Nat.cast_mul]
    have hm : (1 : ℝ) ≤ (s + 3 : ℕ) := by exact_mod_cast (show 1 ≤ s + 3 by omega)
    have heq : broadDelta s * (((s + 3 : ℕ) : ℝ) * W) =
        (W : ℝ) / (2 * ((s + 3 : ℕ) : ℝ)) := by
      unfold broadDelta
      field_simp
      <;> ring
    rw [heq]
    exact div_le_self (Nat.cast_nonneg _) (by linarith)
  refine ⟨fun i => hδ.trans (by exact_mod_cast hdegree i), ?_, ?_⟩
  · intro j
    simp_rw [siteAdjacent_symm (j := label j)]
    exact hδ.trans (by exact_mod_cast hdegree j)
  · intro J
    by_cases hJ : J.card = 0
    · simp only [hJ, Nat.cast_zero, mul_zero]
      exact (min_le_right _ _).trans (Nat.cast_nonneg _)
    let c : Fin (s + 3) → ℝ := fun b => ((J.filter (fun j => label j = b)).card : ℝ)
    let K := heavyBlocks s c (J.card : ℝ)
    let E := K ∪ K.image (finRotate (s + 3))
    have hc (b) : c b ≤ (W : ℝ) := by
      dsimp [c]
      rw [← hfiber b]
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ J))
    have hsum : ∑ b, c b = (J.card : ℝ) := by
      dsimp [c]
      rw [← Nat.cast_sum, Finset.sum_card_fiberwise_eq_card_filter]
      simp
    have hmax : (J.card : ℝ) ≤ ((s + 3 : ℕ) : ℝ) * W := by
      rw [← Nat.cast_mul, ← hcard]
      exact_mod_cast Finset.card_le_univ J
    have hweight := heavy_expansion_weight s c (J.card : ℝ) W
      (by exact_mod_cast Nat.pos_of_ne_zero hJ) (Nat.cast_nonneg _) hc hsum hmax
    have hsub : (Finset.univ.filter (fun i => label i ∈ E)) ⊆
        Finset.univ.filter (fun i => broadDelta s * (J.card : ℝ) ≤
          ((J.filter (fun j => siteAdjacent (label i) (label j))).card : ℝ)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have hex : ∃ b ∈ K, siteAdjacent (label i) b := by
        rcases Finset.mem_union.mp hi with hb | hb
        · exact ⟨label i, hb, Or.inl rfl⟩
        · obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hb
          refine ⟨b, hb, siteAdjacent_symm.mp ?_⟩
          exact Or.inr (Or.inl heq.symm)
      obtain ⟨b, hb, hadj⟩ := hex
      have hh : broadDelta s * (J.card : ℝ) ≤ c b := by
        simpa only [K, heavyBlocks, Finset.mem_filter, Finset.mem_univ, true_and] using hb
      apply hh.trans
      dsimp [c]
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro j hj
      rcases Finset.mem_filter.mp hj with ⟨hjJ, hjb⟩
      exact Finset.mem_filter.mpr ⟨hjJ, hjb.symm ▸ hadj⟩
    have hcount := Finset.card_le_card hsub
    rw [card_label_mem label W hfiber E] at hcount
    rw [hcard, Nat.cast_mul]
    exact hweight.trans (by exact_mod_cast hcount)

def scalarAdjacent (W s : ℕ) (i j : Fin ((s + 3) * W)) : Prop :=
  siteAdjacent (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1

instance (W s : ℕ) : DecidableRel (scalarAdjacent W s) := fun i j =>
  inferInstanceAs (Decidable (siteAdjacent (finProdFinEquiv.symm i).1
    (finProdFinEquiv.symm j).1))

/-- Proposition 3.8, Cook 1.12 application: the actual zero-one mask is
broadly connected. Thus this certificate is not an external interface. -/
theorem fullBlock_broadlyConnected (W s : ℕ) :
    BroadlyConnected (scalarAdjacent W s) (broadDelta s) (broadNu s) := by
  exact broadlyConnected_of_cyclic_blocks s W
    (fun i : Fin ((s + 3) * W) => (finProdFinEquiv.symm i).1)
    (block_fiber_card W s) (by simp)

/-- Proposition 3.8, bounded-block uniformity: decreasing the two
connectivity parameters preserves Cook's hypotheses. -/
theorem BroadlyConnected.mono {I : Type*} [Fintype I] [DecidableEq I]
    {adj : I → I → Prop} [DecidableRel adj] {δ ν δ' ν' : ℝ}
    (h : BroadlyConnected adj δ ν) (hδ : δ' ≤ δ) (hν : ν' ≤ ν) :
    BroadlyConnected adj δ' ν' := by
  classical
  refine ⟨fun i => (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)).trans (h.row i),
    fun j => (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)).trans (h.column j), ?_⟩
  intro J
  apply (min_le_min_left _ (mul_le_mul_of_nonneg_right
    (add_le_add (le_refl 1) hν) (Nat.cast_nonneg _))).trans
  apply (h.expansion J).trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  rcases Finset.mem_filter.mp hi with ⟨hi, hbound⟩
  exact Finset.mem_filter.mpr ⟨hi,
    (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)).trans hbound⟩

/-- Proposition 3.8, bounded-block uniformity: the constants can be
chosen using the fixed upper bound on the number of blocks. -/
theorem fullBlock_broadlyConnected_uniform (W s sStar : ℕ) (hs : s ≤ sStar) :
    BroadlyConnected (scalarAdjacent W s) (broadDelta sStar) (broadNu sStar) := by
  have hm : (((s + 3 : ℕ) : ℝ)) ≤ ((sStar + 3 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hs 3
  apply (fullBlock_broadlyConnected W s).mono
  · unfold broadDelta
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hm 2) (by norm_num)
  · unfold broadNu
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

end ShortRingAnchor.Proposition38
