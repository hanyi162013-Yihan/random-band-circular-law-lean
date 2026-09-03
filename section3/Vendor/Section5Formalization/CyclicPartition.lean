/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/Section5Formalization/CyclicPartition.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Section5Formalization.Section5Formalization

noncomputable section

open Set

namespace Section5Formalization

/-- Left endpoint of the `j`-th balanced consecutive interval. -/
def balancedStart (N L j : ℕ) : ℕ :=
  j * (N / L) + min j (N % L)

/-- The `j`-th consecutive block in the canonical balanced partition. -/
def balancedIntervalBlock (N L : ℕ) (j : Fin L) : Finset (Fin N) :=
  Finset.univ.filter fun i =>
    balancedStart N L j.1 ≤ i.1 ∧ i.1 < balancedStart N L (j.1 + 1)

@[simp]
lemma balancedStart_zero (N L : ℕ) : balancedStart N L 0 = 0 := by
  simp [balancedStart]

lemma balancedStart_last (N L : ℕ) (hL : 0 < L) : balancedStart N L L = N := by
  have hr : N % L ≤ L := (Nat.mod_lt N hL).le
  rw [balancedStart, Nat.min_eq_right hr]
  simpa [add_comm, mul_comm] using (Nat.mod_add_div N L)

lemma balancedStart_mono (N L : ℕ) : Monotone (balancedStart N L) := by
  intro a b hab
  exact Nat.add_le_add (Nat.mul_le_mul_right (N / L) hab)
    (min_le_min hab (le_refl (N % L)))

lemma balancedStart_step (N L j : ℕ) :
    balancedStart N L (j + 1) - balancedStart N L j =
      if j < N % L then N / L + 1 else N / L := by
  unfold balancedStart
  by_cases hj : j < N % L
  · have hjle : j ≤ N % L := hj.le
    have hsucc : j + 1 ≤ N % L := by omega
    rw [Nat.min_eq_left hsucc, Nat.min_eq_left hjle, if_pos hj]
    have heq :
        (j + 1) * (N / L) + (j + 1) =
          (j * (N / L) + j) + (N / L + 1) := by ring
    rw [heq, Nat.add_sub_cancel_left]
  · have hrj : N % L ≤ j := Nat.le_of_not_gt hj
    have hrsucc : N % L ≤ j + 1 := hrj.trans (Nat.le_add_right j 1)
    rw [Nat.min_eq_right hrsucc, Nat.min_eq_right hrj, if_neg hj]
    have heq :
        (j + 1) * (N / L) + N % L =
          (j * (N / L) + N % L) + N / L := by ring
    rw [heq, Nat.add_sub_cancel_left]

lemma balancedStart_succ_le_last (N L : ℕ) (hL : 0 < L) (j : Fin L) :
    balancedStart N L (j.1 + 1) ≤ N := by
  calc
    balancedStart N L (j.1 + 1) ≤ balancedStart N L L :=
      balancedStart_mono N L (Nat.succ_le_iff.mpr j.2)
    _ = N := balancedStart_last N L hL

/-- The canonical balanced intervals are pairwise disjoint. -/
theorem balancedIntervalBlock_pairwise_disjoint (N L : ℕ) :
    Pairwise fun i j : Fin L =>
      Disjoint (balancedIntervalBlock N L i) (balancedIntervalBlock N L j) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro x hxi hxj
  simp only [balancedIntervalBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hxi hxj
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hs : balancedStart N L (i.1 + 1) ≤ balancedStart N L j.1 :=
      balancedStart_mono N L (Nat.succ_le_iff.mpr hij')
    omega
  · have hs : balancedStart N L (j.1 + 1) ≤ balancedStart N L i.1 :=
      balancedStart_mono N L (Nat.succ_le_iff.mpr hji')
    omega

/-- Cardinality of a canonical block is the difference of its endpoints. -/
theorem balancedIntervalBlock_card (N L : ℕ) (hL : 0 < L) (j : Fin L) :
    (balancedIntervalBlock N L j).card =
      balancedStart N L (j.1 + 1) - balancedStart N L j.1 := by
  let a := balancedStart N L j.1
  let b := balancedStart N L (j.1 + 1)
  have hbN : b ≤ N := balancedStart_succ_le_last N L hL j
  have hcard : (balancedIntervalBlock N L j).card = (Finset.Ico a b).card := by
    classical
    refine Finset.card_bij (fun i _hi => i.1) ?_ ?_ ?_
    · intro i hi
      simpa [balancedIntervalBlock, a, b] using hi
    · intro i hi i' hi' heq
      exact Fin.ext heq
    · intro x hx
      have hxb : x < b := (Finset.mem_Ico.mp hx).2
      have hxN : x < N := hxb.trans_le hbN
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      simpa [balancedIntervalBlock, a, b] using hx
  simpa [a, b] using hcard.trans (Nat.card_Ico a b)

/-- Every canonical block has size `N / L` or `N / L + 1`. -/
theorem balancedIntervalBlock_card_eq (N L : ℕ) (hL : 0 < L) (j : Fin L) :
    (balancedIntervalBlock N L j).card =
      if j.1 < N % L then N / L + 1 else N / L := by
  rw [balancedIntervalBlock_card N L hL j, balancedStart_step]

/-- The canonical balanced intervals cover `Fin N`. -/
theorem balancedIntervalBlock_cover (N L : ℕ) (hL : 0 < L) :
    ∀ i : Fin N, ∃ j : Fin L, i ∈ balancedIntervalBlock N L j := by
  intro i
  let candidates := (Finset.range L).filter fun j =>
    i.1 < balancedStart N L (j + 1)
  have hcandidates : candidates.Nonempty := by
    refine ⟨L - 1, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · have hpred : L - 1 + 1 = L := by omega
      rw [hpred, balancedStart_last N L hL]
      exact i.2
  let jn := candidates.min' hcandidates
  have hjmem : jn ∈ candidates := Finset.min'_mem candidates hcandidates
  have hjL : jn < L := Finset.mem_range.mp (Finset.mem_filter.mp hjmem).1
  have hupper : i.1 < balancedStart N L (jn + 1) :=
    (Finset.mem_filter.mp hjmem).2
  have hlower : balancedStart N L jn ≤ i.1 := by
    by_cases hj0 : jn = 0
    · simp [hj0]
    · have hjpred : jn - 1 < jn := Nat.sub_lt (Nat.zero_lt_of_ne_zero hj0) Nat.zero_lt_one
      have hjpredL : jn - 1 < L := hjpred.trans hjL
      have hnotmem : jn - 1 ∉ candidates := by
        intro hmem
        have hle := Finset.min'_le candidates (jn - 1) hmem
        omega
      have hnotupper : ¬i.1 < balancedStart N L (jn - 1 + 1) := by
        intro h
        apply hnotmem
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjpredL, h⟩
      have hpredsucc : jn - 1 + 1 = jn := by omega
      rw [hpredsucc] at hnotupper
      omega
  refine ⟨⟨jn, hjL⟩, ?_⟩
  simp [balancedIntervalBlock, hlower, hupper]

lemma balancedStart_step_le (N L j : ℕ) :
    balancedStart N L (j + 1) - balancedStart N L j ≤ N / L + 1 := by
  rw [balancedStart_step]
  split <;> omega

/-- Linear (non-wrapping) neighboring blocks have diameter at most two block widths. -/
theorem balancedIntervalBlock_linear_neighbor_dist
    (N L : ℕ) {i j : Fin L} {a b : Fin N}
    (ha : a ∈ balancedIntervalBlock N L i)
    (hb : b ∈ balancedIntervalBlock N L j)
    (hij : i = j ∨ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) :
    Nat.dist a.1 b.1 ≤ 2 * (N / L + 1) := by
  simp only [balancedIntervalBlock, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  rcases hij with hij | hij | hij
  · subst j
    have hstep := balancedStart_step_le N L i.1
    by_cases hab : a.1 ≤ b.1
    · rw [Nat.dist_eq_sub_of_le hab]
      omega
    · rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_not_ge hab)]
      omega
  · have hstepi := balancedStart_step_le N L i.1
    have hstepj := balancedStart_step_le N L j.1
    have hstepi' := Nat.sub_le_iff_le_add.mp hstepi
    have hstepj' := Nat.sub_le_iff_le_add.mp hstepj
    clear hstepi hstepj
    rw [← hij] at hb hstepj'
    have hab : a.1 ≤ b.1 := by
      omega
    rw [Nat.dist_eq_sub_of_le hab]
    omega
  · have hstepi := balancedStart_step_le N L i.1
    have hstepj := balancedStart_step_le N L j.1
    have hstepi' := Nat.sub_le_iff_le_add.mp hstepi
    have hstepj' := Nat.sub_le_iff_le_add.mp hstepj
    clear hstepi hstepj
    rw [← hij] at ha hstepi'
    have hba : b.1 ≤ a.1 := by
      omega
    rw [Nat.dist_eq_sub_of_le_right hba]
    omega

/-- Complementary cyclic distance for the last/first pair of blocks. -/
theorem balancedIntervalBlock_wrap_distance
    (N L : ℕ) (hL : 0 < L) (_hLN : L ≤ N)
    {i j : Fin L} {a b : Fin N}
    (ha : a ∈ balancedIntervalBlock N L i)
    (hb : b ∈ balancedIntervalBlock N L j)
    (hij : i ≠ j) (hi : i.1 = 0) (hj : j.1 + 1 = L) :
    N - Nat.dist a.1 b.1 ≤ 2 * (N / L + 1) := by
  simp only [balancedIntervalBlock, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hLtwo : 2 ≤ L := by
    by_contra hnot
    have hLone : L = 1 := by omega
    apply hij
    apply Fin.ext
    omega
  have hjpos : 1 ≤ j.1 := by omega
  have hbetween : balancedStart N L 1 ≤ balancedStart N L j.1 :=
    balancedStart_mono N L hjpos
  have haFirst : a.1 < balancedStart N L 1 := by
    simpa [hi] using ha.2
  have hab : a.1 ≤ b.1 := by
    omega
  have hfirst := balancedStart_step_le N L 0
  have hlast := balancedStart_step_le N L j.1
  have hfirst' := Nat.sub_le_iff_le_add.mp hfirst
  have hlast' := Nat.sub_le_iff_le_add.mp hlast
  clear hfirst hlast
  have hfirstBound : balancedStart N L 1 ≤ N / L + 1 := by
    simpa using hfirst'
  have hlastEnd : balancedStart N L (j.1 + 1) = N := by
    rw [hj, balancedStart_last N L hL]
  rw [hlastEnd] at hlast'
  rw [Nat.dist_eq_sub_of_le hab]
  apply Nat.sub_le_iff_le_add.mpr
  have hdistadd : b.1 - a.1 + a.1 = b.1 := Nat.sub_add_cancel hab
  omega

/-- Equality or cyclic adjacency of block indices. -/
def CyclicNeighbor {L : ℕ} (i j : Fin L) : Prop :=
  i = j ∨
    (i ≠ j ∧
      (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 ∨
        (i.1 = 0 ∧ j.1 + 1 = L) ∨ (j.1 = 0 ∧ i.1 + 1 = L)))

/-- Every pair of entries in equal or cyclically adjacent blocks lies in the band. -/
theorem balancedIntervalBlock_cyclic_neighbor_dist
    (N L W : ℕ) (hL : 0 < L) (hLN : L ≤ N)
    (hwidth : 2 * (N / L + 1) ≤ W)
    {i j : Fin L} {a b : Fin N}
    (ha : a ∈ balancedIntervalBlock N L i)
    (hb : b ∈ balancedIntervalBlock N L j)
    (hneighbor : CyclicNeighbor i j) :
    cyclicDist N a b ≤ W := by
  rcases hneighbor with hij | ⟨hij, hlinear | hlinear | hwrap | hwrap⟩
  · apply cyclicDist_le_of_dist_le
    exact (balancedIntervalBlock_linear_neighbor_dist N L ha hb (Or.inl hij)).trans hwidth
  · apply cyclicDist_le_of_dist_le
    exact (balancedIntervalBlock_linear_neighbor_dist N L ha hb
      (Or.inr (Or.inl hlinear))).trans hwidth
  · apply cyclicDist_le_of_dist_le
    exact (balancedIntervalBlock_linear_neighbor_dist N L ha hb
      (Or.inr (Or.inr hlinear))).trans hwidth
  · exact (min_le_right _ _).trans
      ((balancedIntervalBlock_wrap_distance N L hL hLN ha hb hij hwrap.1 hwrap.2).trans
        hwidth)
  · rw [cyclicDist, Nat.dist_comm]
    exact (min_le_right _ _).trans
      ((balancedIntervalBlock_wrap_distance N L hL hLN hb ha hij.symm hwrap.1 hwrap.2).trans
        hwidth)

/--
The canonical consecutive blocks produce the full cyclic-partition certificate
once the manuscript's elementary scale inequalities are supplied.
-/
noncomputable def canonicalBalancedCyclicPartition
    (N L W c0 C0 : ℕ) (hL : 0 < L) (hLN : L ≤ N)
    (hscaleLower : c0 * W ≤ N / L)
    (hscaleUpper : N / L + 1 ≤ C0 * W)
    (hblockCount : L * W ≤ C0 * N)
    (hwidth : 2 * (N / L + 1) ≤ W) :
    BalancedCyclicPartition N W := by
  classical
  let neighbors : Fin L → Finset (Fin L) := fun i =>
    Finset.univ.filter fun j => CyclicNeighbor i j
  refine
    { L := L
      hL_pos := hL
      blocks := balancedIntervalBlock N L
      d := N / L
      c0 := c0
      C0 := C0
      h_cover := balancedIntervalBlock_cover N L hL
      h_disjoint := balancedIntervalBlock_pairwise_disjoint N L
      h_card_lower := ?_
      h_card_upper := ?_
      h_scale_lower := hscaleLower
      h_scale_upper := hscaleUpper
      h_block_count := hblockCount
      neighbors := neighbors
      h_neighbor_dist := ?_ }
  · intro j
    rw [balancedIntervalBlock_card_eq N L hL j]
    split <;> omega
  · intro j
    rw [balancedIntervalBlock_card_eq N L hL j]
    split <;> omega
  · intro i j hj a ha b hb
    apply balancedIntervalBlock_cyclic_neighbor_dist N L W hL hLN hwidth ha hb
    simpa [neighbors] using hj

end Section5Formalization

