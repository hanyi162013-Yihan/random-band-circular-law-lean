import ShortRingAnchor.Proposition38.Profile

/-!
# Proposition 3.8: elementary expansion of a finite cyclic block mask

Cook's broad connectivity is proved using heavy column blocks. The
constants are deliberately non-optimal: `δ = 1/(2m²)`, `ν = 1/(2m)`.
For bounded `m` these are uniform positive constants, which is all the
proof between (3.21) and (3.22) needs.
-/

noncomputable section
open scoped BigOperators
namespace ShortRingAnchor.Proposition38

def broadDelta (s : ℕ) : ℝ := 1 / (2 * ((s + 3 : ℕ) : ℝ) ^ 2)
def broadNu (s : ℕ) : ℝ := 1 / (2 * ((s + 3 : ℕ) : ℝ))

/-- Proposition 3.8, finite-ring geometry: a nonempty proper set of
blocks has an outgoing cyclic edge. -/
theorem exists_cyclic_boundary {s : ℕ} (K : Finset (Fin (s + 3)))
    (hne : K.Nonempty) (hproper : K ≠ Finset.univ) :
    ∃ b ∈ K, finRotate (s + 3) b ∉ K := by
  by_contra! hclosed
  obtain ⟨b, hb⟩ := hne
  have hit : ∀ n : ℕ, (finRotate (s + 3))^[n] b ∈ K := by
    intro n
    induction n with
    | zero => simpa using hb
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hclosed _ ih
  apply hproper
  apply Finset.eq_univ_of_forall
  intro j
  have h := hit (j - b).val
  rw [← finCycle_eq_finRotate_iterate, finCycle_apply] at h
  rw [add_comm b (j - b), sub_add_cancel] at h
  exact h

/-- Proposition 3.8, finite-ring geometry: one-step expansion gains at
least one entire block unless every block was already selected. -/
theorem card_cyclic_expansion {s : ℕ} (K : Finset (Fin (s + 3)))
    (hne : K.Nonempty) (hproper : K ≠ Finset.univ) :
    K.card + 1 ≤ (K ∪ K.image (finRotate (s + 3))).card := by
  obtain ⟨b, hb, hout⟩ := exists_cyclic_boundary K hne hproper
  apply Nat.succ_le_of_lt
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
  intro heq
  have hi : finRotate (s + 3) b ∈ K ∪ K.image (finRotate (s + 3)) :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb)
  rw [← heq] at hi
  exact hout hi

def heavyBlocks (s : ℕ) (c : Fin (s + 3) → ℝ) (T : ℝ) : Finset (Fin (s + 3)) :=
  Finset.univ.filter (fun b => broadDelta s * T ≤ c b)

/-- Proposition 3.8, Cook geometry: columns in light blocks have total
mass at most `ν |J|`. All inequalities are deterministic counting. -/
theorem heavy_mass_bound (s : ℕ) (c : Fin (s + 3) → ℝ) (T W : ℝ)
    (hT : 0 ≤ T) (hW : ∀ b, c b ≤ W) (hsum : ∑ b, c b = T) :
    T ≤ ((heavyBlocks s c T).card : ℝ) * W + broadNu s * T := by
  classical
  have hd : 0 ≤ broadDelta s * T := by unfold broadDelta; positivity
  have hpoint (b) : c b ≤
      (if b ∈ heavyBlocks s c T then W else 0) + broadDelta s * T := by
    by_cases hb : b ∈ heavyBlocks s c T
    · simp only [hb, if_true]
      exact (hW b).trans (le_add_of_nonneg_right hd)
    · have hh : c b < broadDelta s * T := by
        simpa only [heavyBlocks, Finset.mem_filter, Finset.mem_univ, true_and,
          not_le] using hb
      simpa only [hb, if_false, zero_add] using hh.le
  have h := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hpoint b)
  rw [hsum, Finset.sum_add_distrib] at h
  have heq : (∑ b : Fin (s + 3), if b ∈ heavyBlocks s c T then W else 0) =
      ((heavyBlocks s c T).card : ℝ) * W := by simp
  rw [heq] at h
  have hm : (0 : ℝ) < (s + 3 : ℕ) := by positivity
  have hdn : ((s + 3 : ℕ) : ℝ) * broadDelta s = broadNu s := by
    unfold broadDelta broadNu
    field_simp
    <;> ring
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_assoc, hdn] using h

/-- Proposition 3.8, Cook geometry: heavy blocks and their successors
already contain the required expanded number of scalar row positions. -/
theorem heavy_expansion_weight (s : ℕ) (c : Fin (s + 3) → ℝ) (T W : ℝ)
    (hT : 0 < T) (hW : 0 ≤ W) (hc : ∀ b, c b ≤ W)
    (hsum : ∑ b, c b = T) (hmax : T ≤ ((s + 3 : ℕ) : ℝ) * W) :
    min (((s + 3 : ℕ) : ℝ) * W) ((1 + broadNu s) * T) ≤
      (((heavyBlocks s c T ∪
        (heavyBlocks s c T).image (finRotate (s + 3))).card : ℕ) : ℝ) * W := by
  classical
  let K := heavyBlocks s c T
  have hmass := heavy_mass_bound s c T W hT.le hc hsum
  have hm : (3 : ℝ) ≤ (s + 3 : ℕ) := by exact_mod_cast Nat.le_add_left 3 s
  have hnu0 : 0 < broadNu s := by unfold broadNu; positivity
  have hnu1 : broadNu s < 1 := by
    unfold broadNu
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hne : K.Nonempty := by
    by_contra hn
    have he : K.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
    change T ≤ (K.card : ℝ) * W + broadNu s * T at hmass
    rw [he] at hmass
    norm_num at hmass
    nlinarith
  by_cases hall : K = Finset.univ
  · change min _ _ ≤ ((K ∪ K.image _).card : ℝ) * W
    rw [hall]
    rw [Finset.union_eq_left.mpr (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact min_le_left _ _
  · have hexp := card_cyclic_expansion K hne hall
    have hcard : (K.card : ℝ) + 1 ≤ ((K ∪ K.image (finRotate (s + 3))).card : ℝ) := by
      exact_mod_cast hexp
    have hnT : 2 * broadNu s * T ≤ W := by
      have hh := mul_le_mul_of_nonneg_left hmax (by positivity : 0 ≤ 2 * broadNu s)
      have heq : 2 * broadNu s * (((s + 3 : ℕ) : ℝ) * W) = W := by
        unfold broadNu
        field_simp
        <;> ring
      rwa [heq] at hh
    apply (min_le_right _ _).trans
    change (1 + broadNu s) * T ≤ ((K ∪ K.image _).card : ℝ) * W
    have hh := mul_le_mul_of_nonneg_right hcard hW
    change T ≤ (K.card : ℝ) * W + broadNu s * T at hmass
    nlinarith

end ShortRingAnchor.Proposition38
