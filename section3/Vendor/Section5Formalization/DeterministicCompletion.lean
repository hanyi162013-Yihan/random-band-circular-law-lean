/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/Section5Formalization/DeterministicCompletion.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Section5Formalization.CyclicPartition

open scoped BigOperators

namespace Section5Formalization

/-!
# Remaining deterministic ingredients from Section 5

This file isolates statements which do not use probability.  In particular, the
cyclic path update below acts simultaneously on all source coordinates and is
the precise product-preserving map used in the change-of-variables argument.
-/

section CyclicPath

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]

/-- The source coordinates of a path are all path vertices except its endpoint. -/
def cyclicPathSources {s : ℕ} (path : Fin (s + 1) → ι) : Finset ι :=
  Finset.univ.image fun q : Fin s => path q.castSucc

/-- Telescoping identity for all simultaneous source-to-successor replacements. -/
theorem simultaneous_cyclic_path_telescope {s : ℕ} (value : Fin (s + 1) → M) :
    (∏ q : Fin s, value q.succ) * value 0 =
      (∏ q : Fin s, value q.castSucc) * value (Fin.last s) := by
  calc
    (∏ q : Fin s, value q.succ) * value 0 =
        value 0 * ∏ q : Fin s, value q.succ := mul_comm _ _
    _ = ∏ q : Fin (s + 1), value q := (Fin.prod_univ_succ value).symm
    _ = (∏ q : Fin s, value q.castSucc) * value (Fin.last s) :=
      Fin.prod_univ_castSucc value

/--
The full-coordinate product identity for a simultaneous cyclic path update.
Outside the path sources `y` equals `x`; at every source it receives the value
of the next path vertex.  No division and hence no nonvanishing assumption is
needed.
-/
theorem cyclic_path_map_product {s : ℕ} (path : Fin (s + 1) → ι)
    (hpath : Function.Injective path) (x y : ι → M)
    (hshift : ∀ q : Fin s, y (path q.castSucc) = x (path q.succ))
    (hfixed : ∀ i ∉ cyclicPathSources path, y i = x i) :
    (∏ i, y i) * x (path 0) = (∏ i, x i) * x (path (Fin.last s)) := by
  let S := cyclicPathSources path
  have hsource_inj : Function.Injective (fun q : Fin s => path q.castSucc) :=
    hpath.comp (Fin.castSucc_injective s)
  have hyS : (∏ i ∈ S, y i) = ∏ q : Fin s, x (path q.succ) := by
    calc
      (∏ i ∈ S, y i) =
          ∏ q ∈ (Finset.univ : Finset (Fin s)), y (path q.castSucc) := by
        simpa [S, cyclicPathSources] using
          (Finset.prod_image (f := y) hsource_inj.injOn)
      _ = ∏ q ∈ (Finset.univ : Finset (Fin s)), x (path q.succ) :=
        Finset.prod_congr rfl fun q _ => hshift q
      _ = ∏ q : Fin s, x (path q.succ) := by simp
  have hxS : (∏ i ∈ S, x i) = ∏ q : Fin s, x (path q.castSucc) := by
    simpa [S, cyclicPathSources] using
      (Finset.prod_image (f := x) hsource_inj.injOn)
  have hcomplement : (∏ i ∈ Sᶜ, y i) = ∏ i ∈ Sᶜ, x i := by
    apply Finset.prod_congr rfl
    intro i hi
    apply hfixed i
    simpa [S] using hi
  have htelescope := simultaneous_cyclic_path_telescope (fun q => x (path q))
  calc
    (∏ i, y i) * x (path 0) =
        ((∏ i ∈ Sᶜ, y i) * ∏ i ∈ S, y i) * x (path 0) := by
          rw [Finset.prod_compl_mul_prod]
    _ = ((∏ i ∈ Sᶜ, x i) * ∏ q : Fin s, x (path q.succ)) * x (path 0) := by
      rw [hcomplement, hyS]
    _ = (∏ i ∈ Sᶜ, x i) *
        ((∏ q : Fin s, x (path q.succ)) * x (path 0)) := by
      rw [mul_assoc]
    _ = (∏ i ∈ Sᶜ, x i) *
        ((∏ q : Fin s, x (path q.castSucc)) * x (path (Fin.last s))) := by
      rw [htelescope]
    _ = ((∏ i ∈ Sᶜ, x i) * ∏ i ∈ S, x i) * x (path (Fin.last s)) := by
      rw [hxS, mul_assoc]
    _ = (∏ i, x i) * x (path (Fin.last s)) := by
      rw [Finset.prod_compl_mul_prod]

end CyclicPath

section CyclicPathNormRatio

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [NormedField 𝕜]

/-- Taking norms in the simultaneous path-map identity preserves the endpoint ledger. -/
theorem cyclic_path_map_norm_product {s : ℕ} (path : Fin (s + 1) → ι)
    (hpath : Function.Injective path) (x y : ι → 𝕜)
    (hshift : ∀ q : Fin s, y (path q.castSucc) = x (path q.succ))
    (hfixed : ∀ i ∉ cyclicPathSources path, y i = x i) :
    (∏ i, ‖y i‖) * ‖x (path 0)‖ =
      (∏ i, ‖x i‖) * ‖x (path (Fin.last s))‖ := by
  have h := congrArg norm (cyclic_path_map_product path hpath x y hshift hfixed)
  simpa only [norm_mul, norm_prod] using h

/--
When the original product and the initial path coordinate do not vanish, the
global product-norm ratio is exactly the terminal-to-initial coordinate ratio.
-/
theorem cyclic_path_map_norm_ratio {s : ℕ} (path : Fin (s + 1) → ι)
    (hpath : Function.Injective path) (x y : ι → 𝕜)
    (hshift : ∀ q : Fin s, y (path q.castSucc) = x (path q.succ))
    (hfixed : ∀ i ∉ cyclicPathSources path, y i = x i)
    (hxprod : (∏ i, x i) ≠ 0) (hxstart : x (path 0) ≠ 0) :
    (∏ i, ‖y i‖) / (∏ i, ‖x i‖) =
      ‖x (path (Fin.last s))‖ / ‖x (path 0)‖ := by
  have hledger := cyclic_path_map_norm_product path hpath x y hshift hfixed
  have hxprod_norm : (∏ i, ‖x i‖) ≠ 0 := by
    have hnorm : ‖∏ i, x i‖ ≠ 0 := norm_ne_zero_iff.mpr hxprod
    simpa only [norm_prod] using hnorm
  have hxstart_norm : ‖x (path 0)‖ ≠ 0 := norm_ne_zero_iff.mpr hxstart
  field_simp [hxprod_norm, hxstart_norm]
  simpa [mul_comm] using hledger

end CyclicPathNormRatio

section DeletedRows

variable {α : Type*} [DecidableEq α]

/-- A block of size at least `d` still contains `d - 1` selectable rows after one deletion. -/
theorem exists_deleted_row_set (B : Finset α) (i : α) (d : ℕ) (hd : d ≤ B.card) :
    ∃ R ⊆ B.erase i, R.card = d - 1 := by
  apply Finset.exists_subset_card_eq
  exact (Nat.sub_le_sub_right hd 1).trans Finset.pred_card_le_card_erase

/-- The deleted-row selection can be made simultaneously for every block. -/
theorem exists_deleted_row_family {κ : Type*} (blocks : κ → Finset α) (pivot : κ → α)
    (d : ℕ) (hd : ∀ q, d ≤ (blocks q).card) :
    ∃ rows : κ → Finset α,
      ∀ q, rows q ⊆ (blocks q).erase (pivot q) ∧ (rows q).card = d - 1 := by
  classical
  have hexists : ∀ q, ∃ R ⊆ (blocks q).erase (pivot q), R.card = d - 1 :=
    fun q => exists_deleted_row_set (blocks q) (pivot q) d (hd q)
  choose rows hsubset hcard using hexists
  exact ⟨rows, fun q => ⟨hsubset q, hcard q⟩⟩

end DeletedRows

section BlockProductNet

variable {E : Type*} [SeminormedAddCommGroup E]

/-- Euclidean aggregate of the errors in a family of blocks. -/
noncomputable def blockError {L : ℕ} (e : Fin L → E) : ℝ :=
  Real.sqrt (∑ q, ‖e q‖ ^ 2)

/-- Per-block error `η` produces total block-product error at most `√L η`. -/
theorem block_product_error_le_sqrt {L : ℕ} (e : Fin L → E) {η : ℝ}
    (hη : 0 ≤ η) (he : ∀ q, ‖e q‖ ≤ η) :
    blockError e ≤ Real.sqrt (L : ℝ) * η := by
  have hterm : ∀ q : Fin L, ‖e q‖ ^ 2 ≤ η ^ 2 := by
    intro q
    exact (sq_le_sq₀ (norm_nonneg (e q)) hη).2 (he q)
  have hsum : (∑ q, ‖e q‖ ^ 2) ≤ (L : ℝ) * η ^ 2 := by
    calc
      (∑ q, ‖e q‖ ^ 2) ≤ ∑ _q : Fin L, η ^ 2 :=
        Finset.sum_le_sum fun q _ => hterm q
      _ = (L : ℝ) * η ^ 2 := by simp
  have hsum_nonneg : 0 ≤ ∑ q, ‖e q‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hη)).mp
  rw [Real.sq_sqrt hsum_nonneg, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ L)]
  exact hsum

end BlockProductNet

section FiniteBlockNets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every finite-dimensional closed ball has a finite internal `η`-net. -/
theorem exists_finite_closedBall_net {R η : ℝ} (hη : 0 < η) :
    ∃ net : Finset E,
      (∀ y ∈ net, ‖y‖ ≤ R) ∧
      ∀ x : E, ‖x‖ ≤ R → ∃ y ∈ net, dist x y ≤ η := by
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  obtain ⟨N, hNsubset, hNfinite, hNcover⟩ :=
    Metric.finite_approx_of_totallyBounded
      (isCompact_closedBall (0 : E) R).totallyBounded η hη
  refine ⟨hNfinite.toFinset, ?_, ?_⟩
  · intro y hy
    have hyN : y ∈ N := hNfinite.mem_toFinset.mp hy
    simpa using Metric.mem_closedBall.mp (hNsubset hyN)
  · intro x hx
    have hxball : x ∈ Metric.closedBall (0 : E) R := by simpa using hx
    have hxcover := hNcover hxball
    simp only [Set.mem_iUnion, Metric.mem_ball] at hxcover
    obtain ⟨y, hyN, hxy⟩ := hxcover
    exact ⟨y, hNfinite.mem_toFinset.mpr hyN, hxy.le⟩

/-- Cartesian product of the finite nets assigned to the blocks. -/
noncomputable def blockProductNet {L : ℕ} (nets : Fin L → Finset E) :
    Finset (Fin L → E) := by
  classical
  exact Fintype.piFinset nets

@[simp]
theorem mem_blockProductNet {L : ℕ} {nets : Fin L → Finset E} {x : Fin L → E} :
    x ∈ blockProductNet nets ↔ ∀ q, x q ∈ nets q := by
  classical
  simp [blockProductNet]

@[simp]
theorem blockProductNet_card {L : ℕ} (nets : Fin L → Finset E) :
    (blockProductNet nets).card = ∏ q, (nets q).card := by
  classical
  simp [blockProductNet]

/-- A uniform local cardinality bound tensorizes to the corresponding power. -/
theorem blockProductNet_card_le_pow {L Q : ℕ} (nets : Fin L → Finset E)
    (hcard : ∀ q, (nets q).card ≤ Q) :
    (blockProductNet nets).card ≤ Q ^ L := by
  rw [blockProductNet_card]
  calc
    (∏ q, (nets q).card) ≤ ∏ _q : Fin L, Q :=
      Finset.prod_le_prod' fun q _ => hcard q
    _ = Q ^ L := by simp

/-- Choosing one approximant in every local net gives the advertised global error. -/
theorem blockProductNet_approximates {L : ℕ} (nets : Fin L → Finset E) {η : ℝ}
    (hη : 0 ≤ η)
    (hnet : ∀ q (u : E), ∃ v ∈ nets q, ‖u - v‖ ≤ η) (x : Fin L → E) :
    ∃ y ∈ blockProductNet nets, blockError (x - y) ≤ Real.sqrt (L : ℝ) * η := by
  classical
  have hchoices : ∀ q, ∃ v ∈ nets q, ‖x q - v‖ ≤ η := fun q => hnet q (x q)
  choose y hymem hyerror using hchoices
  refine ⟨y, mem_blockProductNet.mpr hymem, ?_⟩
  apply block_product_error_le_sqrt (e := x - y) hη
  intro q
  simpa using hyerror q

end FiniteBlockNets

end Section5Formalization

