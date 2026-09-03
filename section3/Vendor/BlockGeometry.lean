/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/BlockGeometry.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.PlanarNets
import Vendor.NormalEvents

open scoped BigOperators
open Set

noncomputable section

namespace HighBandLSV.BlockGeometry

open NormalEvents

structure Partition (N J : Nat) where
  blocks : Fin J → Finset (Fin N)
  cover : ∀ i : Fin N, ∃ j, i ∈ blocks j
  disjoint : Pairwise (fun j k => Disjoint (blocks j) (blocks k))

namespace Partition

variable {N J : Nat} (p : Partition N J)

def owner (i : Fin N) : Fin J := Classical.choose (p.cover i)

theorem owner_mem (i : Fin N) : i ∈ p.blocks (p.owner i) := Classical.choose_spec (p.cover i)

theorem owner_eq_of_mem (j : Fin J) {i : Fin N} (hi : i ∈ p.blocks j) : p.owner i = j := by
  by_contra h
  exact Finset.disjoint_left.mp (p.disjoint h) (p.owner_mem i) hi

theorem blocks_union : Finset.univ.biUnion p.blocks = Finset.univ := by
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
  exact p.cover i

theorem sum_blocks (f : Fin N → Real) : (∑ j, ∑ i ∈ p.blocks j, f i) = ∑ i, f i := by
  have hd : ∀ j ∈ (Finset.univ : Finset (Fin J)),
      ∀ k ∈ (Finset.univ : Finset (Fin J)), j ≠ k → Disjoint (p.blocks j) (p.blocks k) :=
    fun _ _ _ _ hjk => p.disjoint hjk
  rw [← Finset.sum_biUnion hd, p.blocks_union]

theorem sum_card_blocks : (∑ j, (p.blocks j).card) = N := by
  have h := p.sum_blocks (fun _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at h
  exact_mod_cast h

abbrev Block (j : Fin J) := EuclideanSpace Complex {i : Fin N // i ∈ p.blocks j}

def restrict (u : Vec N) (j : Fin J) : p.Block j :=
  WithLp.toLp 2 (fun i => u i.1)

def assemble (w : ∀ j, p.Block j) : Vec N :=
  WithLp.toLp 2 (fun i => w (p.owner i) ⟨i, p.owner_mem i⟩)

theorem restrict_assemble (w : ∀ j, p.Block j) (j : Fin J) :
    p.restrict (p.assemble w) j = w j := by
  ext i
  rcases i with ⟨a, ha⟩
  have ho := p.owner_eq_of_mem j ha
  change w (p.owner a) ⟨a, p.owner_mem a⟩ = w j ⟨a, ha⟩
  subst j
  rfl

theorem assemble_restrict (u : Vec N) : p.assemble (p.restrict u) = u := by
  ext i
  rfl

theorem restrict_sub (u v : Vec N) (j : Fin J) :
    p.restrict (u - v) j = p.restrict u j - p.restrict v j := by
  ext i
  rfl

theorem restrict_norm_sq (u : Vec N) (j : Fin J) :
    ‖p.restrict u j‖ ^ 2 = ∑ i ∈ p.blocks j, ‖u i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i : {i : Fin N // i ∈ p.blocks j}, ‖u i.1‖ ^ 2) = _
  exact Finset.sum_coe_sort (p.blocks j) (fun i : Fin N => ‖u i‖ ^ 2)

theorem sum_restrict_norm_sq (u : Vec N) : (∑ j, ‖p.restrict u j‖ ^ 2) = ‖u‖ ^ 2 := by
  simp_rw [p.restrict_norm_sq]
  rw [p.sum_blocks, PiLp.norm_sq_eq_of_L2]

theorem restrict_norm_le (u : Vec N) (j : Fin J) : ‖p.restrict u j‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [p.restrict_norm_sq, PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

theorem exists_heavy_block (hJ : 0 < J) (u : Vec N) (hu : ‖u‖ = 1) :
    ∃ j : Fin J, 1 / Real.sqrt (J : Real) ≤ ‖p.restrict u j‖ := by
  letI : Nonempty (Fin J) := Fin.pos_iff_nonempty.mp hJ
  obtain ⟨j, hj⟩ := Finite.exists_max (fun j => ‖p.restrict u j‖ ^ 2)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hj k)
  rw [p.sum_restrict_norm_sq, hu, one_pow] at hsum
  have hJp : 0 < (J : Real) := Nat.cast_pos.mpr hJ
  have hsq : (1 : Real) / J ≤ ‖p.restrict u j‖ ^ 2 := by
    apply (div_le_iff₀ hJp).mpr
    simpa [mul_comm] using hsum
  refine ⟨j, (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp ?_⟩
  have he : ((1 : Real) / Real.sqrt J) ^ 2 = 1 / (J : Real) := by
    rw [div_pow, one_pow, Real.sq_sqrt hJp.le]
  rwa [he]

theorem assembled_error (u : Vec N) (w : ∀ j, p.Block j) {h : Real} (hh : 0 ≤ h)
    (happrox : ∀ j, dist (p.restrict u j) (w j) ≤ h) :
    ‖u - p.assemble w‖ ≤ Real.sqrt (J : Real) * h := by
  have hs : ‖u - p.assemble w‖ ^ 2 ≤ (J : Real) * h ^ 2 := by
    rw [← p.sum_restrict_norm_sq]
    calc
      (∑ j, ‖p.restrict (u - p.assemble w) j‖ ^ 2) ≤ ∑ _j : Fin J, h ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [p.restrict_sub, p.restrict_assemble]
        apply (sq_le_sq₀ (norm_nonneg _) hh).mpr
        simpa [dist_eq_norm] using happrox j
      _ = (J : Real) * h ^ 2 := by simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ Real.sqrt (J : Real) * h)).mp
  simpa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg J)] using hs

end Partition

def canonical (N J : Nat) (hJ : 0 < J) : Partition N J where
  blocks := Section5Formalization.balancedIntervalBlock N J
  cover := Section5Formalization.balancedIntervalBlock_cover N J hJ
  disjoint := Section5Formalization.balancedIntervalBlock_pairwise_disjoint N J

structure RowSelection {N J : Nat} (p : Partition N J) (i : Fin N) (r : Nat) where
  rows : Fin J → Finset (Fin N)
  subset : ∀ j, rows j ⊆ p.blocks j
  avoids : ∀ j, i ∉ rows j
  card : ∀ j, (rows j).card = r

def chooseRows {N J : Nat} (p : Partition N J) (i : Fin N) (r : Nat)
    (hsize : ∀ j, r + 1 ≤ (p.blocks j).card) : RowSelection p i r := by
  classical
  have hex := Section5Formalization.exists_deleted_row_family
    p.blocks (fun _ => i) (r + 1) hsize
  let rows := Classical.choose hex
  have hrows := Classical.choose_spec hex
  exact {
    rows := rows
    subset := fun j => (hrows j).1.trans (Finset.erase_subset _ _)
    avoids := fun j hi => (Finset.mem_erase.mp ((hrows j).1 hi)).1 rfl
    card := fun j => by simpa [rows] using (hrows j).2 }

namespace RowSelection

variable {N J r : Nat} {p : Partition N J} {i : Fin N} (sel : RowSelection p i r)

def allRows : Finset (Fin N) := Finset.univ.biUnion sel.rows

theorem disjoint : Pairwise (fun j k => Disjoint (sel.rows j) (sel.rows k)) := by
  intro j k hjk
  exact (p.disjoint hjk).mono (sel.subset j) (sel.subset k)

theorem avoids_allRows : i ∉ sel.allRows := by
  intro hi
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
  exact sel.avoids j hj

theorem owner_of_mem (j : Fin J) {q : Fin N} (hq : q ∈ sel.rows j) : p.owner q = j :=
  p.owner_eq_of_mem j (sel.subset j hq)

theorem product_by_blocks {M : Type*} [CommMonoid M] (b : Fin J → M) :
    (∏ q ∈ sel.allRows, b (p.owner q)) = ∏ j, (b j) ^ r := by
  classical
  have hd : ∀ j ∈ (Finset.univ : Finset (Fin J)),
      ∀ k ∈ (Finset.univ : Finset (Fin J)), j ≠ k → Disjoint (sel.rows j) (sel.rows k) :=
    fun _ _ _ _ hjk => sel.disjoint hjk
  rw [allRows, Finset.prod_biUnion hd]
  apply Finset.prod_congr rfl
  intro j _
  calc
    (∏ q ∈ sel.rows j, b (p.owner q)) = ∏ _q ∈ sel.rows j, b j := by
      apply Finset.prod_congr rfl
      intro q hq
      rw [sel.owner_of_mem j hq]
    _ = b j ^ r := by simp [sel.card]

theorem card_allRows : sel.allRows.card = J * r := by
  classical
  have hd : ∀ j ∈ (Finset.univ : Finset (Fin J)),
      ∀ k ∈ (Finset.univ : Finset (Fin J)), j ≠ k → Disjoint (sel.rows j) (sel.rows k) :=
    fun _ _ _ _ hjk => sel.disjoint hjk
  rw [allRows, Finset.card_biUnion hd]
  simp [sel.card]

end RowSelection

#print axioms Partition.assembled_error
#print axioms chooseRows
#print axioms RowSelection.product_by_blocks

end HighBandLSV.BlockGeometry

