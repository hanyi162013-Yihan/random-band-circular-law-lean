import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Actual contiguous-block periodicization routes

Rows are indexed by a block and its local position. The standard finite
sigma equivalence identifies them with consecutive positions in the full
matrix. The original route wraps around the full matrix; the block route
wraps within one block. They agree on every row at distance at least `H`
from its endpoints, and at most `2H` rows per block are exceptional.
-/

open scoped BigOperators

noncomputable section

namespace CircularLawSection6

section FinSlots

open Fin.NatCast

def cyclicFinSlot {N : ℕ} [NeZero N] (H : ℕ) (i : Fin N) (s : Fin (2 * H + 1)) : Fin N :=
  (i - (H : Fin N)) + (s.val : Fin N)

theorem cyclicFinSlot_injective {N H : ℕ} [NeZero N] (hfit : 2 * H + 1 ≤ N) (i : Fin N) :
    Function.Injective (cyclicFinSlot H i) := by
  intro s t h
  have hcast : (s.val : Fin N) = (t.val : Fin N) := add_left_cancel h
  have hv := congrArg Fin.val hcast
  simp only [Fin.val_natCast, Nat.mod_eq_of_lt (s.isLt.trans_le hfit),
    Nat.mod_eq_of_lt (t.isLt.trans_le hfit)] at hv
  exact Fin.ext hv

theorem cyclicFinSlot_val_of_interior {N H : ℕ} [NeZero N]
    (hfit : 2 * H + 1 ≤ N) (i : Fin N) (hi : H ≤ i.val) (hi' : i.val + H < N)
    (s : Fin (2 * H + 1)) :
    (cyclicFinSlot H i s).val = i.val - H + s.val := by
  have hh : ((H : Fin N) : ℕ) = H := by
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega : H < N)]
  have hs : ((s.val : Fin N) : ℕ) = s.val := by
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (s.isLt.trans_le hfit)]
  have hsub : (i - (H : Fin N)).val = i.val - H := by
    rw [Fin.coe_sub_iff_le.mpr (by simpa only [Fin.le_def, hh] using hi), hh]
  unfold cyclicFinSlot
  rw [Fin.val_add, hsub, hs, Nat.mod_eq_of_lt (by have := s.isLt; omega)]

end FinSlots

variable {q : ℕ} (len : Fin q → ℕ)

def fullBlockRoute [NeZero (∑ b, len b)] (H : ℕ)
    (i : (b : Fin q) × Fin (len b)) (s : Fin (2 * H + 1)) : (b : Fin q) × Fin (len b) :=
  finSigmaFinEquiv.symm (cyclicFinSlot H (finSigmaFinEquiv i) s)

def periodicBlockRoute [∀ b, NeZero (len b)] (H : ℕ)
    (i : (b : Fin q) × Fin (len b)) (s : Fin (2 * H + 1)) : (b : Fin q) × Fin (len b) :=
  ⟨i.1, cyclicFinSlot H i.2 s⟩

def blockBoundaryRows (H : ℕ) : Finset ((b : Fin q) × Fin (len b)) :=
  Finset.univ.filter (fun i => i.2.val < H ∨ len i.1 ≤ i.2.val + H)

theorem fullBlockRoute_injective [NeZero (∑ b, len b)] {H : ℕ}
    (hfit : ∀ b, 2 * H + 1 ≤ len b) (i : (b : Fin q) × Fin (len b)) :
    Function.Injective (fullBlockRoute len H i) := by
  have hle : len i.1 ≤ ∑ b, len b :=
    Finset.single_le_sum (fun b _ => Nat.zero_le (len b)) (Finset.mem_univ i.1)
  exact finSigmaFinEquiv.symm.injective.comp (cyclicFinSlot_injective ((hfit i.1).trans hle) _)

theorem periodicBlockRoute_injective [∀ b, NeZero (len b)] {H : ℕ}
    (hfit : ∀ b, 2 * H + 1 ≤ len b) (i : (b : Fin q) × Fin (len b)) :
    Function.Injective (periodicBlockRoute len H i) :=
  sigma_mk_injective.comp (cyclicFinSlot_injective (hfit i.1) i.2)

theorem block_prefix_add_length_le (b : Fin q) (hb : 0 < len b) :
    (∑ j : Fin b.val, len (Fin.castLE b.isLt.le j)) + len b ≤ ∑ j, len j := by
  let last : Fin (len b) := ⟨len b - 1, by omega⟩
  have h := (finSigmaFinEquiv (⟨b, last⟩ : (b : Fin q) × Fin (len b))).isLt
  rw [finSigmaFinEquiv_apply] at h
  dsimp only [last] at h
  omega

theorem blockRoutes_eq_off_boundary [∀ b, NeZero (len b)] [NeZero (∑ b, len b)]
    {H : ℕ} (hfit : ∀ b, 2 * H + 1 ≤ len b)
    (i : (b : Fin q) × Fin (len b)) (hi : i ∉ blockBoundaryRows len H)
    (s : Fin (2 * H + 1)) : fullBlockRoute len H i s = periodicBlockRoute len H i s := by
  have hi0 : H ≤ i.2.val ∧ i.2.val + H < len i.1 := by
    simpa only [blockBoundaryRows, Finset.mem_filter, Finset.mem_univ, true_and,
      not_or, not_lt, not_le] using hi
  have hend := block_prefix_add_length_le len i.1 (NeZero.pos (len i.1))
  have hle : len i.1 ≤ ∑ b, len b :=
    Finset.single_le_sum (fun b _ => Nat.zero_le (len b)) (Finset.mem_univ i.1)
  have hglobal0 : H ≤ (finSigmaFinEquiv i).val := by
    rw [finSigmaFinEquiv_apply]
    omega
  have hglobal1 : (finSigmaFinEquiv i).val + H < ∑ b, len b := by
    rw [finSigmaFinEquiv_apply]
    omega
  apply finSigmaFinEquiv.injective
  unfold fullBlockRoute periodicBlockRoute
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rw [cyclicFinSlot_val_of_interior ((hfit i.1).trans hle) _ hglobal0 hglobal1,
    finSigmaFinEquiv_apply, finSigmaFinEquiv_apply,
    cyclicFinSlot_val_of_interior (hfit i.1) i.2 hi0.1 hi0.2]
  dsimp only
  omega

theorem fin_boundary_card_le (m H : ℕ) :
    (Finset.univ.filter (fun i : Fin m => i.val < H ∨ m ≤ i.val + H)).card ≤ 2 * H := by
  classical
  let left := Finset.univ.filter (fun i : Fin m => i.val < H)
  let right := Finset.univ.filter (fun i : Fin m => m ≤ i.val + H)
  have hl : left.card ≤ H := by
    have h := Finset.card_le_card_of_injOn Fin.val
      (s := left) (t := Finset.range H)
      (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2)
      (fun _ _ _ _ h => Fin.ext h)
    simpa only [Finset.card_range] using h
  have hr : right.card ≤ H := by
    have h := Finset.card_le_card_of_injOn (fun i : Fin m => m - 1 - i.val)
      (s := right) (t := Finset.range H)
      (by
        intro i hi
        have hb := (Finset.mem_filter.mp hi).2
        have hm := i.isLt
        apply Finset.mem_range.mpr
        dsimp only
        omega)
      (by
        intro i _ j _ h
        apply Fin.ext
        have hi := i.isLt
        have hj := j.isLt
        dsimp only at h
        omega)
    simpa only [Finset.card_range] using h
  have heq : Finset.univ.filter (fun i : Fin m => i.val < H ∨ m ≤ i.val + H) = left ∪ right := by
    ext i
    simp only [left, right, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [heq]
  exact (Finset.card_union_le _ _).trans (by omega)

theorem blockBoundaryRows_card_le (H : ℕ) : (blockBoundaryRows len H).card ≤ q * (2 * H) := by
  classical
  have heq : blockBoundaryRows len H = Finset.univ.sigma
      (fun b => Finset.univ.filter (fun i : Fin (len b) => i.val < H ∨ len b ≤ i.val + H)) := by
    ext ⟨b, i⟩
    simp only [blockBoundaryRows, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma]
  rw [heq, Finset.card_sigma]
  calc
    _ ≤ ∑ b : Fin q, 2 * H := Finset.sum_le_sum (fun b _ => fin_boundary_card_le (len b) H)
    _ = _ := by simp

/-- Euclidean division gives genuine blocks covering every index. The last
block absorbs the remainder, so there is no uncovered terminal segment. -/
theorem exists_periodic_block_lengths {N m₀ : ℕ} (hm₀ : 0 < m₀) (hN : m₀ ≤ N) :
    ∃ (q : ℕ) (len : Fin q → ℕ), 0 < q ∧ (∑ b, len b) = N ∧
      ∀ b, m₀ ≤ len b ∧ len b < 2 * m₀ := by
  have hq : 0 < N / m₀ := Nat.div_pos hN hm₀
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  let lens : Fin (k + 1) → ℕ := fun i => if i = Fin.last k then m₀ + N % m₀ else m₀
  refine ⟨k + 1, lens, by omega, ?_, ?_⟩
  · rw [Fin.sum_univ_castSucc]
    simp only [lens, Fin.castSucc_ne_last, if_false, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    have hdiv := Nat.mod_add_div N m₀
    rw [hk, Nat.mul_succ, Nat.mul_comm m₀ k] at hdiv
    omega
  · intro b
    have hr := Nat.mod_lt N hm₀
    dsimp only [lens]
    split_ifs <;> omega

end CircularLawSection6
