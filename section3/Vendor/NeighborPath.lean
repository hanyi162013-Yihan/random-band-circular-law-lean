/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/NeighborPath.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Section5Formalization.DeterministicCompletion

/-!
An explicit simple nearest-neighbor path and its non-bijective forward map.
The map duplicates the terminal block and omits the initial block; the exact
product identity records this endpoint gain instead of assuming telescoping.
-/

open scoped BigOperators
open Section5Formalization

namespace HighBandLSV.NeighborPath

def Step {J : Nat} (i j : Fin J) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

structure Path {J : Nat} (k l : Fin J) where
  length : Nat
  vertices : Fin (length + 1) → Fin J
  injective : Function.Injective vertices
  initial : vertices 0 = k
  terminal : vertices (Fin.last length) = l
  adjacent : ∀ q : Fin length, Step (vertices q.castSucc) (vertices q.succ)

def increasing {J : Nat} (k : Fin J) (m : Nat) (hm : k.val + m < J)
    (q : Fin (m + 1)) : Fin J :=
  ⟨k.val + q.val, by omega⟩

theorem increasing_injective {J : Nat} (k : Fin J) (m : Nat)
    (hm : k.val + m < J) : Function.Injective (increasing k m hm) := by
  intro a b hab
  apply Fin.ext
  have := congrArg Fin.val hab
  simp only [increasing] at this
  omega

def decreasing {J : Nat} (k : Fin J) (m : Nat) (hm : m ≤ k.val)
    (q : Fin (m + 1)) : Fin J :=
  ⟨k.val - q.val, by omega⟩

theorem decreasing_injective {J : Nat} (k : Fin J) (m : Nat)
    (hm : m ≤ k.val) : Function.Injective (decreasing k m hm) := by
  intro a b hab
  apply Fin.ext
  have := congrArg Fin.val hab
  simp only [decreasing] at this
  omega

def between {J : Nat} (k l : Fin J) : Path k l := by
  by_cases h : k.val ≤ l.val
  · let m := l.val - k.val
    have hm : k.val + m < J := by dsimp [m]; omega
    refine ⟨m, increasing k m hm, increasing_injective k m hm, ?_, ?_, ?_⟩
    · apply Fin.ext
      simp [increasing]
    · apply Fin.ext
      simp only [increasing, Fin.val_last]
      dsimp [m]
      omega
    · intro q
      apply Or.inl
      change k.val + q.val + 1 = k.val + (q.val + 1)
      omega
  · let m := k.val - l.val
    have hm : m ≤ k.val := Nat.sub_le _ _
    refine ⟨m, decreasing k m hm, decreasing_injective k m hm, ?_, ?_, ?_⟩
    · apply Fin.ext
      simp [decreasing]
    · apply Fin.ext
      simp only [decreasing, Fin.val_last]
      dsimp [m]
      omega
    · intro q
      apply Or.inr
      simp only [decreasing, Fin.val_succ, Fin.val_castSucc]
      have hq := q.isLt
      dsimp [m] at hq
      omega

noncomputable def next {J m : Nat} (path : Fin (m + 1) → Fin J)
    (j : Fin J) : Fin J :=
  if h : ∃ q : Fin m, path q.castSucc = j then
    path (Classical.choose h).succ
  else j

theorem next_on {J m : Nat} (path : Fin (m + 1) → Fin J)
    (hp : Function.Injective path) (q : Fin m) :
    next path (path q.castSucc) = path q.succ := by
  classical
  have hex : ∃ a : Fin m, path a.castSucc = path q.castSucc := ⟨q, rfl⟩
  rw [next, dif_pos hex]
  have ha : Classical.choose hex = q := by
    exact Fin.castSucc_injective m (hp (Classical.choose_spec hex))
  rw [ha]

theorem next_off {J m : Nat} (path : Fin (m + 1) → Fin J)
    (j : Fin J) (hj : ∀ q : Fin m, path q.castSucc ≠ j) :
    next path j = j := by
  classical
  simp only [next, not_exists.mpr hj, dite_false]

theorem next_eq_or_step {J : Nat} {k l : Fin J} (p : Path k l) (j : Fin J) :
    next p.vertices j = j ∨ Step j (next p.vertices j) := by
  classical
  by_cases h : ∃ q : Fin p.length, p.vertices q.castSucc = j
  · obtain ⟨q, rfl⟩ := h
    rw [next_on _ p.injective]
    exact Or.inr (p.adjacent q)
  · exact Or.inl (next_off _ _ (not_exists.mp h))

theorem next_product {J m : Nat} (path : Fin (m + 1) → Fin J)
    (hp : Function.Injective path) (x : Fin J → Real) :
    (∏ j, x (next path j)) * x (path 0) =
      (∏ j, x j) * x (path (Fin.last m)) := by
  classical
  apply cyclic_path_map_product path hp x (fun j => x (next path j))
  · intro q
    rw [next_on _ hp]
  · intro j hj
    rw [next_off]
    intro q hq
    apply hj
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hq⟩

theorem path_product {J : Nat} {k l : Fin J} (p : Path k l)
    (x : Fin J → Real) :
    (∏ j, x (next p.vertices j)) * x k = (∏ j, x j) * x l := by
  simpa only [p.initial, p.terminal] using next_product p.vertices p.injective x

theorem path_product_ratio {J : Nat} {k l : Fin J} (p : Path k l)
    (x : Fin J → Real) (hk : 0 < x k) :
    (∏ j, x (next p.vertices j)) = (∏ j, x j) * (x l / x k) := by
  have h := path_product p x
  calc
    (∏ j, x (next p.vertices j)) = ((∏ j, x j) * x l) / x k :=
      (eq_div_iff (ne_of_gt hk)).2 h
    _ = (∏ j, x j) * (x l / x k) := by ring

theorem inverse_product_ratio {J : Nat} {k l : Fin J} (p : Path k l)
    (x : Fin J → Real) (hx : ∀ j, 0 < x j) :
    (∏ j, x j) / (∏ j, x (next p.vertices j)) = x k / x l := by
  have hprod : 0 < ∏ j, x j := Finset.prod_pos (fun j _ => hx j)
  rw [path_product_ratio p x (hx k)]
  field_simp

end HighBandLSV.NeighborPath

#print axioms HighBandLSV.NeighborPath.between
#print axioms HighBandLSV.NeighborPath.inverse_product_ratio

