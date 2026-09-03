/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/PathGeometry.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.NeighborPath
import Vendor.BlockGeometry

/-! Every row-to-block assignment constructed from the path stays inside the band. -/

open Section5Formalization

namespace HighBandLSV.PathGeometry

theorem step_cyclicNeighbor {J : Nat} {i j : Fin J}
    (h : NeighborPath.Step i j) : CyclicNeighbor i j := by
  rcases h with h | h
  · right
    refine ⟨?_, Or.inl h⟩
    intro heq
    have := congrArg Fin.val heq
    omega
  · right
    refine ⟨?_, Or.inr (Or.inl h)⟩
    intro heq
    have := congrArg Fin.val heq
    omega

theorem next_cyclicNeighbor {J : Nat} {k l : Fin J}
    (p : NeighborPath.Path k l) (j : Fin J) :
    CyclicNeighbor j (NeighborPath.next p.vertices j) := by
  rcases NeighborPath.next_eq_or_step p j with h | h
  · exact Or.inl h.symm
  · exact step_cyclicNeighbor h

theorem next_cyclicNeighbor_rev {J : Nat} {k l : Fin J}
    (p : NeighborPath.Path k l) (j : Fin J) :
    CyclicNeighbor (NeighborPath.next p.vertices j) j := by
  rcases NeighborPath.next_eq_or_step p j with h | h
  · exact Or.inl h
  · apply step_cyclicNeighbor
    exact h.symm

def LocalBand {N J : Nat} (p : BlockGeometry.Partition N J) (W : Nat) : Prop :=
  ∀ a b, CyclicNeighbor a b → ∀ i ∈ p.blocks a, ∀ q ∈ p.blocks b,
    cyclicDist N i q ≤ W

theorem target_in_band {N J W : Nat} (p : BlockGeometry.Partition N J)
    (hp : LocalBand p W) {k l : Fin J} (path : NeighborPath.Path k l)
    (q : Fin N) (i : Fin N)
    (hi : i ∈ p.blocks (NeighborPath.next path.vertices (p.owner q))) :
    cyclicDist N i q ≤ W := by
  exact hp _ _ (next_cyclicNeighbor_rev path (p.owner q)) i hi q (p.owner_mem q)

end HighBandLSV.PathGeometry

#print axioms HighBandLSV.PathGeometry.target_in_band

