/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/InternalNet.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Section5Formalization.VolumetricNet
import Vendor.Section5Formalization.BlockEnergy

/-!
Turn a finite external cover into an internal net without assuming the set is
closed, measurable, or equipped with a continuous choice of Gram coordinates.
-/

open Set

namespace HighBandLSV.InternalNet

theorem exists_internal_net {E : Type*} [PseudoMetricSpace E]
    (S : Set E) (F : Finset E) (eps : Real)
    (hcover : ∀ x ∈ S, ∃ y ∈ F, dist x y ≤ eps) :
    ∃ G : Finset E, (∀ y ∈ G, y ∈ S) ∧ G.card ≤ F.card ∧
      ∀ x ∈ S, ∃ y ∈ G, dist x y ≤ 2 * eps := by
  classical
  let cells := F.filter (fun y => ∃ x ∈ S, dist x y ≤ eps)
  have hex : ∀ y : ↥cells, ∃ x ∈ S, dist x y.val ≤ eps :=
    fun y => (Finset.mem_filter.mp y.property).2
  let representative : ↥cells → E := fun y => Classical.choose (hex y)
  have hrep (y : ↥cells) : representative y ∈ S ∧ dist (representative y) y.val ≤ eps :=
    Classical.choose_spec (hex y)
  let G := Finset.univ.image representative
  refine ⟨G, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
    exact (hrep q).1
  · calc
      G.card ≤ (Finset.univ : Finset ↥cells).card := Finset.card_image_le
      _ = cells.card := by simp
      _ ≤ F.card := Finset.card_le_card (Finset.filter_subset _ _)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    have hycell : y ∈ cells := Finset.mem_filter.mpr ⟨hy, x, hx, hxy⟩
    let q : ↥cells := ⟨y, hycell⟩
    refine ⟨representative q, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩
    calc
      dist x (representative q) ≤ dist x y + dist y (representative q) :=
        dist_triangle _ _ _
      _ ≤ eps + eps := add_le_add hxy (by simpa only [dist_comm] using (hrep q).2)
      _ = 2 * eps := by ring

end HighBandLSV.InternalNet

#print axioms HighBandLSV.InternalNet.exists_internal_net

