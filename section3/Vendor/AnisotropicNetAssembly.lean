/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/AnisotropicNetAssembly.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.AnisotropicNets
import Vendor.BlockGeometry

/-! Independent anisotropic block nets assembled on the actual balanced partition. -/

noncomputable section
open scoped BigOperators
namespace HighBandLSV.Anisotropic
open HighBandLSV.BlockGeometry

local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev BlockLabel (h : Real) := {q : Label h // admissible q}
abbrev Labels (J : Nat) (h : Real) := Fin J → BlockLabel h

theorem blockLabel_card {h : Real} (hh : 0 < h) (hh1 : h ≤ 1) :
    (Fintype.card (BlockLabel h) : Real) ≤ (5 / h) ^ 3 := by
  have hc : Fintype.card (BlockLabel h) ≤ Fintype.card (Label h) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hcast : (Fintype.card (BlockLabel h) : Real) ≤ Fintype.card (Label h) := by
    exact_mod_cast hc
  exact hcast.trans (label_card_bound hh hh1)

theorem labels_card (J : Nat) {h : Real} (hh : 0 < h) (hh1 : h ≤ 1) :
    (Fintype.card (Labels J h) : Real) ≤ (5 / h) ^ (3 * J) := by
  simp only [Labels, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [pow_mul]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (blockLabel_card hh hh1) J

structure System {N J : Nat} (p : Partition N J) (h : Real) where
  points : (j : Fin J) → BlockLabel h → Finset (p.Block j)
  bounds : ∀ j q v, v ∈ points j q → v ∈ blockClass q.val
  cover : ∀ j q (u : p.Block j), u ∈ blockClass q.val → ∃ v ∈ points j q, dist u v ≤ h
  card : ∀ j q, ((points j q).card : Real) ≤
    (1024 * labelWeight q.val / h ^ 2) ^ (p.blocks j).card

def chooseSystem {N J : Nat} (p : Partition N J) (h : Real) (hh : 0 < h) : System p h := by
  classical
  have hex := fun (j : Fin J) (q : BlockLabel h) =>
    exists_internal_anisotropic_net (I := {i // i ∈ p.blocks j}) hh q.val q.property
  let F := fun j q => Classical.choose (hex j q)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro j q v hv
    exact (Classical.choose_spec (hex j q)).1 v hv
  · intro j q u hu
    simpa only [F] using (Classical.choose_spec (hex j q)).2.1 u hu
  · intro j q
    simpa only [F, Fintype.card_coe] using (Classical.choose_spec (hex j q)).2.2

namespace System
variable {N J : Nat} {p : Partition N J} {h : Real} (net : System p h)

abbrev Centers (q : Labels J h) := (j : Fin J) → {v // v ∈ net.points j (q j)}

def vector (q : Labels J h) (v : net.Centers q) : NormalEvents.Vec N :=
  p.assemble (fun j => (v j).val)

theorem block_class (q : Labels J h) (v : net.Centers q) (j : Fin J) :
    p.restrict (net.vector q v) j ∈ blockClass (q j).val := by
  rw [vector, p.restrict_assemble]
  exact net.bounds j (q j) (v j).val (v j).property

theorem covers_unit_sphere (hh : 0 < h) (u : NormalEvents.Vec N) (hu : ‖u‖ = 1) :
    ∃ q : Labels J h, ∃ v : net.Centers q,
      (∀ j, p.restrict u j ∈ blockClass (q j).val) ∧
      ‖u - net.vector q v‖ ≤ Real.sqrt (J : Real) * h := by
  classical
  have hlabel : ∀ j : Fin J, ∃ q : BlockLabel h, p.restrict u j ∈ blockClass q.val := by
    intro j
    have huj : ‖p.restrict u j‖ ≤ 1 := by simpa [hu] using p.restrict_norm_le u j
    obtain ⟨q, hq, hclass⟩ := exists_block_label hh (p.restrict u j) huj
    exact ⟨⟨q, hq⟩, hclass⟩
  choose q hq using hlabel
  have hcenter : ∀ j, ∃ v ∈ net.points j (q j), dist (p.restrict u j) v ≤ h := by
    intro j
    exact net.cover j (q j) (p.restrict u j) (hq j)
  choose v hv hd using hcenter
  let w : net.Centers q := fun j => ⟨v j, hv j⟩
  refine ⟨q, w, hq, ?_⟩
  exact p.assembled_error u v hh.le hd

theorem center_card (q : Labels J h) :
    (Fintype.card (net.Centers q) : Real) ≤
      ∏ j, (1024 * labelWeight (q j).val / h ^ 2) ^ (p.blocks j).card := by
  classical
  have he : Fintype.card (net.Centers q) = ∏ j, (net.points j (q j)).card := by
    simp [Centers, Fintype.card_pi]
  rw [he, Nat.cast_prod]
  exact Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _)
    (fun j _ => net.card j (q j))

end System
end HighBandLSV.Anisotropic

#print axioms HighBandLSV.Anisotropic.System.covers_unit_sphere
#print axioms HighBandLSV.Anisotropic.System.center_card

