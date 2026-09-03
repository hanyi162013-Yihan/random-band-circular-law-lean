/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealNormalNetEvents.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.AnisotropicNetAssembly
import Vendor.NormalNetEvents

/-! A deterministic finite anisotropic cover of every bad normal space. -/

noncomputable section
open scoped BigOperators
namespace HighBandLSV.RealNormalNetEvents
open HighBandLSV.Anisotropic

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def endpoints {J : Nat} (h d : Real) (k l : Fin J) (q : Labels J h) : Prop :=
  labelWeight (q k).val ≤ d ^ 2 ∧ h / (4 * Real.sqrt (J : Real)) ≤ labelWeight (q l).val

abbrev EndpointLabels {J : Nat} (h d : Real) (k l : Fin J) :=
  {q : Labels J h // endpoints h d k l q}

theorem endpoint_labels_card {J : Nat} {h d : Real} (k l : Fin J) (hh : 0 < h) (hh1 : h ≤ 1) :
    (Fintype.card (EndpointLabels h d k l) : Real) ≤ (5 / h) ^ (3 * J) := by
  have hc : Fintype.card (EndpointLabels h d k l) ≤ Fintype.card (Labels J h) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hcast : (Fintype.card (EndpointLabels h d k l) : Real) ≤ Fintype.card (Labels J h) := by
    exact_mod_cast hc
  exact hcast.trans (labels_card J hh hh1)

theorem fixedBad_subset_net_union {N J r : Nat} (p : BlockGeometry.Partition N J)
    {h K d : Real} (net : System p h) (i : Fin N) (k l : Fin J)
    (rows : BlockGeometry.RowSelection p i r) (hJ : 0 < J) (hh : 0 < h) (hK : 0 ≤ K)
    (hhd : h ≤ d) (hmesh : h * Real.sqrt (J : Real) ≤ 1 / 4)
    (herror : (Real.sqrt (J : Real) * h) * K ≤ d) :
    NormalNetEvents.fixedBad p i k l K d ⊆
      ⋃ q : EndpointLabels h d k l, ⋃ v : net.Centers q.val,
        NormalNetEvents.constraint (net.vector q.val v) rows.allRows d := by
  classical
  intro A hA
  obtain ⟨hcap, u, hu, hsmall, hheavy⟩ := hA
  obtain ⟨q, v, hclass, happ⟩ := net.covers_unit_sphere hh u u.property
  have hend : endpoints h d k l q := by
    constructor
    · exact small_block_weight hh hhd (q k).val (hclass k) hsmall.le
    · exact heavy_block_weight hh (by exact_mod_cast hJ) hmesh (q l).val (hclass l) hheavy
  refine Set.mem_iUnion.mpr ⟨⟨q, hend⟩, Set.mem_iUnion.mpr ⟨v, ?_⟩⟩
  intro j hj
  have hji : j ≠ i := by
    intro heq
    exact rows.avoids_allRows (by simpa only [heq] using hj)
  exact NormalNetEvents.column_inner_error A i j u (net.vector q v)
    hu hji (hcap j) happ hK herror

end HighBandLSV.RealNormalNetEvents

#print axioms HighBandLSV.RealNormalNetEvents.fixedBad_subset_net_union

