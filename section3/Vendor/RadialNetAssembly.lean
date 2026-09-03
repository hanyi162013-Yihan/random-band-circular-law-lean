/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RadialNetAssembly.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.BlockGeometry
import Vendor.RadialLedger

/-! Finite radial block nets assembled into genuine vectors in the original space. -/

open scoped BigOperators
open HighBandLSV.BlockGeometry

noncomputable section

namespace HighBandLSV.RadialNetAssembly

abbrev Label (h : Real) := Fin (PlanarNets.levelCount h)
abbrev Labels (J : Nat) (h : Real) := Fin J → Label h

def radius (h : Real) (q : Label h) : Real := (q.val : Real) * h
def weight (h : Real) (q : Label h) : Real := (max (radius h q) h) ^ 2

theorem radius_nonneg {h : Real} (hh : 0 ≤ h) (q : Label h) : 0 ≤ radius h q := by
  unfold radius
  positivity

theorem weight_pos {h : Real} (hh : 0 < h) (q : Label h) : 0 < weight h q := by
  unfold weight
  have hm : 0 < max (radius h q) h := lt_of_lt_of_le hh (le_max_right _ _)
  positivity

theorem weight_le_one {h : Real} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (q : Label h) (hq : radius h q ≤ 1) : weight h q ≤ 1 := by
  have hm : 0 ≤ max (radius h q) h := le_trans hh (le_max_right _ _)
  have hm1 : max (radius h q) h ≤ 1 := max_le hq hh1
  unfold weight
  nlinarith

theorem radius_zero_or_ge {h : Real} (hh : 0 < h) (q : Label h) :
    radius h q = 0 ∨ h ≤ radius h q := by
  by_cases hq : q.val = 0
  · exact Or.inl (by simp [radius, hq])
  · right
    have hnat : 1 ≤ q.val := by omega
    have hcast : (1 : Real) ≤ q.val := by exact_mod_cast hnat
    unfold radius
    nlinarith

theorem exists_label {h x : Real} (hh : 0 < h) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ q : Label h, radius h q ≤ x ∧ x ≤ radius h q + h := by
  let k := Nat.floor (x / h)
  have hk : k ≤ Nat.ceil (1 / h) := by
    apply Nat.floor_le_of_le
    exact (div_le_div_of_nonneg_right hx1 hh.le).trans (Nat.le_ceil _)
  let q : Label h := ⟨k, by
    change k < Nat.ceil (1 / h) + 1
    omega⟩
  refine ⟨q, ?_, ?_⟩
  · have hf := Nat.floor_le (div_nonneg hx hh.le)
    have hm := (le_div_iff₀ hh).mp hf
    simpa only [radius, q, k] using hm
  · have hf := Nat.lt_floor_add_one (x / h)
    have hm := (div_lt_iff₀ hh).mp hf
    change x ≤ (k : Real) * h + h
    dsimp [k]
    nlinarith

structure System {N J : Nat} (p : BlockGeometry.Partition N J) (h : Real) where
  points : (j : Fin J) → Label h → Finset (p.Block j)
  bounds : ∀ j q v, v ∈ points j q → radius h q ≤ ‖v‖ ∧ ‖v‖ ≤ radius h q + h
  cover : ∀ j q (u : p.Block j), radius h q ≤ ‖u‖ → ‖u‖ ≤ radius h q + h →
    ∃ v ∈ points j q, ‖u - v‖ ≤ h
  card : ∀ j q, ((points j q).card : Real) ≤
    (25 * weight h q / h ^ 2) ^ (p.blocks j).card

def chooseSystem {N J : Nat} (p : BlockGeometry.Partition N J)
    (h : Real) (hh : 0 < h) : System p h := by
  classical
  have hex := fun (j : Fin J) (q : Label h) =>
    PlanarNets.exists_annular_net {i // i ∈ p.blocks j}
      (radius_nonneg hh.le q) hh
  let F := fun j q => Classical.choose (hex j q)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro j q v hv
    exact (Classical.choose_spec (hex j q)).1 v hv
  · intro j q u hlow hupp
    simpa only [dist_eq_norm, F] using (Classical.choose_spec (hex j q)).2.1 u hlow hupp
  · intro j q
    simpa only [weight, Fintype.card_coe, F] using (Classical.choose_spec (hex j q)).2.2

namespace System

variable {N J : Nat} {p : BlockGeometry.Partition N J} {h : Real}
variable (net : System p h)

abbrev Centers (q : Labels J h) := (j : Fin J) → {v // v ∈ net.points j (q j)}

def vector (q : Labels J h) (v : net.Centers q) : NormalEvents.Vec N :=
  p.assemble (fun j => (v j).val)

theorem restrict_vector (q : Labels J h) (v : net.Centers q) (j : Fin J) :
    p.restrict (net.vector q v) j = (v j).val := p.restrict_assemble _ _

theorem vector_block_bounds (q : Labels J h) (v : net.Centers q) (j : Fin J) :
    radius h (q j) ≤ ‖p.restrict (net.vector q v) j‖ ∧
      ‖p.restrict (net.vector q v) j‖ ≤ radius h (q j) + h := by
  rw [net.restrict_vector]
  exact net.bounds j (q j) (v j).val (v j).property

theorem center_count (q : Labels J h) :
    (Fintype.card (net.Centers q) : Real) ≤
      ∏ j, (25 * weight h (q j) / h ^ 2) ^ (p.blocks j).card := by
  classical
  calc
    (Fintype.card (net.Centers q) : Real) =
        ∏ j, ((net.points j (q j)).card : Real) := by
      simp only [Centers, Fintype.card_pi, Fintype.card_coe, Nat.cast_prod]
    _ ≤ ∏ j, (25 * weight h (q j) / h ^ 2) ^ (p.blocks j).card := by
      apply Finset.prod_le_prod
      · intro j _
        exact Nat.cast_nonneg _
      · intro j _
        exact net.card j (q j)

theorem approximates (hh : 0 ≤ h) (u : NormalEvents.Vec N) (q : Labels J h)
    (hq : ∀ j, radius h (q j) ≤ ‖p.restrict u j‖ ∧
      ‖p.restrict u j‖ ≤ radius h (q j) + h) :
    ∃ v : net.Centers q, ‖u - net.vector q v‖ ≤ Real.sqrt (J : Real) * h := by
  classical
  have hv : ∀ j, ∃ v ∈ net.points j (q j), ‖p.restrict u j - v‖ ≤ h :=
    fun j => net.cover j (q j) (p.restrict u j) (hq j).1 (hq j).2
  choose v hv herr using hv
  let center : net.Centers q := fun j => ⟨v j, hv j⟩
  refine ⟨center, ?_⟩
  exact p.assembled_error u v hh (fun j => by simpa only [dist_eq_norm] using herr j)

theorem covers_unit_sphere (hh : 0 < h) (u : NormalEvents.Vec N) (hu : ‖u‖ = 1) :
    ∃ q : Labels J h, (∀ j, radius h (q j) ≤ 1) ∧
      (∀ j, radius h (q j) ≤ ‖p.restrict u j‖ ∧
        ‖p.restrict u j‖ ≤ radius h (q j) + h) ∧
      ∃ v : net.Centers q, ‖u - net.vector q v‖ ≤ Real.sqrt (J : Real) * h := by
  classical
  have hex : ∀ j, ∃ q : Label h, radius h q ≤ ‖p.restrict u j‖ ∧
      ‖p.restrict u j‖ ≤ radius h q + h := by
    intro j
    apply exists_label hh (norm_nonneg _)
    exact (p.restrict_norm_le u j).trans_eq hu
  choose q hq using hex
  exact ⟨q, fun j => (hq j).1.trans ((p.restrict_norm_le u j).trans_eq hu),
    hq, net.approximates hh.le u q hq⟩

end System

theorem small_weight {h delta : Real} (hh : 0 ≤ h) (hhd : h ≤ delta)
    (q : Label h) (hq : radius h q ≤ delta) : weight h q ≤ delta ^ 2 := by
  have hm : max (radius h q) h ≤ delta := max_le hq hhd
  have hm0 : 0 ≤ max (radius h q) h := le_trans hh (le_max_right _ _)
  unfold weight
  nlinarith

theorem heavy_weight {J : Nat} {h x : Real} (hJ : 0 < J) (hh : 0 ≤ h)
    (q : Label h) (hx : 1 / Real.sqrt (J : Real) ≤ x)
    (hxq : x ≤ radius h q + h) (hmesh : h * Real.sqrt (J : Real) ≤ 1 / 2) :
    1 / (4 * (J : Real)) ≤ weight h q := by
  have hJr : 0 < (J : Real) := Nat.cast_pos.mpr hJ
  have hs : 0 < Real.sqrt (J : Real) := Real.sqrt_pos.2 hJr
  have hxmul : 1 ≤ x * Real.sqrt (J : Real) := (div_le_iff₀ hs).mp hx
  have hR : 1 / 2 ≤ radius h q * Real.sqrt (J : Real) := by
    have hmul := mul_le_mul_of_nonneg_right hxq hs.le
    nlinarith
  have hm : 1 / 2 ≤ max (radius h q) h * Real.sqrt (J : Real) :=
    hR.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hs.le)
  have hid : (max (radius h q) h * Real.sqrt (J : Real)) ^ 2 =
      weight h q * J := by
    rw [mul_pow, Real.sq_sqrt hJr.le]
    rfl
  apply (div_le_iff₀ (by positivity : 0 < 4 * (J : Real))).2
  nlinarith [sq_nonneg (max (radius h q) h * Real.sqrt (J : Real) - 1 / 2)]

end HighBandLSV.RadialNetAssembly

#print axioms HighBandLSV.RadialNetAssembly.chooseSystem
#print axioms HighBandLSV.RadialNetAssembly.System.covers_unit_sphere
#print axioms HighBandLSV.RadialNetAssembly.heavy_weight

