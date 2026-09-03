/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealTensorization.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealRowBounds
import Vendor.AnisotropicNetAssembly
import Vendor.ProductEvents
import Vendor.NormalNetEvents
import Vendor.MatrixGeometry
import Vendor.FiniteProbability

/-! Tensorization of the actual real-entry column law over deleted row families. -/

noncomputable section
open MeasureTheory LivshytsProjectionFormalization
open scoped BigOperators ENNReal InnerProductSpace
namespace HighBandLSV.Anisotropic

theorem labelWeight_pos {h : Real} (hh : 0 < h) (q : Label h) : 0 < labelWeight q := by
  exact mul_pos (hh.trans_le (le_max_right _ _)) (hh.trans_le (le_max_right _ _))

theorem labelWeight_le_one {h : Real} (hh : 0 < h) (hh1 : h ≤ 1)
    (q : Label h) (hq : admissible q) : labelWeight q ≤ 1 := by
  have hx : max (xRadius q) h ≤ 1 := max_le hq.1 hh1
  have hy : max (yRadius q) h ≤ 1 := max_le (hq.2.1.trans hq.1) hh1
  have hx0 : 0 ≤ max (xRadius q) h := hh.le.trans (le_max_right _ _)
  have hy0 : 0 ≤ max (yRadius q) h := hh.le.trans (le_max_right _ _)
  exact (mul_le_mul hx hy hy0 (by norm_num)).trans_eq (by norm_num)

end HighBandLSV.Anisotropic
namespace HighBandLSV.RealBandModel
open HighBandLSV.Anisotropic
variable {N W : Nat} {c C rho : Real} (m : RealBandModel N W c C rho)

theorem inner_shifted_column (j : Fin N) (u : CV (Fin N)) (omega : Sample N) (z : Complex) :
    inner Complex u (NormalEvents.col (shifted (m.matrix omega) z) j) =
      m.linearForm j u (omega j) - star (u j) * z := by
  rw [MatrixGeometry.inner_shifted_column]
  rfl

theorem constraint_probability (u : CV (Fin N)) (S : Finset (Fin N)) (z : Complex) (d : Real) :
    m.law ((fun omega => shifted (m.matrix omega) z) ⁻¹' NormalNetEvents.constraint u S d) =
      ∏ j ∈ S, m.columnLaw j {x | ‖m.linearForm j u x - star (u j) * z‖ ≤ d} := by
  have he : (fun omega => shifted (m.matrix omega) z) ⁻¹' NormalNetEvents.constraint u S d =
      {omega | ∀ j ∈ S, ‖m.linearForm j u (omega j) - star (u j) * z‖ ≤ d} := by
    ext omega
    simp only [Set.mem_preimage, NormalNetEvents.constraint, Set.mem_setOf_eq, m.inner_shifted_column]
  rw [he]
  simpa only [law, Set.mem_setOf_eq] using ProductEvents.finite_constraints m.columnLaw S
    (fun j => {x | ‖m.linearForm j u x - star (u j) * z‖ ≤ d})

end HighBandLSV.RealBandModel
namespace HighBandLSV.RealTensorization
open HighBandLSV.Anisotropic

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def rowProduct {J : Nat} (r : Nat) (A W d h : Real)
    {k l : Fin J} (path : NeighborPath.Path k l) (q : Labels J h) : Real :=
  ∏ j, (A * W * d ^ 2 / labelWeight (q (NeighborPath.next path.vertices j)).val) ^ r

theorem point_probability {N J W r : Nat} {c C rho A h d : Real}
    (m : RealBandModel N W c C rho) (hGBL : RealFiniteGeometricBrascampLieb)
    (hrho : 0 < rho) (hc : 0 < c) (hW : 0 < W)
    (hA1 : 1 ≤ A) (hAone : 2 * (Real.exp 1 * rho) / Real.sqrt c ≤ A)
    (hAtwo : 8 * (Real.exp 1 * rho ^ 2) / c ≤ A) (hh : 0 < h) (hhd : h ≤ d)
    (p : BlockGeometry.Partition N J) (hband : PathGeometry.LocalBand p W)
    {i : Fin N} {k l : Fin J} (path : NeighborPath.Path k l)
    (net : System p h) (q : Labels J h) (sel : BlockGeometry.RowSelection p i r)
    (z : Complex) (v : net.Centers q) :
    m.law ((fun omega => shifted (m.matrix omega) z) ⁻¹'
      NormalNetEvents.constraint (net.vector q v) sel.allRows d) ≤
        ENNReal.ofReal (rowProduct r A W d h path q) := by
  classical
  let b : Fin J → Real := fun j =>
    A * W * d ^ 2 / labelWeight (q (NeighborPath.next path.vertices j)).val
  have hb : ∀ j, 0 ≤ b j := by
    intro j
    have ha : 0 ≤ A := zero_le_one.trans hA1
    have hw := labelWeight_pos hh (q (NeighborPath.next path.vertices j)).val
    dsimp [b]
    positivity
  have hp : ∀ j : Fin N,
      m.columnLaw j {x | ‖m.linearForm j (net.vector q v) x - star (net.vector q v j) * z‖ ≤ d} ≤
        ENNReal.ofReal (b (p.owner j)) := by
    intro j
    let target := NeighborPath.next path.vertices (p.owner j)
    exact m.anisotropic_row_probability hGBL hrho hc hW hA1 hAone hAtwo hh hhd
      j (p.blocks target) (fun a ha => PathGeometry.target_in_band p hband path j a ha)
      (q target).val (q target).property (net.vector q v) (net.block_class q v target)
      (star (net.vector q v j) * z)
  rw [m.constraint_probability]
  calc
    (∏ j ∈ sel.allRows, m.columnLaw j
        {x | ‖m.linearForm j (net.vector q v) x - star (net.vector q v j) * z‖ ≤ d}) ≤
      ∏ j ∈ sel.allRows, ENNReal.ofReal (b (p.owner j)) := Finset.prod_le_prod' (fun j _ => hp j)
    _ = ENNReal.ofReal (∏ j ∈ sel.allRows, b (p.owner j)) := by
      rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => hb (p.owner j))]
    _ = ENNReal.ofReal (rowProduct r A W d h path q) := by
      rw [sel.product_by_blocks b]
      rfl

theorem center_union_probability {N J W r : Nat} {c C rho A h d : Real}
    (m : RealBandModel N W c C rho) (hGBL : RealFiniteGeometricBrascampLieb)
    (hrho : 0 < rho) (hc : 0 < c) (hW : 0 < W)
    (hA1 : 1 ≤ A) (hAone : 2 * (Real.exp 1 * rho) / Real.sqrt c ≤ A)
    (hAtwo : 8 * (Real.exp 1 * rho ^ 2) / c ≤ A) (hh : 0 < h) (hhd : h ≤ d)
    (p : BlockGeometry.Partition N J) (hband : PathGeometry.LocalBand p W)
    {i : Fin N} {k l : Fin J} (path : NeighborPath.Path k l)
    (net : System p h) (q : Labels J h) (sel : BlockGeometry.RowSelection p i r) (z : Complex) :
    m.law (⋃ v : net.Centers q, (fun omega => shifted (m.matrix omega) z) ⁻¹'
      NormalNetEvents.constraint (net.vector q v) sel.allRows d) ≤
        ENNReal.ofReal ((Fintype.card (net.Centers q) : Real) * rowProduct r A W d h path q) := by
  apply FiniteProbability.finite_union
  intro v
  exact point_probability m hGBL hrho hc hW hA1 hAone hAtwo hh hhd p hband path net q sel z v

end HighBandLSV.RealTensorization

#print axioms HighBandLSV.RealTensorization.center_union_probability

