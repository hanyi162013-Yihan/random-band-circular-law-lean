/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/PlanarTensorization.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.PlanarRowBounds
import Vendor.NormalNetEvents
import Vendor.FiniteProbability
import Vendor.MatrixGeometry

/-! Independent original columns give the complete net-point probability product. -/

open scoped BigOperators ENNReal
open MeasureTheory Set

noncomputable section

namespace HighBandLSV.PlanarTensorization

theorem projected_column_formula {N W : Nat} {c C L : Real}
    (m : PlanarBandModel N W c C L) (omega : MatrixSample N) (z : Complex)
    (v : NormalEvents.Vec N) (j : Fin N) :
    inner Complex v (NormalEvents.col (shifted (m.matrix omega) z) j) =
      m.linearForm j (fun i => v i) (omega j) - star (v j) * z := by
  rw [MatrixGeometry.inner_shifted_column]
  unfold PlanarBandModel.linearForm PlanarBandModel.coefficients PlanarBandModel.matrix
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

def rowProduct {J : Nat} (r : Nat) (A N W delta h : Real)
    {k l : Fin J} (path : NeighborPath.Path k l)
    (q : RadialNetAssembly.Labels J h) : Real :=
  ∏ j, (PlanarRowBounds.bound A N W delta
    (RadialNetAssembly.weight h (q (NeighborPath.next path.vertices j)))) ^ r

theorem point_probability {N J W r : Nat} {c C L A h delta : Real}
    (m : PlanarBandModel N W c C L) (p : BlockGeometry.Partition N J)
    (hband : PathGeometry.LocalBand p W) {k l : Fin J} (path : NeighborPath.Path k l)
    (net : RadialNetAssembly.System p h) (q : RadialNetAssembly.Labels J h)
    (v : net.Centers q) {i : Fin N} (rows : BlockGeometry.RowSelection p i r) (z : Complex)
    (hN : 0 < N) (hc : 0 < c) (hW : 0 < W) (hL : 0 ≤ L)
    (hA1 : 1 ≤ A) (hA : Real.pi * L / c ≤ A) (hh : 0 < h) (hhd : h ≤ delta) :
    m.law ((fun omega => shifted (m.matrix omega) z) ⁻¹'
      NormalNetEvents.constraint (net.vector q v) rows.allRows delta) ≤
        ENNReal.ofReal (rowProduct r A N W delta h path q) := by
  classical
  let u : Fin N → Complex := fun j => net.vector q v j
  have hevent : (fun omega => shifted (m.matrix omega) z) ⁻¹'
      NormalNetEvents.constraint (net.vector q v) rows.allRows delta =
        {omega | ∀ j ∈ rows.allRows,
          ‖m.linearForm j u (omega j) - star (u j) * z‖ ≤ delta} := by
    ext omega
    simp only [mem_preimage, NormalNetEvents.constraint, mem_setOf_eq,
      projected_column_formula, u]
  rw [hevent, m.selected_rows_probability (fun _ => u) (fun j => star (u j) * z)]
  calc
    (∏ j ∈ rows.allRows,
        m.columnLaw j {x | ‖m.linearForm j u x - star (u j) * z‖ ≤ delta}) ≤
      ENNReal.ofReal (∏ j ∈ rows.allRows, PlanarRowBounds.bound A N W delta
        (RadialNetAssembly.weight h (q (NeighborPath.next path.vertices (p.owner j))))) := by
      apply FiniteProbability.product_bound
      · intro j _
        exact PlanarRowBounds.bound_nonneg (zero_le_one.trans hA1)
          (Nat.cast_nonneg N) (Nat.cast_nonneg W) (RadialNetAssembly.weight_pos hh _).le
      · intro j _
        exact PlanarRowBounds.center_row_probability m p hband path net q v j
          (star (u j) * z) hN hc hW hL hA1 hA hh hhd
    _ = ENNReal.ofReal (rowProduct r A N W delta h path q) := by
      congr 1
      exact rows.product_by_blocks (fun j => PlanarRowBounds.bound A N W delta
        (RadialNetAssembly.weight h (q (NeighborPath.next path.vertices j))))

theorem center_union_probability {N J W r : Nat} {c C L A h delta : Real}
    (m : PlanarBandModel N W c C L) (p : BlockGeometry.Partition N J)
    (hband : PathGeometry.LocalBand p W) {k l : Fin J} (path : NeighborPath.Path k l)
    (net : RadialNetAssembly.System p h) (q : RadialNetAssembly.Labels J h)
    {i : Fin N} (rows : BlockGeometry.RowSelection p i r) (z : Complex)
    (hN : 0 < N) (hc : 0 < c) (hW : 0 < W) (hL : 0 ≤ L)
    (hA1 : 1 ≤ A) (hA : Real.pi * L / c ≤ A) (hh : 0 < h) (hhd : h ≤ delta) :
    m.law (⋃ v : net.Centers q, (fun omega => shifted (m.matrix omega) z) ⁻¹'
      NormalNetEvents.constraint (net.vector q v) rows.allRows delta) ≤
        ENNReal.ofReal ((Fintype.card (net.Centers q) : Real) *
          rowProduct r A N W delta h path q) := by
  classical
  apply FiniteProbability.finite_union
  intro v
  exact point_probability m p hband path net q v rows z hN hc hW hL hA1 hA hh hhd

theorem center_union_endpoint_bound {N J W r : Nat} {c C L A h delta : Real}
    (m : PlanarBandModel N W c C L) (p : BlockGeometry.Partition N J)
    (hband : PathGeometry.LocalBand p W) {k l : Fin J} (path : NeighborPath.Path k l)
    (net : RadialNetAssembly.System p h) (q : RadialNetAssembly.Labels J h)
    {i : Fin N} (rows : BlockGeometry.RowSelection p i r) (z : Complex)
    (hN : 0 < N) (hJ : 0 < J) (hc : 0 < c) (hW : 0 < W) (hL : 0 ≤ L)
    (hA1 : 1 ≤ A) (hA : Real.pi * L / c ≤ A) (hh : 0 < h) (hh1 : h ≤ 1)
    (hhd : h ≤ delta) (hsize : ∀ j, r ≤ (p.blocks j).card)
    (hq : NormalNetEvents.admissible h delta k l q) :
    m.law (⋃ v : net.Centers q, (fun omega => shifted (m.matrix omega) z) ⁻¹'
      NormalNetEvents.constraint (net.vector q v) rows.allRows delta) ≤
        ENNReal.ofReal ((25 / h ^ 2) ^ N * (A * (N : Real) * W * delta ^ 2) ^ (r * J) *
          (4 * (J : Real) * delta ^ 2) ^ r) := by
  classical
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  have hrow0 : 0 ≤ rowProduct r A N W delta h path q := by
    apply Finset.prod_nonneg
    intro j _
    exact pow_nonneg (PlanarRowBounds.bound_nonneg hA0 (Nat.cast_nonneg N)
      (Nat.cast_nonneg W) (RadialNetAssembly.weight_pos hh _).le) r
  have hcancel := RadialLedger.radial_to_endpoint_bound path
    (fun j => (p.blocks j).card) (fun j => RadialNetAssembly.weight h (q j))
    (A := 25) (B := A * (N : Real) * W * delta ^ 2) (delta := delta)
    hJ (by norm_num) (by positivity) hh
    (fun j => RadialNetAssembly.weight_pos hh (q j))
    (fun j => RadialNetAssembly.weight_le_one hh.le hh1 (q j) (hq.1 j))
    hsize p.sum_card_blocks hq.2.1 hq.2.2
  apply (center_union_probability m p hband path net q rows z
    hN hc hW hL hA1 hA hh hhd).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    (Fintype.card (net.Centers q) : Real) * rowProduct r A N W delta h path q ≤
      (∏ j, (25 * RadialNetAssembly.weight h (q j) / h ^ 2) ^ (p.blocks j).card) *
        rowProduct r A N W delta h path q :=
      mul_le_mul_of_nonneg_right (net.center_count q) hrow0
    _ ≤ (25 / h ^ 2) ^ N * (A * (N : Real) * W * delta ^ 2) ^ (r * J) *
        (4 * (J : Real) * delta ^ 2) ^ r := by
      simpa only [rowProduct, PlanarRowBounds.bound] using hcancel

end HighBandLSV.PlanarTensorization

#print axioms HighBandLSV.PlanarTensorization.point_probability
#print axioms HighBandLSV.PlanarTensorization.center_union_endpoint_bound

