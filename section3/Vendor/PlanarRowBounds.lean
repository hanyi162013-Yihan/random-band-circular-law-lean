/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/PlanarRowBounds.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RandomMatrixModel
import Vendor.RadialNetAssembly
import Vendor.PathGeometry

/-! Row small-ball bounds for every radial label, including the zero-radius labels. -/

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section

namespace HighBandLSV.PlanarRowBounds

def bound (A N W delta weight : Real) : Real := A * N * W * delta ^ 2 / weight

theorem bound_nonneg {A N W delta weight : Real}
    (hA : 0 ≤ A) (hN : 0 ≤ N) (hW : 0 ≤ W) (hw : 0 ≤ weight) :
    0 ≤ bound A N W delta weight := by
  unfold bound
  positivity

theorem probability_of_energy {N W : Nat} {c C L A delta weight : Real}
    (m : PlanarBandModel N W c C L) (hc : 0 < c) (hW : 0 < W) (hL : 0 ≤ L)
    (hA : Real.pi * L / c ≤ A) (hw : 0 < weight) (hd : 0 ≤ delta)
    (j : Fin N) (u : Fin N → Complex) (w : Complex)
    (henergy : (c / (W : Real)) * weight ≤ m.energy j u) :
    m.columnLaw j {x | ‖m.linearForm j u x - w‖ ≤ delta} ≤
      ENNReal.ofReal (bound A N W delta weight) := by
  have hWr : 0 < (W : Real) := Nat.cast_pos.mpr hW
  have hE : 0 < (c / (W : Real)) * weight := mul_pos (div_pos hc hWr) hw
  apply (m.linearForm_small_ball_of_energy_lower hL j u hE henergy w hd).trans
  apply ENNReal.ofReal_le_ofReal
  apply (min_le_right _ _).trans
  calc
    Real.pi * ((N : Real) * L / ((c / (W : Real)) * weight)) * delta ^ 2 =
        (Real.pi * L / c) * ((N : Real) * W * delta ^ 2) / weight := by
      field_simp
      <;> ring
    _ ≤ A * ((N : Real) * W * delta ^ 2) / weight := by
      apply div_le_div_of_nonneg_right _ hw.le
      exact mul_le_mul_of_nonneg_right hA (by positivity)
    _ = bound A N W delta weight := by unfold bound; ring

theorem probability_of_small_weight {N W : Nat} {c C L A delta weight : Real}
    (m : PlanarBandModel N W c C L) (hN : 0 < N) (hW : 0 < W)
    (hA : 1 ≤ A) (hw : 0 < weight) (hsmall : weight ≤ delta ^ 2)
    (j : Fin N) (u : Fin N → Complex) (w : Complex) :
    m.columnLaw j {x | ‖m.linearForm j u x - w‖ ≤ delta} ≤
      ENNReal.ofReal (bound A N W delta weight) := by
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hWr : (1 : Real) ≤ W := by exact_mod_cast hW
  have hAN : 1 ≤ A * (N : Real) :=
    hNr.trans (by simpa using mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg N))
  have hbase : 1 ≤ A * (N : Real) * W :=
    hWr.trans (by simpa using mul_le_mul_of_nonneg_right hAN (Nat.cast_nonneg W))
  have hnum : weight ≤ A * (N : Real) * W * delta ^ 2 :=
    hsmall.trans (by nlinarith [mul_le_mul_of_nonneg_right hbase (sq_nonneg delta)])
  have hbound : 1 ≤ bound A N W delta weight := by
    unfold bound
    exact (le_div_iff₀ hw).2 (by simpa using hnum)
  calc
    m.columnLaw j {x | ‖m.linearForm j u x - w‖ ≤ delta} ≤ 1 := by
      calc
        _ ≤ m.columnLaw j Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    _ = ENNReal.ofReal (1 : Real) := by simp
    _ ≤ ENNReal.ofReal (bound A N W delta weight) := ENNReal.ofReal_le_ofReal hbound

theorem center_energy {N J W : Nat} {c C L h : Real}
    (m : PlanarBandModel N W c C L) (p : BlockGeometry.Partition N J)
    (hband : PathGeometry.LocalBand p W) {k l : Fin J} (path : NeighborPath.Path k l)
    (net : RadialNetAssembly.System p h) (q : RadialNetAssembly.Labels J h)
    (v : net.Centers q) (j : Fin N) (hc : 0 < c) (hW : 0 < W) (hh : 0 < h)
    (hradius : h ≤ RadialNetAssembly.radius h
      (q (NeighborPath.next path.vertices (p.owner j)))) :
    (c / (W : Real)) * RadialNetAssembly.weight h
      (q (NeighborPath.next path.vertices (p.owner j))) ≤
        m.energy j (fun i => net.vector q v i) := by
  let t := NeighborPath.next path.vertices (p.owner j)
  have hmass : RadialNetAssembly.weight h (q t) ≤
      ∑ i ∈ p.blocks t, ‖net.vector q v i‖ ^ 2 := by
    rw [← p.restrict_norm_sq (net.vector q v) t]
    unfold RadialNetAssembly.weight
    rw [max_eq_left hradius]
    exact pow_le_pow_left₀ (RadialNetAssembly.radius_nonneg hh.le _)
      (net.vector_block_bounds q v t).1 2
  have hfloor := m.energy_ge_block j (fun i => net.vector q v i) (p.blocks t)
    (fun i hi => PathGeometry.target_in_band p hband path j i hi)
  exact (mul_le_mul_of_nonneg_left hmass
    (div_nonneg hc.le (Nat.cast_nonneg W))).trans hfloor

theorem center_row_probability {N J W : Nat} {c C L A h delta : Real}
    (m : PlanarBandModel N W c C L) (p : BlockGeometry.Partition N J)
    (hband : PathGeometry.LocalBand p W) {k l : Fin J} (path : NeighborPath.Path k l)
    (net : RadialNetAssembly.System p h) (q : RadialNetAssembly.Labels J h)
    (v : net.Centers q) (j : Fin N) (w : Complex)
    (hN : 0 < N) (hc : 0 < c) (hW : 0 < W) (hL : 0 ≤ L)
    (hA1 : 1 ≤ A) (hA : Real.pi * L / c ≤ A) (hh : 0 < h) (hhd : h ≤ delta) :
    m.columnLaw j {x | ‖m.linearForm j (fun i => net.vector q v i) x - w‖ ≤ delta} ≤
      ENNReal.ofReal (bound A N W delta
        (RadialNetAssembly.weight h (q (NeighborPath.next path.vertices (p.owner j))))) := by
  let t := NeighborPath.next path.vertices (p.owner j)
  have hweight := RadialNetAssembly.weight_pos hh (q t)
  rcases RadialNetAssembly.radius_zero_or_ge hh (q t) with hz | hR
  · apply probability_of_small_weight m hN hW hA1 hweight _ j _ w
    apply RadialNetAssembly.small_weight hh.le hhd (q t)
    rw [hz]
    exact hh.le.trans hhd
  · exact probability_of_energy m hc hW hL hA hweight (hh.le.trans hhd) j _ w
      (center_energy m p hband path net q v j hc hW hh hR)

end HighBandLSV.PlanarRowBounds

#print axioms HighBandLSV.PlanarRowBounds.center_row_probability

