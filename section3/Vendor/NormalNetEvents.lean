/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/NormalNetEvents.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RadialNetAssembly
import Vendor.MatrixColumnBound
import Vendor.PathGeometry

/-! Concrete bad-normal events and their deterministic finite-net covering. -/

open scoped BigOperators ENNReal
open MeasureTheory Set Section5Formalization

noncomputable section

namespace HighBandLSV.NormalNetEvents

def columnCap {N : Nat} (K : Real) : Set (NormalEvents.Mat N) :=
  {A | ∀ j, ‖NormalEvents.col A j‖ ≤ K}

def normalSpread {N J : Nat} (p : BlockGeometry.Partition N J) (delta : Real) :
    Set (NormalEvents.Mat N) :=
  {A | ∀ i j, A ∈ NormalEvents.good i (p.blocks j) delta}

theorem measurableSet_normalSpread {N J : Nat}
    (p : BlockGeometry.Partition N J) (delta : Real) :
    MeasurableSet (normalSpread p delta) := by
  have heq : normalSpread p delta = ⋂ i, ⋂ j, NormalEvents.good i (p.blocks j) delta := by
    ext A
    simp [normalSpread]
  rw [heq]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    NormalEvents.measurableSet_good i (p.blocks j) delta

def fixedBad {N J : Nat} (p : BlockGeometry.Partition N J)
    (i : Fin N) (k l : Fin J) (K delta : Real) : Set (NormalEvents.Mat N) :=
  {A | A ∈ columnCap K ∧ ∃ u : NormalEvents.UnitVec N,
    NormalEvents.IsNormal A i u ∧ ‖p.restrict u k‖ < delta ∧
      1 / Real.sqrt (J : Real) ≤ ‖p.restrict u l‖}

theorem normal_cover {N J : Nat} (p : BlockGeometry.Partition N J)
    (hJ : 0 < J) {K delta : Real} (hd : 0 < delta) :
    columnCap K \ normalSpread p delta ⊆
      ⋃ i : Fin N, ⋃ k : Fin J, ⋃ l : Fin J, fixedBad p i k l K delta := by
  classical
  intro A hA
  have hbad : ¬ ∀ i j, A ∈ NormalEvents.good i (p.blocks j) delta := hA.2
  obtain ⟨i, hi⟩ := not_forall.mp hbad
  obtain ⟨k, hk⟩ := not_forall.mp hi
  change ¬ ∀ u : NormalEvents.UnitVec N, NormalEvents.IsNormal A i u →
    delta ^ 2 ≤ NormalEvents.blockMass (p.blocks k) u at hk
  push_neg at hk
  obtain ⟨u, hu, hmass⟩ := hk
  have hnormsq : ‖p.restrict u k‖ ^ 2 = NormalEvents.blockMass (p.blocks k) u :=
    p.restrict_norm_sq u k
  have hsmall : ‖p.restrict u k‖ < delta := by nlinarith [norm_nonneg (p.restrict u k)]
  obtain ⟨l, hl⟩ := p.exists_heavy_block hJ (u : NormalEvents.Vec N) u.2
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨k, mem_iUnion.mpr
    ⟨l, hA.1, u, hu, hsmall, hl⟩⟩⟩

theorem column_inner_error {N : Nat} (A : NormalEvents.Mat N) (i j : Fin N)
    (u v : NormalEvents.Vec N) {K e delta : Real}
    (hu : NormalEvents.IsNormal A i u) (hji : j ≠ i)
    (hcap : ‖NormalEvents.col A j‖ ≤ K) (he : ‖u - v‖ ≤ e)
    (hK : 0 ≤ K) (heK : e * K ≤ delta) :
    ‖inner Complex v (NormalEvents.col A j)‖ ≤ delta := by
  have hzero : inner Complex u (NormalEvents.col A j) = 0 :=
    inner_eq_zero_symm.mp (hu j hji)
  have her : ‖v - u‖ ≤ e := by simpa only [norm_sub_rev] using he
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  calc
    ‖inner Complex v (NormalEvents.col A j)‖ =
        ‖inner Complex (v - u) (NormalEvents.col A j)‖ := by
      rw [inner_sub_left, hzero, sub_zero]
    _ ≤ ‖v - u‖ * ‖NormalEvents.col A j‖ := norm_inner_le_norm _ _
    _ ≤ e * K := mul_le_mul her hcap (norm_nonneg _) he0
    _ ≤ delta := heK

def constraint {N : Nat} (v : NormalEvents.Vec N) (rows : Finset (Fin N))
    (delta : Real) : Set (NormalEvents.Mat N) :=
  {A | ∀ j ∈ rows, ‖inner Complex v (NormalEvents.col A j)‖ ≤ delta}

def admissible {J : Nat} (h delta : Real) (k l : Fin J)
    (q : RadialNetAssembly.Labels J h) : Prop :=
  (∀ j, RadialNetAssembly.radius h (q j) ≤ 1) ∧
    RadialNetAssembly.weight h (q k) ≤ delta ^ 2 ∧
      1 / (4 * (J : Real)) ≤ RadialNetAssembly.weight h (q l)

theorem fixedBad_subset_net_union {N J r : Nat}
    (p : BlockGeometry.Partition N J) {h K delta : Real}
    (net : RadialNetAssembly.System p h) (i : Fin N) (k l : Fin J)
    (rows : BlockGeometry.RowSelection p i r)
    (hJ : 0 < J) (hh : 0 < h) (hK : 0 ≤ K) (hhd : h ≤ delta)
    (hmesh : h * Real.sqrt (J : Real) ≤ 1 / 2)
    (herror : (Real.sqrt (J : Real) * h) * K ≤ delta) :
    fixedBad p i k l K delta ⊆
      ⋃ q : {q : RadialNetAssembly.Labels J h // admissible h delta k l q},
        ⋃ v : net.Centers q.val, constraint (net.vector q.val v) rows.allRows delta := by
  classical
  intro A hA
  obtain ⟨hcap, u, hu, hsmall, hheavy⟩ := hA
  obtain ⟨q, hq1, hq, v, hv⟩ := net.covers_unit_sphere hh (u : NormalEvents.Vec N) u.2
  have hsmallW : RadialNetAssembly.weight h (q k) ≤ delta ^ 2 :=
    RadialNetAssembly.small_weight hh.le hhd (q k) ((hq k).1.trans hsmall.le)
  have hheavyW : 1 / (4 * (J : Real)) ≤ RadialNetAssembly.weight h (q l) :=
    RadialNetAssembly.heavy_weight hJ hh.le (q l) hheavy (hq l).2 hmesh
  let label : {q : RadialNetAssembly.Labels J h // admissible h delta k l q} :=
    ⟨q, hq1, hsmallW, hheavyW⟩
  apply mem_iUnion.mpr
  refine ⟨label, mem_iUnion.mpr ⟨v, ?_⟩⟩
  intro j hj
  apply column_inner_error A i j (u : NormalEvents.Vec N) (net.vector q v) hu
  · intro heq
    subst j
    exact rows.avoids_allRows hj
  · exact hcap j
  · exact hv
  · exact hK
  · exact herror

end HighBandLSV.NormalNetEvents

#print axioms HighBandLSV.NormalNetEvents.normal_cover
#print axioms HighBandLSV.NormalNetEvents.fixedBad_subset_net_union

