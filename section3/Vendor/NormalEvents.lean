/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/NormalEvents.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RandomMatrixModel
import Vendor.GinibreLSV.Ginibre
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Borel events for moving normal spaces

Compactness of the unit sphere proves measurability of the actual universal
normal-spread event. A unit normal may then be chosen separately in each
Fubini fiber. No measurable-selector or nonvanishing-cofactor hypothesis is
needed for that use of the column estimate.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

noncomputable section

namespace HighBandLSV.NormalEvents

abbrev Vec (N : Nat) := EuclideanSpace Complex (Fin N)
abbrev Mat (N : Nat) := Matrix (Fin N) (Fin N) Complex

def col {N : Nat} (A : Mat N) (j : Fin N) : Vec N :=
  WithLp.toLp 2 (fun i => A i j)

theorem col_eq {N : Nat} (A : Mat N) (j : Fin N) : col A j = GinibreLSV.column A j := by
  exact (GinibreLSV.column_matrixOfColumns (fun k => col A k) j).symm

theorem continuous_col {N : Nat} (j : Fin N) : Continuous (fun A : Mat N => col A j) := by
  exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)

def blockMass {N : Nat} (B : Finset (Fin N)) (u : Vec N) : Real :=
  ∑ i ∈ B, ‖u i‖ ^ 2

theorem continuous_blockMass {N : Nat} (B : Finset (Fin N)) : Continuous (blockMass B) := by
  unfold blockMass
  fun_prop

abbrev UnitVec (N : Nat) := {u : Vec N // ‖u‖ = 1}

private theorem compactUnitSphere (E : Type*) [NormedAddCommGroup E] [ProperSpace E] :
    CompactSpace {u : E // ‖u‖ = 1} := by
  apply isCompact_iff_compactSpace.mp
  simpa only [Metric.sphere, dist_zero_right, Set.ofPred] using
    isCompact_sphere (0 : E) (1 : Real)

instance unitVec_compact (N : Nat) : CompactSpace (UnitVec N) :=
  compactUnitSphere (Vec N)

def IsNormal {N : Nat} (A : Mat N) (j : Fin N) (u : Vec N) : Prop :=
  ∀ k, k ≠ j → inner Complex (col A k) u = 0

def closedBad {N : Nat} (j : Fin N) (B : Finset (Fin N)) (r : Real) : Set (Mat N) :=
  {A | ∃ u : UnitVec N, IsNormal A j u ∧ blockMass B u ≤ r}

theorem isClosed_closedBad {N : Nat} (j : Fin N) (B : Finset (Fin N)) (r : Real) :
    IsClosed (closedBad j B r) := by
  let S : Set (Mat N × UnitVec N) :=
    {p | IsNormal p.1 j p.2 ∧ blockMass B p.2 ≤ r}
  have hn : IsClosed {p : Mat N × UnitVec N | IsNormal p.1 j p.2} := by
    simp only [IsNormal, setOf_forall]
    apply isClosed_iInter
    intro k
    apply isClosed_iInter
    intro _
    exact isClosed_eq (((continuous_col k).comp continuous_fst).inner
      (continuous_subtype_val.comp continuous_snd)) continuous_const
  have hb : IsClosed {p : Mat N × UnitVec N | blockMass B p.2 ≤ r} :=
    isClosed_le ((continuous_blockMass B).comp
      (continuous_subtype_val.comp continuous_snd)) continuous_const
  have heq : closedBad j B r = Prod.fst '' S := by
    ext A
    constructor
    · rintro ⟨u, hu, hmass⟩
      exact ⟨(A, u), ⟨hu, hmass⟩, rfl⟩
    · rintro ⟨⟨A, u⟩, hu, rfl⟩
      exact ⟨u, hu⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace S (hn.inter hb)

def bad {N : Nat} (j : Fin N) (B : Finset (Fin N)) (d : Real) : Set (Mat N) :=
  {A | ∃ u : UnitVec N, IsNormal A j u ∧ blockMass B u < d ^ 2}

def good {N : Nat} (j : Fin N) (B : Finset (Fin N)) (d : Real) : Set (Mat N) :=
  {A | ∀ u : UnitVec N, IsNormal A j u → d ^ 2 ≤ blockMass B u}

theorem measurableSet_bad {N : Nat} (j : Fin N) (B : Finset (Fin N)) (d : Real) :
    MeasurableSet (bad j B d) := by
  have heq : bad j B d = ⋃ q : Rat, ⋃ (_ : (q : Real) < d ^ 2), closedBad j B q := by
    ext A
    simp only [mem_iUnion]
    constructor
    · rintro ⟨u, hu, hmass⟩
      obtain ⟨q, hq, hqd⟩ := exists_rat_btwn hmass
      exact ⟨q, hqd, u, hu, hq.le⟩
    · rintro ⟨q, hqd, u, hu, hmass⟩
      exact ⟨u, hu, hmass.trans_lt hqd⟩
  rw [heq]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    (isClosed_closedBad j B q).measurableSet

theorem good_eq_compl_bad {N : Nat} (j : Fin N) (B : Finset (Fin N)) (d : Real) :
    good j B d = (bad j B d)ᶜ := by
  ext A
  constructor
  · intro h hbad
    obtain ⟨u, hu, hmass⟩ := hbad
    exact (not_lt_of_ge (h u hu)) hmass
  · intro h u hu
    by_contra hmass
    exact h ⟨u, hu, lt_of_not_ge hmass⟩

theorem measurableSet_good {N : Nat} (j : Fin N) (B : Finset (Fin N)) (d : Real) :
    MeasurableSet (good j B d) := by
  rw [good_eq_compl_bad]
  exact (measurableSet_bad j B d).compl

/-- This works at every matrix, including every rank-deficient exceptional fiber. -/
theorem exists_unit_normal {N : Nat} (A : Mat N) (j : Fin N) :
    ∃ u : UnitVec N, IsNormal A j u := by
  let H := GinibreLSV.columnSpanExcept A j
  have hK : Hᗮ ≠ ⊥ := by
    intro h
    exact GinibreLSV.columnSpanExcept_ne_top A j (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨v, hv, hv0⟩ : ∃ v : Vec N, v ∈ Hᗮ ∧ v ≠ 0 := by
    by_contra h
    apply hK
    apply le_antisymm _ bot_le
    intro v hv
    change v = 0
    by_contra hv0
    exact h ⟨v, hv, hv0⟩
  let u : Vec N := ((‖v‖ : Real) : Complex)⁻¹ • v
  have hunit : ‖u‖ = 1 := by simp [u, norm_smul, hv0]
  have hu : u ∈ Hᗮ := Hᗮ.smul_mem _ hv
  refine ⟨⟨u, hunit⟩, ?_⟩
  intro k hk
  rw [col_eq]
  exact hu _ (GinibreLSV.column_mem_columnSpanExcept A hk)

theorem normal_congr {N : Nat} {A A' : Mat N} (j : Fin N)
    (hcols : ∀ k, k ≠ j → col A k = col A' k) (u : Vec N) :
    IsNormal A j u ↔ IsNormal A' j u := by
  constructor <;> intro h k hk
  · rw [← hcols k hk]
    exact h k hk
  · rw [hcols k hk]
    exact h k hk

theorem good_congr {N : Nat} {A A' : Mat N} (j : Fin N) (B : Finset (Fin N)) (d : Real)
    (hcols : ∀ k, k ≠ j → col A k = col A' k) : A ∈ good j B d ↔ A' ∈ good j B d := by
  constructor <;> intro h u hu
  · exact h u ((normal_congr j hcols u).mpr hu)
  · exact h u ((normal_congr j hcols u).mp hu)

set_option maxHeartbeats 1000000 in
theorem measurable_columnDistance {N : Nat} (j : Fin N) :
    Measurable (fun A : Mat N => GinibreLSV.columnDistance A j) := by
  apply measurable_of_Iio
  intro r
  have hC : Measurable (fun A : Mat N => fun k => col A k) :=
    measurable_pi_lambda _ fun k => (continuous_col k).measurable
  have heq (A : Mat N) :
      GinibreLSV.matrixOfColumns (fun k => col A k) = A := by
    ext i k
    rfl
  have hset : MeasurableSet {A : Mat N |
      GinibreLSV.columnDistance (GinibreLSV.matrixOfColumns (fun k => col A k)) j < r} :=
    (GinibreLSV.measurableSet_columnDistance_matrixOfColumns_lt j r).preimage hC
  convert hset using 1
  ext A
  simp only [heq, mem_preimage, mem_Iio, mem_setOf_eq]

theorem inner_col_eq {N : Nat} (u : Vec N) (A : Mat N) (j : Fin N) :
    inner Complex u (col A j) = ∑ i, star (u i) * A i j := by
  simp [col, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem norm_inner_lt_of_distance_lt {N : Nat} (A : Mat N) (j : Fin N)
    (u : UnitVec N) (hu : IsNormal A j u) {r : Real}
    (hdist : GinibreLSV.columnDistance A j < r) : ‖inner Complex (u : Vec N) (col A j)‖ < r := by
  obtain ⟨a, ha⟩ := (GinibreLSV.columnDistance_lt_iff_exists_coeff A j r).mp hdist
  let v := ∑ k, a k • GinibreLSV.column A k
  have hv : inner Complex (u : Vec N) v = 0 := by
    dsimp [v]
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [inner_smul_right]
    have hk : inner Complex (u : Vec N) (GinibreLSV.column A k) = 0 := by
      apply inner_eq_zero_symm.mp
      simpa only [col_eq] using hu k.1 k.2
    rw [hk, mul_zero]
  rw [col_eq]
  calc
    ‖inner Complex (u : Vec N) (GinibreLSV.column A j)‖ =
        ‖inner Complex (u : Vec N) (GinibreLSV.column A j - v)‖ := by
      rw [inner_sub_right, hv, sub_zero]
    _ ≤ ‖(u : Vec N)‖ * ‖GinibreLSV.column A j - v‖ := norm_inner_le_norm _ _
    _ = ‖GinibreLSV.column A j - v‖ := by rw [u.2, one_mul]
    _ < r := ha

theorem norm_inner_le_distance {N : Nat} (A : Mat N) (j : Fin N)
    (u : UnitVec N) (hu : IsNormal A j u) :
    ‖inner Complex (u : Vec N) (col A j)‖ ≤ GinibreLSV.columnDistance A j := by
  by_contra h
  exact (lt_irrefl _) (norm_inner_lt_of_distance_lt A j u hu (lt_of_not_ge h))

#print axioms measurableSet_good
#print axioms exists_unit_normal
#print axioms norm_inner_le_distance

end HighBandLSV.NormalEvents
