/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/MatrixColumnBound.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RandomMatrixModel
import Vendor.NormalEvents

/-!
# The actual column-distance estimate for the complex band matrix

The good event is the universal normal-spread event, not an assumed small-ball
event. Its measurability is proved in `NormalEvents`. Unit normals are selected
only after fixing a Fubini fiber, so no measurable selection assumption is used.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set Section5Formalization GinibreLSV

noncomputable section

namespace HighBandLSV.ColumnExposure

open NormalEvents

variable {n W : Nat} {c C L : Real}
  (m : PlanarBandModel (n + 1) W c C L) (j : Fin (n + 1))

theorem reconstruct_same (x : AtomColumn (n + 1)) (rest : Rest (n := n)) :
    (expose j).symm (x, rest) j = x := by
  change Fin.insertNth (α := fun _ : Fin (n + 1) => AtomColumn (n + 1)) j x rest j = x
  exact Fin.insertNth_apply_same (α := fun _ : Fin (n + 1) => AtomColumn (n + 1)) j x rest

theorem reconstruct_other (x y : AtomColumn (n + 1)) (rest : Rest (n := n))
    (k : Fin (n + 1)) (hk : k ≠ j) :
    (expose j).symm (x, rest) k = (expose j).symm (y, rest) k := by
  cases k using Fin.succAboveCases j with
  | x => exact (hk rfl).elim
  | p k =>
    change Fin.insertNth (α := fun _ : Fin (n + 1) => AtomColumn (n + 1))
      j x rest (j.succAbove k) =
      Fin.insertNth (α := fun _ : Fin (n + 1) => AtomColumn (n + 1)) j y rest (j.succAbove k)
    simp only [Fin.insertNth_apply_succAbove]

def reconstructedMatrix (z : Complex) (p : AtomColumn (n + 1) × Rest (n := n)) :
    Mat (n + 1) := shifted (m.matrix ((expose j).symm p)) z

def frozenMatrix (z : Complex) (rest : Rest (n := n)) : Mat (n + 1) :=
  reconstructedMatrix m j z (0, rest)

theorem measurable_reconstructedMatrix (z : Complex) :
    Measurable (reconstructedMatrix m j z) := by
  have hm := m.measurable_matrix
  have he := (expose j).symm.measurable
  unfold reconstructedMatrix shifted
  fun_prop

theorem measurable_frozenMatrix (z : Complex) : Measurable (frozenMatrix m j z) :=
  (measurable_reconstructedMatrix m j z).comp (measurable_const.prodMk measurable_id)

theorem reconstructed_other_col (z : Complex) (x : AtomColumn (n + 1))
    (rest : Rest (n := n)) (k : Fin (n + 1)) (hk : k ≠ j) :
    col (reconstructedMatrix m j z (x, rest)) k = col (frozenMatrix m j z rest) k := by
  ext i
  have heq := reconstruct_other j x 0 rest k hk
  change (shifted (m.matrix ((expose j).symm (x, rest))) z) i k =
    (shifted (m.matrix ((expose j).symm (0, rest))) z) i k
  simp only [shifted, Matrix.sub_apply, PlanarBandModel.matrix]
  rw [heq]

theorem inner_reconstructed_col (z : Complex) (x : AtomColumn (n + 1))
    (rest : Rest (n := n)) (u : Vec (n + 1)) :
    inner Complex u (col (reconstructedMatrix m j z (x, rest)) j) =
      m.linearForm j u x - star (u j) * z := by
  rw [inner_col_eq]
  simp [reconstructedMatrix, shifted, PlanarBandModel.matrix, PlanarBandModel.linearForm,
    PlanarBandModel.coefficients, reconstruct_same, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, mul_sub, Finset.sum_sub_distrib, mul_assoc]

def goodRest (z : Complex) (B : Finset (Fin (n + 1))) (d : Real) : Set (Rest (n := n)) :=
  (frozenMatrix m j z) ⁻¹' NormalEvents.good j B d

theorem measurableSet_goodRest (z : Complex) (B : Finset (Fin (n + 1))) (d : Real) :
    MeasurableSet (goodRest m j z B d) :=
  (NormalEvents.measurableSet_good j B d).preimage (measurable_frozenMatrix m j z)

def distanceEvent (z : Complex) (B : Finset (Fin (n + 1))) (d s : Real) :
    Set (AtomColumn (n + 1) × Rest (n := n)) :=
  {p | p.2 ∈ goodRest m j z B d ∧ columnDistance (reconstructedMatrix m j z p) j ≤ s}

theorem measurableSet_distanceEvent (z : Complex) (B : Finset (Fin (n + 1))) (d s : Real) :
    MeasurableSet (distanceEvent m j z B d s) := by
  apply ((measurableSet_goodRest m j z B d).preimage measurable_snd).inter
  exact measurableSet_le
    ((NormalEvents.measurable_columnDistance j).comp (measurable_reconstructedMatrix m j z))
    measurable_const

/-- No density, independence, or normal-selection conclusion is assumed here. -/
theorem exposed_distance_small_ball (hL : 0 ≤ L) (hc : 0 < c) (hW : 0 < W)
    (z : Complex) (B : Finset (Fin (n + 1)))
    (hB : ∀ i ∈ B, cyclicDist (n + 1) i j ≤ W)
    {d s : Real} (hd : 0 < d) (hs : 0 ≤ s) :
    (m.columnLaw j).prod (restLaw m j) (distanceEvent m j z B d s) ≤
      ENNReal.ofReal (min 1
        (Real.pi * (((n + 1 : Nat) : Real) * L / ((c / W) * d ^ 2)) * s ^ 2)) := by
  apply GinibreLSV.prod_measure_le_of_forall_left_fiber _ _ _
    (measurableSet_distanceEvent m j z B d s)
  intro rest
  by_cases hrest : rest ∈ goodRest m j z B d
  · obtain ⟨u, hu⟩ := NormalEvents.exists_unit_normal (frozenMatrix m j z rest) j
    have hmass : d ^ 2 ≤ ∑ i ∈ B, ‖(u : Vec (n + 1)) i‖ ^ 2 := hrest u hu
    have hsubset :
        (fun x : AtomColumn (n + 1) => (x, rest)) ⁻¹' distanceEvent m j z B d s ⊆
        {x | ‖m.linearForm j u x - star ((u : Vec (n + 1)) j) * z‖ ≤ s} := by
      intro x hx
      have hun : IsNormal (reconstructedMatrix m j z (x, rest)) j u :=
        (NormalEvents.normal_congr j (reconstructed_other_col m j z x rest) u).mpr hu
      have hsmall := (NormalEvents.norm_inner_le_distance
        (reconstructedMatrix m j z (x, rest)) j u hun).trans hx.2
      rwa [inner_reconstructed_col] at hsmall
    exact (measure_mono hsubset).trans
      (m.block_small_ball hL hc hW j u B hB hd hmass (star ((u : Vec (n + 1)) j) * z) hs)
  · have hempty :
        (fun x : AtomColumn (n + 1) => (x, rest)) ⁻¹' distanceEvent m j z B d s = ∅ := by
      ext x
      simp [distanceEvent, hrest]
    simp [hempty]

end ColumnExposure

namespace PlanarBandModel

open NormalEvents ColumnExposure

variable {n W : Nat} {c C L : Real} (m : PlanarBandModel (n + 1) W c C L)

/-- The concrete good event: each deleted-column normal has sufficient mass
on the designated local block. -/
def goodNormalEvent (z : Complex) (B : Fin (n + 1) → Finset (Fin (n + 1))) (d : Real) :
    Set (MatrixSample (n + 1)) :=
  {omega | ∀ j, shifted (m.matrix omega) z ∈ NormalEvents.good j (B j) d}

theorem measurableSet_goodNormalEvent (z : Complex)
    (B : Fin (n + 1) → Finset (Fin (n + 1))) (d : Real) :
    MeasurableSet (m.goodNormalEvent z B d) := by
  have hm := m.measurable_matrix
  have hs : Measurable (fun omega => shifted (m.matrix omega) z) := by
    unfold shifted
    fun_prop
  simp only [goodNormalEvent, setOf_forall]
  exact MeasurableSet.iInter fun j => (NormalEvents.measurableSet_good j (B j) d).preimage hs

/-- The actual matrix column-distance estimate, with an explicit normal-spread
event. This is the column probability input needed by final LSV assembly. -/
theorem column_distance_small_ball (hL : 0 ≤ L) (hc : 0 < c) (hW : 0 < W)
    (z : Complex) (B : Fin (n + 1) → Finset (Fin (n + 1)))
    (hB : ∀ j i, i ∈ B j → cyclicDist (n + 1) i j ≤ W)
    {d s : Real} (hd : 0 < d) (hs : 0 ≤ s) (j : Fin (n + 1)) :
    m.law (closedColumnEvent (fun omega => shifted (m.matrix omega) z) s j ∩
      m.goodNormalEvent z B d) ≤
      ENNReal.ofReal (min 1
        (Real.pi * (((n + 1 : Nat) : Real) * L / ((c / W) * d ^ 2)) * s ^ 2)) := by
  have hsubset :
      closedColumnEvent (fun omega => shifted (m.matrix omega) z) s j ∩
          m.goodNormalEvent z B d ⊆
        (expose j) ⁻¹' distanceEvent m j z (B j) d s := by
    intro omega homega
    have hA : reconstructedMatrix m j z (expose j omega) = shifted (m.matrix omega) z := by
      simp [reconstructedMatrix]
    have hg : reconstructedMatrix m j z (expose j omega) ∈ NormalEvents.good j (B j) d := by
      rw [hA]
      exact homega.2 j
    constructor
    · exact (NormalEvents.good_congr j (B j) d
        (reconstructed_other_col m j z (expose j omega).1 (expose j omega).2)).mp hg
    · rw [hA]
      exact homega.1
  apply (measure_mono hsubset).trans
  rw [(expose_preserving m j).measure_preimage
    (measurableSet_distanceEvent m j z (B j) d s).nullMeasurableSet]
  exact exposed_distance_small_ball m j hL hc hW z (B j) (hB j) hd hs

end PlanarBandModel

#print axioms ColumnExposure.exposed_distance_small_ball
#print axioms PlanarBandModel.column_distance_small_ball

end HighBandLSV

