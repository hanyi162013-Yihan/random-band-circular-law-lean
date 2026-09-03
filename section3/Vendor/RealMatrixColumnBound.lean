/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealMatrixColumnBound.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealColumnExposure
import Vendor.RealColumnSmallBall
import Vendor.MatrixGeometry

/-! Model-level real column distance bound by measurable exposure and pointwise normals. -/

noncomputable section
open MeasureTheory LivshytsProjectionFormalization
open scoped ENNReal InnerProductSpace
namespace HighBandLSV.RealBandModel
open HighBandLSV.RealColumnExposure HighBandLSV.Anisotropic

variable {n W : Nat} {c C rho : Real} (m : RealBandModel (n + 1) W c C rho)

def reconstructedMatrix (j : Fin (n + 1)) (p : AtomColumn (n + 1) × Rest n) : NormalEvents.Mat (n + 1) :=
  m.matrix (reconstruct j p.1 p.2)

def frozenMatrix (j : Fin (n + 1)) (rest : Rest n) : NormalEvents.Mat (n + 1) :=
  m.reconstructedMatrix j (0, rest)

theorem reconstructed_column_other (j : Fin (n + 1)) (x : AtomColumn (n + 1)) (rest : Rest n) (k : Fin n) :
    NormalEvents.col (m.reconstructedMatrix j (x, rest)) (j.succAbove k) =
      NormalEvents.col (m.frozenMatrix j rest) (j.succAbove k) := by
  ext a <;> simp [NormalEvents.col, reconstructedMatrix, frozenMatrix, matrix]

theorem shifted_reconstructed_other (j : Fin (n + 1)) (x : AtomColumn (n + 1)) (rest : Rest n)
    (k : Fin n) (z : Complex) :
    NormalEvents.col (shifted (m.reconstructedMatrix j (x, rest)) z) (j.succAbove k) =
      NormalEvents.col (shifted (m.frozenMatrix j rest) z) (j.succAbove k) := by
  rw [MatrixGeometry.shifted_column, MatrixGeometry.shifted_column, m.reconstructed_column_other]

theorem normal_reconstruct_iff (j : Fin (n + 1)) (x : AtomColumn (n + 1)) (rest : Rest n)
    (z : Complex) (u : NormalEvents.Vec (n + 1)) :
    NormalEvents.IsNormal (shifted (m.reconstructedMatrix j (x, rest)) z) j u ↔
      NormalEvents.IsNormal (shifted (m.frozenMatrix j rest) z) j u := by
  constructor
  · intro hu k hk
    obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
    have h := hu (j.succAbove l) hk
    rw [m.shifted_reconstructed_other j x rest l z] at h
    exact h
  · intro hu k hk
    obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
    rw [m.shifted_reconstructed_other j x rest l z]
    exact hu (j.succAbove l) hk

theorem good_reconstruct_iff (j : Fin (n + 1)) (x : AtomColumn (n + 1)) (rest : Rest n)
    (z : Complex) (B : Finset (Fin (n + 1))) (d : Real) :
    shifted (m.reconstructedMatrix j (x, rest)) z ∈ NormalEvents.good j B d ↔
      shifted (m.frozenMatrix j rest) z ∈ NormalEvents.good j B d := by
  constructor
  · intro h u hu
    exact h u ((m.normal_reconstruct_iff j x rest z u).mpr hu)
  · intro h u hu
    exact h u ((m.normal_reconstruct_iff j x rest z u).mp hu)

theorem measurable_reconstructedMatrix (j : Fin (n + 1)) : Measurable (m.reconstructedMatrix j) := by
  have hm : Measurable m.matrix := by
    have hc : Continuous m.matrix := by unfold matrix; fun_prop
    exact hc.measurable
  exact hm.comp (measurable_reconstruct j)

theorem measurable_reconstructedShift (j : Fin (n + 1)) (z : Complex) :
    Measurable (fun p => shifted (m.reconstructedMatrix j p) z) := by
  have hs : Continuous (fun A : NormalEvents.Mat (n + 1) => shifted A z) := by
    unfold shifted
    fun_prop
  exact hs.measurable.comp (m.measurable_reconstructedMatrix j)

theorem measurable_frozenShift (j : Fin (n + 1)) (z : Complex) :
    Measurable (fun rest => shifted (m.frozenMatrix j rest) z) :=
  (m.measurable_reconstructedShift j z).comp
    (show Measurable (fun rest : Rest n => ((0 : AtomColumn (n + 1)), rest)) by fun_prop)

def goodRest (j : Fin (n + 1)) (z : Complex) (B : Finset (Fin (n + 1))) (d : Real) : Set (Rest n) :=
  {rest | shifted (m.frozenMatrix j rest) z ∈ NormalEvents.good j B d}

theorem measurableSet_goodRest (j : Fin (n + 1)) (z : Complex) (B : Finset (Fin (n + 1))) (d : Real) :
    MeasurableSet (m.goodRest j z B d) :=
  (NormalEvents.measurableSet_good j B d).preimage (m.measurable_frozenShift j z)

def exposedDistanceEvent (j : Fin (n + 1)) (z : Complex) (B : Finset (Fin (n + 1))) (d s : Real) :
    Set (AtomColumn (n + 1) × Rest n) :=
  {p | GinibreLSV.columnDistance (shifted (m.reconstructedMatrix j p) z) j ≤ s ∧ p.2 ∈ m.goodRest j z B d}

theorem measurableSet_exposedDistanceEvent (j : Fin (n + 1)) (z : Complex)
    (B : Finset (Fin (n + 1))) (d s : Real) : MeasurableSet (m.exposedDistanceEvent j z B d s) := by
  have hdist := (NormalEvents.measurable_columnDistance j).comp (m.measurable_reconstructedShift j z)
  exact (measurableSet_le hdist measurable_const).inter
    ((m.measurableSet_goodRest j z B d).preimage measurable_snd)

theorem reconstructed_inner (j : Fin (n + 1)) (x : AtomColumn (n + 1)) (rest : Rest n)
    (z : Complex) (u : NormalEvents.Vec (n + 1)) :
    inner Complex u (NormalEvents.col (shifted (m.reconstructedMatrix j (x, rest)) z) j) =
      m.linearForm j u x - star (u j) * z := by
  rw [MatrixGeometry.inner_shifted_column]
  simp only [reconstructedMatrix, matrix, reconstruct_same, linearForm]

theorem exposed_distance_small_ball
    (hGBL : RealFiniteGeometricBrascampLieb) (hrho : 0 < rho) (hc : 0 < c) (hW : 0 < W)
    (j : Fin (n + 1)) (z : Complex) (B : Finset (Fin (n + 1)))
    (hB : ∀ i ∈ B, Section5Formalization.cyclicDist (n + 1) i j ≤ W)
    {d s : Real} (hd : 0 < d) (hs : 0 ≤ s) (rest : Rest n) :
    m.columnLaw j ((fun x => (x, rest)) ⁻¹' m.exposedDistanceEvent j z B d s) ≤
      ENNReal.ofReal ((2 * Real.sqrt 2 * Real.exp 1 * rho / Real.sqrt c) * Real.sqrt W * s / d) := by
  classical
  by_cases hrest : rest ∈ m.goodRest j z B d
  · obtain ⟨u, hu⟩ := NormalEvents.exists_unit_normal (shifted (m.frozenMatrix j rest) z) j
    have hmass : d ^ 2 ≤ NormalEvents.blockMass B u := hrest u hu
    have hcover : (fun x => (x, rest)) ⁻¹' m.exposedDistanceEvent j z B d s ⊆
        {x | ‖m.linearForm j u x - star ((u : NormalEvents.Vec (n + 1)) j) * z‖ ≤ s} := by
      intro x hx
      have hun := (m.normal_reconstruct_iff j x rest z u).mpr hu
      have hinner := (NormalEvents.norm_inner_le_distance
        (shifted (m.reconstructedMatrix j (x, rest)) z) j u hun).trans hx.1
      rw [m.reconstructed_inner] at hinner
      exact hinner
    exact (measure_mono hcover).trans
      (m.linearForm_block_mass_small_ball hGBL hrho hc hW j u B hB hd hs hmass
        (star ((u : NormalEvents.Vec (n + 1)) j) * z))
  · have hcover : (fun x => (x, rest)) ⁻¹' m.exposedDistanceEvent j z B d s ⊆
        (∅ : Set (AtomColumn (n + 1))) := by
      intro x hx
      exact False.elim (hrest hx.2)
    calc
      _ ≤ m.columnLaw j ∅ := measure_mono hcover
      _ = 0 := measure_empty
      _ ≤ _ := bot_le

def goodNormalEvent (z : Complex) (B : Fin (n + 1) → Finset (Fin (n + 1))) (d : Real) :
    Set (Sample (n + 1)) := {omega | ∀ j, shifted (m.matrix omega) z ∈ NormalEvents.good j (B j) d}

theorem column_distance_small_ball
    (hGBL : RealFiniteGeometricBrascampLieb) (hrho : 0 < rho) (hc : 0 < c) (hW : 0 < W)
    (z : Complex) (B : Fin (n + 1) → Finset (Fin (n + 1)))
    (hB : ∀ j i, i ∈ B j → Section5Formalization.cyclicDist (n + 1) i j ≤ W)
    {d s : Real} (hd : 0 < d) (hs : 0 ≤ s) (j : Fin (n + 1)) :
    m.law (closedColumnEvent (fun omega => shifted (m.matrix omega) z) s j ∩ m.goodNormalEvent z B d) ≤
      ENNReal.ofReal ((2 * Real.sqrt 2 * Real.exp 1 * rho / Real.sqrt c) * Real.sqrt W * s / d) := by
  apply exposure_probability_bound m j _ (m.exposedDistanceEvent j z (B j) d s)
    (m.measurableSet_exposedDistanceEvent j z (B j) d s)
  · intro omega homega
    have he : m.reconstructedMatrix j (expose j omega) = m.matrix omega := by
      simp [reconstructedMatrix, reconstruct]
    refine ⟨?_, ?_⟩
    · change GinibreLSV.columnDistance (shifted (m.reconstructedMatrix j (expose j omega)) z) j ≤ s
      rw [he]
      exact homega.1
    · have hg : shifted (m.reconstructedMatrix j (expose j omega)) z ∈ NormalEvents.good j (B j) d := by
        rw [he]
        exact homega.2 j
      exact (m.good_reconstruct_iff j (expose j omega).1 (expose j omega).2 z (B j) d).mp hg
  · intro rest
    exact m.exposed_distance_small_ball hGBL hrho hc hW j z (B j) (hB j) hd hs rest

end HighBandLSV.RealBandModel

#print axioms HighBandLSV.RealBandModel.column_distance_small_ball

