import BernoulliSection10.PhysicalRows
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Vector.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The concrete random physical-row model

This module contains the common concrete objects used by the Hodge
integrability and row-concentration layers of Section 10.  One random
coordinate is a complete physical equation row with `3 * W` real atoms.
An interval of `s` sites therefore has `s * W` independent row coordinates.
-/

open scoped BigOperators Matrix ENNReal NNReal Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace BernoulliSection10

open Matrix Set Set.powersetCard
open BernoulliLinearAlgebra

/-! ## The concrete row product probability space -/

/-- The `3W` independent real atoms in one physical equation row. -/
abbrev PhysicalRowAtoms (W : ℕ) := Fin (3 * W) → ℝ

/-- The product law of one physical row. -/
def physicalRowLaw (W : ℕ) (μ : Measure ℝ) : Measure (PhysicalRowAtoms W) :=
  Measure.pi fun _ : Fin (3 * W) ↦ μ

/-- All physical rows in an interval of `s` sites. -/
abbrev IntervalRows (W s : ℕ) := Fin (s * W) → PhysicalRowAtoms W

/-- The outer product law on the `sW` independent physical rows. -/
def intervalRowsLaw (W s : ℕ) (μ : Measure ℝ) : Measure (IntervalRows W s) :=
  Measure.pi fun _ : Fin (s * W) ↦ physicalRowLaw W μ

/-- Decode a site/within-site-row pair as one of the `sW` Efron--Stein
coordinates. -/
def intervalRowIndex {W s : ℕ} (j : Fin s) (a : Fin W) : Fin (s * W) :=
  finProdFinEquiv (j, a)

/-- Decode a block label and column as one of the `3W` atoms of a physical
row.  Labels `0,1,2` refer respectively to `B,A,C`. -/
def physicalAtomIndex {W : ℕ} (b : Fin 3) (c : Fin W) : Fin (3 * W) :=
  finProdFinEquiv (b, c)

/-- The variance-one normalization used for each random block. -/
def blockNormalization (W : ℕ) : ℝ := (Real.sqrt (3 * W : ℝ))⁻¹

/-- Read one atom of a physical row and apply the block normalization. -/
def normalizedPhysicalAtom {W : ℕ} (x : PhysicalRowAtoms W)
    (b : Fin 3) (c : Fin W) : ℂ :=
  (blockNormalization W * x (physicalAtomIndex b c) : ℝ)

/-- The concrete physical row obtained from its `3W` real atoms.  The middle
block is `D = A - zI`, so its diagonal contains the deterministic `-z`
shift. -/
def physicalRowGroupOfAtoms (W : ℕ) (z : ℂ) (a : Fin W)
    (x : PhysicalRowAtoms W) : PhysicalRowGroup (Fin W) where
  B c := normalizedPhysicalAtom x 0 c
  D c := normalizedPhysicalAtom x 1 c - if a = c then z else 0
  C c := normalizedPhysicalAtom x 2 c

/-- The `a`th row at site `j` in an interval configuration. -/
def intervalPhysicalRow {W s : ℕ} (z : ℂ) (x : IntervalRows W s)
    (j : Fin s) (a : Fin W) : PhysicalRowGroup (Fin W) :=
  physicalRowGroupOfAtoms W z a (x (intervalRowIndex j a))

/-- The normalized blocks `(B, D=A-zI, C)` at a site. -/
def intervalSiteBlocks {W s : ℕ} (z : ℂ) (x : IntervalRows W s)
    (j : Fin s) : PhysicalBlocks (Fin W) where
  B a c := (intervalPhysicalRow z x j a).B c
  D a c := (intervalPhysicalRow z x j a).D c
  C a c := (intervalPhysicalRow z x j a).C c

@[simp] theorem intervalPhysicalRow_update_same {W s : ℕ} (z : ℂ)
    (x : IntervalRows W s) (j : Fin s) (a : Fin W)
    (y : PhysicalRowAtoms W) :
    intervalPhysicalRow z (Function.update x (intervalRowIndex j a) y) j a =
      physicalRowGroupOfAtoms W z a y := by
  simp [intervalPhysicalRow, intervalRowIndex]

theorem intervalPhysicalRow_update_ne {W s : ℕ} (z : ℂ)
    (x : IntervalRows W s) (j k : Fin s) (a b : Fin W)
    (h : (j, a) ≠ (k, b)) (y : PhysicalRowAtoms W) :
    intervalPhysicalRow z (Function.update x (intervalRowIndex j a) y) k b =
      intervalPhysicalRow z x k b := by
  have hi : intervalRowIndex k b ≠ intervalRowIndex j a := by
    intro heq
    apply h
    exact finProdFinEquiv.injective heq.symm
  simp [intervalPhysicalRow, hi]

/-- Updating one outer coordinate replaces exactly the corresponding complete
physical row in its site blocks. -/
theorem intervalSiteBlocks_update_same {W s : ℕ} (z : ℂ)
    (x : IntervalRows W s) (j : Fin s) (a : Fin W)
    (y : PhysicalRowAtoms W) :
    intervalSiteBlocks z (Function.update x (intervalRowIndex j a) y) j =
      (intervalSiteBlocks z x j).replaceRow a
        (physicalRowGroupOfAtoms W z a y) := by
  apply PhysicalBlocks.ext
  · ext b c
    by_cases hba : b = a
    · subst b
      change
        (intervalPhysicalRow z
          (Function.update x (intervalRowIndex j a) y) j a).B c =
          Matrix.updateRow (intervalSiteBlocks z x j).B a
            (physicalRowGroupOfAtoms W z a y).B a c
      rw [intervalPhysicalRow_update_same, Matrix.updateRow_self]
    · have hp : (j, a) ≠ (j, b) := by
        intro h
        exact hba (Prod.mk.inj h).2.symm
      change
        (intervalPhysicalRow z
          (Function.update x (intervalRowIndex j a) y) j b).B c =
          Matrix.updateRow (intervalSiteBlocks z x j).B a
            (physicalRowGroupOfAtoms W z a y).B b c
      rw [intervalPhysicalRow_update_ne z x j j a b hp,
        Matrix.updateRow_ne hba]
      rfl
  · ext b c
    by_cases hba : b = a
    · subst b
      change
        (intervalPhysicalRow z
          (Function.update x (intervalRowIndex j a) y) j a).D c =
          Matrix.updateRow (intervalSiteBlocks z x j).D a
            (physicalRowGroupOfAtoms W z a y).D a c
      rw [intervalPhysicalRow_update_same, Matrix.updateRow_self]
    · have hp : (j, a) ≠ (j, b) := by
        intro h
        exact hba (Prod.mk.inj h).2.symm
      change
        (intervalPhysicalRow z
          (Function.update x (intervalRowIndex j a) y) j b).D c =
          Matrix.updateRow (intervalSiteBlocks z x j).D a
            (physicalRowGroupOfAtoms W z a y).D b c
      rw [intervalPhysicalRow_update_ne z x j j a b hp,
        Matrix.updateRow_ne hba]
      rfl
  · ext b c
    by_cases hba : b = a
    · subst b
      change
        (intervalPhysicalRow z
          (Function.update x (intervalRowIndex j a) y) j a).C c =
          Matrix.updateRow (intervalSiteBlocks z x j).C a
            (physicalRowGroupOfAtoms W z a y).C a c
      rw [intervalPhysicalRow_update_same, Matrix.updateRow_self]
    · have hp : (j, a) ≠ (j, b) := by
        intro h
        exact hba (Prod.mk.inj h).2.symm
      change
        (intervalPhysicalRow z
          (Function.update x (intervalRowIndex j a) y) j b).C c =
          Matrix.updateRow (intervalSiteBlocks z x j).C a
            (physicalRowGroupOfAtoms W z a y).C b c
      rw [intervalPhysicalRow_update_ne z x j j a b hp,
        Matrix.updateRow_ne hba]
      rfl

/-- Updating a row at site `j` leaves every other site unchanged. -/
theorem intervalSiteBlocks_update_other {W s : ℕ} (z : ℂ)
    (x : IntervalRows W s) (j k : Fin s) (a : Fin W) (hjk : k ≠ j)
    (y : PhysicalRowAtoms W) :
    intervalSiteBlocks z (Function.update x (intervalRowIndex j a) y) k =
      intervalSiteBlocks z x k := by
  apply PhysicalBlocks.ext
  · ext b c
    have hp : (j, a) ≠ (k, b) := by
      intro h
      exact hjk (Prod.mk.inj h).1.symm
    simp [intervalSiteBlocks,
      intervalPhysicalRow_update_ne z x j k a b hp]
  · ext b c
    have hp : (j, a) ≠ (k, b) := by
      intro h
      exact hjk (Prod.mk.inj h).1.symm
    simp [intervalSiteBlocks,
      intervalPhysicalRow_update_ne z x j k a b hp]
  · ext b c
    have hp : (j, a) ≠ (k, b) := by
      intro h
      exact hjk (Prod.mk.inj h).1.symm
    simp [intervalSiteBlocks,
      intervalPhysicalRow_update_ne z x j k a b hp]

/-! ## Cleared exterior products and the observables `Y_r(I)` -/

/-- A noncommutative product in reverse finite order:
`M (s-1) * ⋯ * M 0`. -/
def reverseMatrixProduct {s : ℕ} {q : Type*} [Fintype q] [DecidableEq q]
    (M : Fin s → Matrix q q ℂ) : Matrix q q ℂ :=
  (List.ofFn fun j : Fin s ↦ M j.rev).prod

/-- The denominator-free exterior factor at one block site. -/
def intervalClearedStep (W : ℕ) {s : ℕ} (z : ℂ)
    (x : IntervalRows W s) (r : Fin (2 * W + 1)) (j : Fin s) :
    Matrix (powersetCard (Fin W ⊕ Fin W) r.1)
      (powersetCard (Fin W ⊕ Fin W) r.1) ℂ :=
  let X := intervalSiteBlocks z x j
  clearedStepCompound r.1 X.B X.D X.C

/-- The paper's left-arrow product of cleared exterior factors on an interval
of `s` consecutive sites. -/
def intervalClearedProduct (W s : ℕ) (z : ℂ) (x : IntervalRows W s)
    (r : Fin (2 * W + 1)) :
    Matrix (powersetCard (Fin W ⊕ Fin W) r.1)
      (powersetCard (Fin W ⊕ Fin W) r.1) ℂ :=
  reverseMatrixProduct (fun j ↦ intervalClearedStep W z x r j)

/-- The concrete observable
`Y_r(I) = log ‖∏←_j clearedStepCompound r‖`. -/
def intervalDegreeLog (W s : ℕ) (z : ℂ) (r : Fin (2 * W + 1))
    (x : IntervalRows W s) : ℝ :=
  Real.log ‖intervalClearedProduct W s z x r‖

/-- The finite family of all degree observables `0 ≤ r ≤ 2W`. -/
def intervalDegreeLogs (W s : ℕ) (z : ℂ) :
    Fin (2 * W + 1) → IntervalRows W s → ℝ :=
  fun r ↦ intervalDegreeLog W s z r

end BernoulliSection10
