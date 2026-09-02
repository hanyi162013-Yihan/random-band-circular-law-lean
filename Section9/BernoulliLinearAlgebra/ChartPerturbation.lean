import BernoulliLinearAlgebra.DenseExtension
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Sequences

/-!
# Concrete perturbations into the invertible upper-left chart

This file supplies the perturbation sequence left abstract in
`DenseExtension.lean`.  For a finite complex matrix `A`, the bad scalar
perturbations are the roots of the characteristic polynomial of `-A`:

`det(A + z I) = charpoly(-A)(z)`.

That root set is finite.  Its complement is dense in `ℂ`, hence contains a
sequence tending to zero.  Applied to the upper-left block of a `2 × 2` block
boundary relation, this gives an everywhere-invertible upper-left block.  If
the full relation is already invertible, continuity of its determinant shows
that a tail of the same sequence keeps the full relation invertible too.

The construction is classical and existential: it uses density of the
complement of a finite root set instead of selecting a numerical formula for
the scalars.  Unlike the abstraction in `SequentiallyDenseAt`, however, the
existence of the required sequence is proved here.
-/

open Filter Topology
open scoped Matrix Topology Polynomial

namespace BernoulliLinearAlgebra

section ScalarPerturbation

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Scalar perturbation of a square matrix.  The characteristic-polynomial
orientation makes the determinant identity below immediate. -/
def scalarPerturb (A : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  Matrix.scalar n z - (-A)

@[simp]
theorem scalarPerturb_zero (A : Matrix n n ℂ) :
    scalarPerturb A 0 = A := by
  simp [scalarPerturb]

/-- `scalarPerturb A z` is the familiar `A + z I`. -/
theorem scalarPerturb_eq_add_smul_one (A : Matrix n n ℂ) (z : ℂ) :
    scalarPerturb A z = A + z • 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [scalarPerturb, Matrix.scalar_apply]
    ring
  · simp [scalarPerturb, Matrix.scalar_apply, h]

/-- The determinant of a scalar perturbation is an evaluation of the
characteristic polynomial of `-A`. -/
theorem scalarPerturb_det (A : Matrix n n ℂ) (z : ℂ) :
    (scalarPerturb A z).det = (-A).charpoly.eval z := by
  rw [Matrix.eval_charpoly]
  rfl

/-- Scalars for which `A + z I` is singular. -/
def scalarPerturbationBadSet (A : Matrix n n ℂ) : Set ℂ :=
  {z | (-A).charpoly.eval z = 0}

/-- A finite matrix has only finitely many singular scalar perturbations. -/
theorem scalarPerturbationBadSet_finite (A : Matrix n n ℂ) :
    (scalarPerturbationBadSet A).Finite := by
  have hp : (-A).charpoly ≠ 0 := (Matrix.charpoly_monic (-A)).ne_zero
  refine (-A).charpoly.roots.finite_toSet.subset ?_
  intro z hz
  exact (Polynomial.mem_roots hp).mpr hz

/-- There are scalar perturbations converging to zero for which every
perturbed matrix is nonsingular. -/
theorem exists_scalarPerturbationSequence (A : Matrix n n ℂ) :
    ∃ ε : ℕ → ℂ,
      Tendsto ε atTop (nhds 0) ∧
        ∀ k, (scalarPerturb A (ε k)).det ≠ 0 := by
  let bad : Set ℂ := scalarPerturbationBadSet A
  have hbad : bad.Finite := scalarPerturbationBadSet_finite A
  have hdense : Dense badᶜ := hbad.countable.dense_compl ℂ
  rcases mem_closure_iff_seq_limit.mp (hdense 0) with ⟨ε, hεGood, hε0⟩
  refine ⟨ε, hε0, ?_⟩
  intro k
  rw [scalarPerturb_det]
  exact hεGood k

/-- Unit-valued form of `exists_scalarPerturbationSequence`. -/
theorem exists_unitScalarPerturbationSequence (A : Matrix n n ℂ) :
    ∃ ε : ℕ → ℂ,
      Tendsto ε atTop (nhds 0) ∧
        ∀ k, IsUnit (scalarPerturb A (ε k)).det := by
  rcases exists_scalarPerturbationSequence A with ⟨ε, hε0, hε⟩
  exact ⟨ε, hε0, fun k ↦ isUnit_iff_ne_zero.mpr (hε k)⟩

end ScalarPerturbation

section BlockPerturbation

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The upper-left block of a matrix indexed by `W ⊕ W`. -/
def upperLeftBlock (Θ : Matrix (W ⊕ W) (W ⊕ W) ℂ) : Matrix W W ℂ :=
  Θ.submatrix Sum.inl Sum.inl

/-- Perturb only the upper-left block by `z I`, leaving all other blocks
unchanged.  This is the matrix version of `Θ + z J₀` from Section 9.5. -/
def upperLeftPerturb (Θ : Matrix (W ⊕ W) (W ⊕ W) ℂ) (z : ℂ) :
    Matrix (W ⊕ W) (W ⊕ W) ℂ :=
  Θ + Matrix.fromBlocks (Matrix.scalar W z) 0 0 0

@[simp]
theorem upperLeftPerturb_zero
    (Θ : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    upperLeftPerturb Θ 0 = Θ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [upperLeftPerturb]

/-- The upper-left block of the block perturbation is exactly the scalar
perturbation constructed above. -/
theorem upperLeftBlock_upperLeftPerturb
    (Θ : Matrix (W ⊕ W) (W ⊕ W) ℂ) (z : ℂ) :
    upperLeftBlock (upperLeftPerturb Θ z) =
      scalarPerturb (upperLeftBlock Θ) z := by
  ext i j
  simp [upperLeftBlock, upperLeftPerturb, scalarPerturb,
    Matrix.scalar_apply]
  abel

/-- Perturbation of the upper-left block depends continuously on its scalar
parameter. -/
theorem continuous_upperLeftPerturb
    (Θ : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    Continuous (upperLeftPerturb Θ) := by
  apply continuous_matrix
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [upperLeftPerturb, Matrix.scalar_apply] <;> fun_prop

/-- The chart used in Section 9.5: both the full relation and its upper-left
block are nonsingular. -/
def invertibleUpperLeftChart :
    Set (Matrix (W ⊕ W) (W ⊕ W) ℂ) :=
  {Θ | IsUnit Θ.det ∧ IsUnit (upperLeftBlock Θ).det}

/-- Every invertible block relation is a sequential limit of relations in the
chart where both the full matrix and its upper-left block are invertible.

The proof first obtains a sequence avoiding all roots of the upper-left
characteristic polynomial.  Since `det Θ ≠ 0`, continuity makes the full
determinant nonzero eventually; shifting to that tail makes both conditions
hold for every term. -/
theorem invertibleUpperLeftChart_sequentiallyDenseAt
    (Θ : Matrix (W ⊕ W) (W ⊕ W) ℂ) (hΘ : IsUnit Θ.det) :
    SequentiallyDenseAt (invertibleUpperLeftChart (W := W)) Θ := by
  rcases exists_scalarPerturbationSequence (upperLeftBlock Θ) with
    ⟨ε, hε0, hεGood⟩
  have hmatrix :
      Tendsto (fun k ↦ upperLeftPerturb Θ (ε k)) atTop (nhds Θ) := by
    have h := Filter.Tendsto.comp
      (continuous_upperLeftPerturb Θ).continuousAt hε0
    simpa [Function.comp_def] using h
  have hdet :
      Tendsto (fun k ↦ (upperLeftPerturb Θ (ε k)).det)
        atTop (nhds Θ.det) := by
    simpa [Function.comp_def] using Filter.Tendsto.comp
      continuous_id.matrix_det.continuousAt hmatrix
  have hΘNe : Θ.det ≠ 0 := isUnit_iff_ne_zero.mp hΘ
  have hfull : ∀ᶠ k in atTop, (upperLeftPerturb Θ (ε k)).det ≠ 0 :=
    hdet.eventually_ne hΘNe
  rcases eventually_atTop.mp hfull with ⟨N, hN⟩
  refine ⟨fun k ↦ upperLeftPerturb Θ (ε (k + N)), ?_, ?_⟩
  · intro k
    constructor
    · exact isUnit_iff_ne_zero.mpr (hN (k + N) (by omega))
    · rw [upperLeftBlock_upperLeftPerturb]
      exact isUnit_iff_ne_zero.mpr (hεGood (k + N))
  · have hεTail : Tendsto (fun k ↦ ε (k + N)) atTop (nhds 0) :=
      hε0.comp (tendsto_add_atTop_nat N)
    have h := Filter.Tendsto.comp
      (continuous_upperLeftPerturb Θ).continuousAt hεTail
    simpa [Function.comp_def] using h

/-- Closure form of `invertibleUpperLeftChart_sequentiallyDenseAt`. -/
theorem invertible_mem_closure_invertibleUpperLeftChart
    (Θ : Matrix (W ⊕ W) (W ⊕ W) ℂ) (hΘ : IsUnit Θ.det) :
    Θ ∈ closure (invertibleUpperLeftChart (W := W)) := by
  apply seqClosure_subset_closure
  exact invertibleUpperLeftChart_sequentiallyDenseAt Θ hΘ

end BlockPerturbation

end BernoulliLinearAlgebra
