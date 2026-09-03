/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/Coordinates.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.BVH.EntryResolvent
import Vendor.Arxiv2410.V3.TraceMeasurability
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Entry coordinates for the specialized BVH replacement

The finite product in the Lindeberg argument is indexed by `Fin (n * n)`.  This file gives
the exact conversion between such coordinate vectors and `n x n` complex matrices.  In
particular, updating one coordinate is proved to add exactly one `Matrix.single` entry.
-/

namespace Arxiv2410V3.BVH

open MeasureTheory

noncomputable section

/-- The `n²` scalar coordinates of a matrix, in the order fixed by `finProdFinEquiv`. -/
def matrixCoordinates {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Fin (n * n) → ℂ :=
  fun k ↦
    let ij := finProdFinEquiv.symm k
    X ij.1 ij.2

/-- Reconstruct a matrix from its `n²` scalar entry coordinates. -/
def matrixOfCoordinates {n : ℕ} (x : Fin (n * n) → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ x (finProdFinEquiv (i, j))

@[simp]
theorem matrixCoordinates_matrixOfCoordinates {n : ℕ} (x : Fin (n * n) → ℂ) :
    matrixCoordinates (matrixOfCoordinates x) = x := by
  funext k
  change x (finProdFinEquiv (finProdFinEquiv.symm k)) = x k
  rw [Equiv.apply_symm_apply]

@[simp]
theorem matrixOfCoordinates_matrixCoordinates {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℂ) :
    matrixOfCoordinates (matrixCoordinates X) = X := by
  ext i j
  simp [matrixCoordinates, matrixOfCoordinates]

/-- Updating coordinate `k` to `w` means adding the corresponding single-entry matrix to the
matrix in which that coordinate has first been set to zero. -/
theorem matrixOfCoordinates_update_eq_add_single {n : ℕ}
    (x : Fin (n * n) → ℂ) (k : Fin (n * n)) (w : ℂ) :
    let ij := finProdFinEquiv.symm k
    matrixOfCoordinates (Function.update x k w) =
      matrixOfCoordinates (Function.update x k 0) + singleEntryMatrix ij.1 ij.2 w := by
  dsimp only
  ext i j
  by_cases h : finProdFinEquiv (i, j) = k
  · have hij : (i, j) = finProdFinEquiv.symm k := by
      calc
        (i, j) = finProdFinEquiv.symm (finProdFinEquiv (i, j)) :=
          (Equiv.symm_apply_apply finProdFinEquiv (i, j)).symm
        _ = finProdFinEquiv.symm k := congrArg finProdFinEquiv.symm h
    have hi : i = (finProdFinEquiv.symm k).1 := congrArg Prod.fst hij
    have hj : j = (finProdFinEquiv.symm k).2 := congrArg Prod.snd hij
    subst i
    subst j
    have hk : finProdFinEquiv (finProdFinEquiv.symm k) = k :=
      Equiv.apply_symm_apply finProdFinEquiv k
    change Function.update x k w (finProdFinEquiv (finProdFinEquiv.symm k)) =
      Function.update x k 0 (finProdFinEquiv (finProdFinEquiv.symm k)) +
        Matrix.single (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 w
          (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    rw [hk]
    simp [Function.update]
  · have hij : (i, j) ≠ finProdFinEquiv.symm k := by
      intro hij
      apply h
      rw [hij]
      exact Equiv.apply_symm_apply finProdFinEquiv k
    have hsingle : ¬ ((finProdFinEquiv.symm k).1 = i ∧
        (finProdFinEquiv.symm k).2 = j) := by
      rintro ⟨hi, hj⟩
      apply hij
      exact Prod.ext hi.symm hj.symm
    have hsingleEq :
        Matrix.single (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 w i j = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ hsingle
    change Function.update x k w (finProdFinEquiv (i, j)) =
      Function.update x k 0 (finProdFinEquiv (i, j)) +
        Matrix.single (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 w i j
    simp only [Function.update, dif_neg h, hsingleEq, add_zero]

/-- Entry coordinates of a random matrix form a measurable finite vector whenever every entry
is measurable. -/
theorem measurable_matrixCoordinates {Omega : Type*} [MeasurableSpace Omega] {n : ℕ}
    {X : Omega → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j)) :
    Measurable (fun omega ↦ matrixCoordinates (X omega)) := by
  apply measurable_pi_lambda
  intro k
  exact hX (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- The normalized Hermitized resolvent trace as a function of all entry coordinates is
strongly measurable. -/
theorem stronglyMeasurable_stieltjesTrace_matrixOfCoordinates {n : ℕ}
    (z eta : ℂ) :
    StronglyMeasurable
      (fun x : Fin (n * n) → ℂ ↦ stieltjesTrace (matrixOfCoordinates x) z eta) := by
  apply Measurable.stronglyMeasurable
  apply measurable_stieltjesTrace
  intro i j
  exact measurable_pi_apply (finProdFinEquiv (i, j))

end

end Arxiv2410V3.BVH

