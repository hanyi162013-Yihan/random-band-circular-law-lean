import CircularLawSection6.LogCutoffComparison
import TaoVuReplacement.MatrixScaling

/-! # The cutoff comparison on actual shifted complex matrices

The operator energy is identified with replacement's explicit entrywise
Hilbert--Schmidt square. Common spectral shifts cancel, and the scaling
factor is exact. All nonsingularity premises are visible.
-/

open scoped BigOperators
open TaoVuReplacement

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixCutoffPotential (A : Matrix ι ι ℂ) (a : ℝ) : ℝ :=
  operatorCutoffPotential A.toEuclideanLin a

theorem toEuclideanLin_injective_of_det_ne_zero (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) :
    Function.Injective A.toEuclideanLin := by
  intro x y h
  apply (WithLp.linearEquiv 2 ℂ (ι → ℂ)).injective
  apply Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det A).mpr
    (isUnit_iff_ne_zero.mpr hA))
  exact congrArg WithLp.ofLp h

theorem operatorHilbertSchmidtSq_toEuclideanLin (A : Matrix ι ι ℂ) :
    operatorHilbertSchmidtSq A.toEuclideanLin = hilbertSchmidtSq A := by
  have h := hilbertSchmidtSq_toMatrix_orthonormalBasis
    (EuclideanSpace.basisFun ι ℂ) A.toEuclideanLin
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin] at h
  exact h.symm

theorem matrixCutoffPotential_difference_le [Nonempty ι]
    (A B : Matrix ι ι ℂ) (hA : A.det ≠ 0) (hB : B.det ≠ 0) {a : ℝ} (ha : 0 < a) :
    |matrixCutoffPotential A a - matrixCutoffPotential B a| ≤
      Real.sqrt (hilbertSchmidtSq (A - B)) / (a * Real.sqrt (Fintype.card ι : ℝ)) := by
  have h := operatorCutoffPotential_difference_le_normalized A.toEuclideanLin B.toEuclideanLin
    (toEuclideanLin_injective_of_det_ne_zero A hA)
    (toEuclideanLin_injective_of_det_ne_zero B hB)
    (by simpa using Fintype.card_pos (α := ι)) ha
  have hm : (A - B).toEuclideanLin = A.toEuclideanLin - B.toEuclideanLin :=
    Matrix.toEuclideanLin.map_sub A B
  rw [← hm, operatorHilbertSchmidtSq_toEuclideanLin] at h
  simpa only [matrixCutoffPotential, finrank_euclideanSpace] using h

theorem matrixShiftedCutoff_difference_le [Nonempty ι]
    (A B : Matrix ι ι ℂ) (r : ℝ) (hr : 0 ≤ r) (z : ℂ)
    (hA : ((r : ℂ) • A - z • 1).det ≠ 0)
    (hB : ((r : ℂ) • B - z • 1).det ≠ 0) {a : ℝ} (ha : 0 < a) :
    |matrixCutoffPotential ((r : ℂ) • A - z • 1) a -
        matrixCutoffPotential ((r : ℂ) • B - z • 1) a| ≤
      r * Real.sqrt (hilbertSchmidtSq (A - B)) / (a * Real.sqrt (Fintype.card ι : ℝ)) := by
  have h := matrixCutoffPotential_difference_le _ _ hA hB ha
  have hd : ((r : ℂ) • A - z • 1) - ((r : ℂ) • B - z • 1) =
      (r : ℂ) • (A - B) := by module
  rw [hd, hilbertSchmidtSq_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at h
  exact h

end CircularLawSection6
