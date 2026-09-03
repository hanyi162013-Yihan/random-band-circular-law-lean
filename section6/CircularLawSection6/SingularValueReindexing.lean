import CircularLawSection6.CutoffReindexing
import CircularLawSection6.CompactCutoffExpectation
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! # Exact ordered singular values under coordinate permutation

The Gram operators are conjugate by the actual Euclidean coordinate isometry.
Their characteristic polynomials and ordered eigenvalues therefore agree.
This argument also covers zero singular values and arbitrary spectral tests.
-/

noncomputable section
open scoped BigOperators

namespace CircularLawSection6

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem reindexed_gram_conjugate (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    (euclideanReindex e).toLinearEquiv.conj (A.toEuclideanLin.adjoint.comp A.toEuclideanLin) =
      (A.submatrix e.symm e.symm).toEuclideanLin.adjoint.comp
        (A.submatrix e.symm e.symm).toEuclideanLin := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (euclideanReindex e).surjective y
  change euclideanReindex e
      (A.toEuclideanLin.adjoint (A.toEuclideanLin
        ((euclideanReindex e).symm (euclideanReindex e x)))) =
    (A.submatrix e.symm e.symm).toEuclideanLin.adjoint
      ((A.submatrix e.symm e.symm).toEuclideanLin (euclideanReindex e x))
  rw [LinearIsometryEquiv.symm_apply_apply, toEuclideanLin_reindex,
    toEuclideanLin_adjoint_reindex]

theorem matrix_singularValues_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) (i : ℕ) :
    (A.submatrix e.symm e.symm).toEuclideanLin.singularValues i =
      A.toEuclideanLin.singularValues i := by
  have hι : Module.finrank ℂ (EuclideanSpace ℂ ι) = Fintype.card ι := finrank_euclideanSpace
  have hκ : Module.finrank ℂ (EuclideanSpace ℂ κ) = Fintype.card ι := by
    rw [finrank_euclideanSpace]
    exact (Fintype.card_congr e).symm
  have hchar :
      ((A.submatrix e.symm e.symm).toEuclideanLin.adjoint.comp
        (A.submatrix e.symm e.symm).toEuclideanLin).charpoly =
      (A.toEuclideanLin.adjoint.comp A.toEuclideanLin).charpoly := by
    rw [← reindexed_gram_conjugate, LinearEquiv.charpoly_conj]
  have hU := (A.submatrix e.symm e.symm).toEuclideanLin.isSymmetric_adjoint_comp_self
  have heig := (hU.eigenvalues_eq_eigenvalues_iff hκ
    A.toEuclideanLin.isSymmetric_adjoint_comp_self hι).2 hchar
  by_cases hi : i < Fintype.card ι
  · rw [LinearMap.singularValues_of_lt _ hκ hi, LinearMap.singularValues_of_lt _ hι hi, heig]
  · rw [LinearMap.singularValues_of_finrank_le _ (by omega),
      LinearMap.singularValues_of_finrank_le _ (by omega)]

theorem matrixSquaredSingularAverage_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) (φ : ℝ → ℝ) :
    matrixSquaredSingularAverage (A.submatrix e.symm e.symm) φ =
      matrixSquaredSingularAverage A φ := by
  unfold matrixSquaredSingularAverage
  simp_rw [matrix_singularValues_reindex]
  simp only [finrank_euclideanSpace]
  rw [Fintype.card_congr e]

theorem matrixSquaredSingularAverage_shifted_reindex (e : ι ≃ κ)
    (A : Matrix ι ι ℂ) (z : ℂ) (φ : ℝ → ℝ) :
    matrixSquaredSingularAverage (A.submatrix e.symm e.symm - z • 1) φ =
      matrixSquaredSingularAverage (A - z • 1) φ := by
  have hm : (A - z • 1).submatrix e.symm e.symm = A.submatrix e.symm e.symm - z • 1 := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, e.symm.injective.eq_iff]
  rw [← hm]
  exact matrixSquaredSingularAverage_reindex e (A - z • 1) φ

end CircularLawSection6
