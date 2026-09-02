import BernoulliSection9.GramVolumeSingular
import BernoulliLinearAlgebra.VolumeComparison
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Matrix Gram volume as graph volume

This identifies the `gramVolume` used by the completed all-minor comparison
with the singular-value graph volume developed locally.  It is the exact
bridge needed to compare the literal terminal coefficient norm with the
large singular values selected by RRQR.
-/

open scoped BigOperators InnerProductSpace Matrix

noncomputable section

namespace BernoulliSection9

open Module

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace Complex E]
variable [NormedAddCommGroup F] [InnerProductSpace Complex F]
variable [FiniteDimensional Complex E] [FiniteDimensional Complex F]

/-- The Gram operator of the graph is `I + T†T`. -/
theorem singularGraph_adjoint_comp_self (T : E →ₗ[Complex] F) :
    LinearMap.adjoint (singularGraph T) ∘ₗ singularGraph T =
      LinearMap.id + (LinearMap.adjoint T ∘ₗ T) := by
  ext x
  apply ext_inner_left Complex
  intro y
  change inner Complex y
      (LinearMap.adjoint (singularGraph T) (singularGraph T x)) =
    inner Complex y (x + LinearMap.adjoint T (T x))
  rw [LinearMap.adjoint_inner_right (singularGraph T) y (singularGraph T x)]
  rw [inner_add_right]
  rw [LinearMap.adjoint_inner_right T y (T x)]
  simp [singularGraph, WithLp.prod_inner_apply]

section Matrix

variable {iota : Type*} [Fintype iota] [DecidableEq iota] [LinearOrder iota]

/-- Matrix form of the graph Gram operator identity. -/
theorem toEuclideanLin_one_add_gram
    (A : Matrix iota iota Complex) :
    Matrix.toEuclideanLin (1 + Aᴴ * A) =
      LinearMap.id +
        (LinearMap.adjoint (Matrix.toEuclideanLin A) ∘ₗ
          Matrix.toEuclideanLin A) := by
  rw [map_add, Matrix.toLpLin_one, Matrix.toLpLin_mul_same,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

/-- The squared graph volume is the real Gram determinant. -/
theorem matrix_singularGraph_normDet_sq_eq_gramEnergy
    (A : Matrix iota iota Complex) :
    (singularGraph (Matrix.toEuclideanLin A)).normDet ^ 2 =
      BernoulliLinearAlgebra.gramEnergy A := by
  have hsquare := (singularGraph (Matrix.toEuclideanLin A)).normDet_sq
  rw [singularGraph_adjoint_comp_self] at hsquare
  rw [← toEuclideanLin_one_add_gram A] at hsquare
  have hdet :
      LinearMap.det (Matrix.toEuclideanLin (1 + Aᴴ * A)) =
        (1 + Aᴴ * A).det := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.det_toLin]
  rw [hdet] at hsquare
  have hre := congrArg Complex.re hsquare
  norm_cast at hre

/-- Exact identity between the dependency's all-minor Gram volume and the
graph-map singular-value volume. -/
theorem gramVolume_eq_singularGraph_normDet
    (A : Matrix iota iota Complex) :
    BernoulliLinearAlgebra.gramVolume A =
      (singularGraph (Matrix.toEuclideanLin A)).normDet := by
  apply (sq_eq_sq₀ (BernoulliLinearAlgebra.gramVolume_nonneg A)
    (LinearMap.normDet_nonneg _)).mp
  rw [BernoulliLinearAlgebra.gramVolume_sq,
    matrix_singularGraph_normDet_sq_eq_gramEnergy]

/-- The terminal Gram volume dominates the product extracted at any cutoff. -/
theorem matrix_largeSingularProduct_le_gramVolume
    (A : Matrix iota iota Complex) (r : Nat) :
    largeSingularProduct (Matrix.toEuclideanLin A) r <=
      BernoulliLinearAlgebra.gramVolume A := by
  rw [gramVolume_eq_singularGraph_normDet]
  exact largeSingularProduct_le_graph_normDet _ _

/-- Threshold upper comparison in matrix language. -/
theorem gramVolume_le_threshold_factor_mul_matrixLargeSingularProduct
    (A : Matrix iota iota Complex) (r : Nat) (tau : Real)
    (htau : 1 <= tau)
    (hlarge : ∀ i : Fin (finrank Complex (EuclideanSpace Complex iota)),
      (i : Nat) < r ->
      tau < (Matrix.toEuclideanLin A).singularValues i)
    (hsmall : ∀ i : Fin (finrank Complex (EuclideanSpace Complex iota)),
      r <= (i : Nat) ->
      (Matrix.toEuclideanLin A).singularValues i <= tau) :
    BernoulliLinearAlgebra.gramVolume A <=
      (2 * tau) ^ (Fintype.card iota) *
        largeSingularProduct (Matrix.toEuclideanLin A) r := by
  rw [gramVolume_eq_singularGraph_normDet]
  simpa [finrank_euclideanSpace] using
    graph_normDet_le_threshold_factor_mul_largeSingularProduct
      (Matrix.toEuclideanLin A) r tau htau hlarge hsmall

end Matrix

end BernoulliSection9
