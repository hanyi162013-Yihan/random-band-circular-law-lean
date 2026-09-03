/- Source snapshot: upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/RealComplexCorrespondence.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.LivshytsProjectionFormalization.KernelCoordinateFrame
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

open MeasureTheory

namespace LivshytsProjectionFormalization

noncomputable section

/-- The standard identification of the real Euclidean plane with the complex line. -/
def euclideanPlaneToComplex (q : CoordinateSpace ℝ 2) : ℂ :=
  (q 0 : ℂ) + (q 1 : ℂ) * Complex.I

@[simp] theorem euclideanPlaneToComplex_re (q : CoordinateSpace ℝ 2) :
    (euclideanPlaneToComplex q).re = q 0 := by
  simp [euclideanPlaneToComplex]

@[simp] theorem euclideanPlaneToComplex_im (q : CoordinateSpace ℝ 2) :
    (euclideanPlaneToComplex q).im = q 1 := by
  simp [euclideanPlaneToComplex]

theorem euclideanPlaneToComplex_norm_sq (q : CoordinateSpace ℝ 2) :
    ‖euclideanPlaneToComplex q‖ ^ 2 = ‖q‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, EuclideanSpace.norm_sq_eq]
  simp only [euclideanPlaneToComplex_re, euclideanPlaneToComplex_im,
    Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  ring

theorem euclideanPlaneToComplex_norm (q : CoordinateSpace ℝ 2) :
    ‖euclideanPlaneToComplex q‖ = ‖q‖ := by
  nlinarith [euclideanPlaneToComplex_norm_sq q, norm_nonneg (euclideanPlaneToComplex q),
    norm_nonneg q]

/-- Complex coordinate of the orthogonal projection onto a real two-plane with an ordered
orthonormal basis. -/
def realPlaneProjectionAsComplex
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : Submodule ℝ V) [E.HasOrthogonalProjection]
    (b : OrthonormalBasis (Fin 2) ℝ E) (x : V) : ℂ :=
  euclideanPlaneToComplex (b.repr (E.orthogonalProjectionOnto x))

@[simp] theorem realPlaneProjectionAsComplex_re
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : Submodule ℝ V) [E.HasOrthogonalProjection]
    (b : OrthonormalBasis (Fin 2) ℝ E) (x : V) :
    (realPlaneProjectionAsComplex E b x).re =
      inner ℝ (b 0) (E.orthogonalProjectionOnto x) := by
  simp [realPlaneProjectionAsComplex, OrthonormalBasis.repr_apply_apply]

@[simp] theorem realPlaneProjectionAsComplex_im
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : Submodule ℝ V) [E.HasOrthogonalProjection]
    (b : OrthonormalBasis (Fin 2) ℝ E) (x : V) :
    (realPlaneProjectionAsComplex E b x).im =
      inner ℝ (b 1) (E.orthogonalProjectionOnto x) := by
  simp [realPlaneProjectionAsComplex, OrthonormalBasis.repr_apply_apply]

theorem realPlaneProjectionAsComplex_norm
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (E : Submodule ℝ V) [E.HasOrthogonalProjection]
    (b : OrthonormalBasis (Fin 2) ℝ E) (x : V) :
    ‖realPlaneProjectionAsComplex E b x‖ = ‖E.orthogonalProjectionOnto x‖ := by
  rw [realPlaneProjectionAsComplex, euclideanPlaneToComplex_norm]
  exact LinearIsometry.norm_map b.repr.toLinearIsometry _

/-- The coordinate-level map `(x,y) ↦ x + iy` preserves planar Lebesgue measure. -/
theorem realPairToComplex_measurePreserving :
    MeasurePreserving Complex.measurableEquivRealProd.symm :=
  Complex.volume_preserving_equiv_real_prod.symm

end

end LivshytsProjectionFormalization

