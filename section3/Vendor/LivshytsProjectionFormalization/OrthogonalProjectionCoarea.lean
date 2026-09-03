/- Source snapshot: upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/OrthogonalProjectionCoarea.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.LivshytsProjectionFormalization.FiniteProductDensity
import Mathlib.MeasureTheory.Integral.Prod

open scoped ENNReal NNReal
open MeasureTheory

namespace LivshytsProjectionFormalization

noncomputable section

private def rclikeLinearIsometryEquivToReal
    {k : Type*} [RCLike k]
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace k U]
    [InnerProductSpace Real U] [IsScalarTower Real k U]
    [NormedAddCommGroup V] [InnerProductSpace k V]
    [InnerProductSpace Real V] [IsScalarTower Real k V]
    (e : U ≃ₗᵢ[k] V) : U ≃ₗᵢ[Real] V :=
  LinearIsometryEquiv.mk (e.toLinearEquiv.restrictScalars Real) e.norm_map

private theorem rclikeLinearIsometryEquiv_measurePreserving
    {k : Type*} [RCLike k]
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace k U]
    [InnerProductSpace Real U] [IsScalarTower Real k U]
    [NormedAddCommGroup V] [InnerProductSpace k V]
    [InnerProductSpace Real V] [IsScalarTower Real k V]
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional Real U] [FiniteDimensional Real V]
    (e : U ≃ₗᵢ[k] V) : MeasurePreserving e := by
  convert (rclikeLinearIsometryEquivToReal e).measurePreserving using 1
  rfl

private def orthogonalCoordinateEquiv
    {k : Type*} [RCLike k] {n : Nat}
    (E : Submodule k (CoordinateSpace k n)) :
    WithLp 2 (CoordinateSpace k (Module.finrank k E) ×
      CoordinateSpace k (Module.finrank k (Submodule.orthogonal E))) ≃ₗᵢ[k]
      CoordinateSpace k n :=
  (LinearIsometryEquiv.withLpProdCongr 2
      (kernelCoordinateBasis E).repr.symm
      (kernelCoordinateBasis (Submodule.orthogonal E)).repr.symm).trans
    E.orthogonalDecomposition.symm

private def orthogonalCoordinateAddition
    {k : Type*} [RCLike k] {n : Nat}
    (E : Submodule k (CoordinateSpace k n))
    (p : CoordinateSpace k (Module.finrank k E) ×
      CoordinateSpace k (Module.finrank k (Submodule.orthogonal E))) :
    CoordinateSpace k n :=
  orthogonalCoordinateEquiv E (WithLp.toLp 2 p)

private theorem orthogonalCoordinateAddition_apply
    {k : Type*} [RCLike k] {n : Nat}
    (E : Submodule k (CoordinateSpace k n))
    (p : CoordinateSpace k (Module.finrank k E) ×
      CoordinateSpace k (Module.finrank k (Submodule.orthogonal E))) :
    orthogonalCoordinateAddition E p =
      ((kernelCoordinateBasis E).repr.symm p.1 : E) +
        ((kernelCoordinateBasis (Submodule.orthogonal E)).repr.symm p.2 :
          Submodule.orthogonal E) := by
  simp [orthogonalCoordinateAddition, orthogonalCoordinateEquiv,
    Submodule.orthogonalDecomposition_symm_apply]

private theorem orthogonalCoordinateAddition_measurePreserving
    {k : Type*} [RCLike k] {n : Nat}
    (E : Submodule k (CoordinateSpace k n)) :
    MeasurePreserving
      (μa := (volume : Measure (CoordinateSpace k (Module.finrank k E))).prod
        (volume : Measure (CoordinateSpace k
          (Module.finrank k (Submodule.orthogonal E)))))
      (orthogonalCoordinateAddition E) := by
  have h := (rclikeLinearIsometryEquiv_measurePreserving
      (orthogonalCoordinateEquiv E)).comp
    (WithLp.volume_preserving_toLp
      (CoordinateSpace k (Module.finrank k E))
      (CoordinateSpace k (Module.finrank k (Submodule.orthogonal E))))
  rw [Measure.volume_eq_prod] at h
  convert h using 1
  rfl

private theorem lintegral_subspaceVolume
    {k : Type*} [RCLike k] {n : Nat}
    (E : Submodule k (CoordinateSpace k n))
    {g : E -> ENNReal} (hg : Measurable g) :
    ∫⁻ y, g y ∂subspaceVolume E =
      ∫⁻ x : CoordinateSpace k (Module.finrank k E),
        g ((kernelCoordinateBasis E).repr.symm x) := by
  unfold subspaceVolume
  exact lintegral_map hg (kernelCoordinateBasis E).repr.symm.continuous.measurable

private theorem orthogonalProjection_orthogonalCoordinateAddition
    {k : Type*} [RCLike k] {n : Nat}
    (E : Submodule k (CoordinateSpace k n))
    (p : CoordinateSpace k (Module.finrank k E) ×
      CoordinateSpace k (Module.finrank k (Submodule.orthogonal E))) :
    E.orthogonalProjectionOnto (orthogonalCoordinateAddition E p) =
      (kernelCoordinateBasis E).repr.symm p.1 := by
  rw [orthogonalCoordinateAddition_apply]
  simp [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal]

theorem orthogonalProjectionCoarea
    {k : Type*} [RCLike k] {n : Nat}
    (E : Submodule k (CoordinateSpace k n))
    {f : Fin n -> k -> ENNReal} (hf : forall i, Measurable (f i)) :
    OrthogonalProjectionCoarea E f := by
  unfold OrthogonalProjectionCoarea
  apply Measure.ext
  intro s hs
  have hp : Measurable E.orthogonalProjectionOnto :=
    E.orthogonalProjectionOnto.continuous.measurable
  have hg : Measurable (coordinateProductDensity f) :=
    measurable_coordinateProductDensity hf
  have hfd : Measurable (orthogonalProjectionFiberDensity E f) :=
    measurable_orthogonalProjectionFiberDensity E hf
  rw [Measure.map_apply hp hs, withDensity_apply _ (hs.preimage hp),
    withDensity_apply _ hs]
  let T : Set (CoordinateSpace k (Module.finrank k E) ×
      CoordinateSpace k (Module.finrank k (Submodule.orthogonal E))) :=
    orthogonalCoordinateAddition E ⁻¹' (E.orthogonalProjectionOnto ⁻¹' s)
  have hT : MeasurableSet T :=
    (hs.preimage hp).preimage (orthogonalCoordinateAddition_measurePreserving E).measurable
  rw [← (orthogonalCoordinateAddition_measurePreserving E).setLIntegral_comp_preimage
    (hs.preimage hp) hg]
  change (∫⁻ p in T, coordinateProductDensity f (orthogonalCoordinateAddition E p)
    ∂((volume : Measure (CoordinateSpace k (Module.finrank k E))).prod
      (volume : Measure (CoordinateSpace k
        (Module.finrank k (Submodule.orthogonal E)))))) = _
  rw [← lintegral_indicator hT]
  rw [lintegral_prod
    (fun p => T.indicator
      (fun q => coordinateProductDensity f (orthogonalCoordinateAddition E q)) p)
    (((hg.comp
      (orthogonalCoordinateAddition_measurePreserving E).measurable).indicator hT).aemeasurable)]
  rw [← lintegral_indicator hs]
  rw [lintegral_subspaceVolume E (hfd.indicator hs)]
  apply lintegral_congr
  intro x
  have hmem (z : CoordinateSpace k
      (Module.finrank k (Submodule.orthogonal E))) :
      (x, z) ∈ T ↔ (kernelCoordinateBasis E).repr.symm x ∈ s := by
    simp only [T, Set.mem_preimage]
    rw [orthogonalProjection_orthogonalCoordinateAddition]
  by_cases hx : (kernelCoordinateBasis E).repr.symm x ∈ s
  · simp_rw [Set.indicator_of_mem ((hmem _).2 hx)]
    simp [hx, orthogonalProjectionFiberDensity, kernelFiberDensity, kernelFiberPoint,
      orthogonalCoordinateAddition_apply]
  · have hnmem (z : CoordinateSpace k
        (Module.finrank k (Submodule.orthogonal E))) : (x, z) ∉ T :=
      fun hz => hx ((hmem z).1 hz)
    simp_rw [Set.indicator_of_notMem (hnmem _)]
    simp [hx]

end

end LivshytsProjectionFormalization

