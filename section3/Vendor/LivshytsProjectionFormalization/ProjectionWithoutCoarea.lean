/- Source snapshot: upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/ProjectionWithoutCoarea.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.LivshytsProjectionFormalization.OrthogonalProjectionCoarea
import Vendor.LivshytsProjectionFormalization.RandomVectorProjection

open MeasureTheory

namespace LivshytsProjectionFormalization

noncomputable section

noncomputable def real_orthogonalProjection_hasBoundedDensity_provedCoarea
    (hGBL : RealFiniteGeometricBrascampLieb)
    {n d : Nat} {K : Real} (hK : 0 < K)
    (E : Submodule Real (CoordinateSpace Real n))
    (hE : Module.finrank Real E = d)
    (D : CoordinateDensityData Real n K) :
    HasBoundedDensity
      (Measure.map E.orthogonalProjectionOnto
        (volume.withDensity (coordinateProductDensity D.pdf)))
      (subspaceVolume E) (K ^ d * Real.exp (d / 2)) :=
  real_orthogonalProjection_hasBoundedDensity hGBL hK E hE D
    (orthogonalProjectionCoarea E D.measurable_pdf)

noncomputable def complex_orthogonalProjection_hasBoundedDensity_provedCoarea
    (hGBL : ComplexFiniteGeometricBrascampLieb)
    {n d : Nat} {K : Real} (hK : 0 < K)
    (E : Submodule Complex (CoordinateSpace Complex n))
    (hE : Module.finrank Complex E = d)
    (D : CoordinateDensityData Complex n K) :
    HasBoundedDensity
      (Measure.map E.orthogonalProjectionOnto
        (volume.withDensity (coordinateProductDensity D.pdf)))
      (subspaceVolume E) (K ^ d * Real.exp d) :=
  complex_orthogonalProjection_hasBoundedDensity hGBL hK E hE D
    (orthogonalProjectionCoarea E D.measurable_pdf)

variable {Omega : Type*} [MeasurableSpace Omega]

noncomputable def real_randomProjection_hasBoundedDensity_provedCoarea
    (hGBL : RealFiniteGeometricBrascampLieb)
    {n d : Nat} {K : Real} (hK : 0 < K)
    (X : Omega -> CoordinateSpace Real n) (P : Measure Omega)
    (E : Submodule Real (CoordinateSpace Real n))
    (hE : Module.finrank Real E = d)
    (D : CoordinateDensityData Real n K)
    (hLaw : CoordinateProductDensityLaw X P D) :
    HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (X omega)) P)
      (subspaceVolume E) (K ^ d * Real.exp (d / 2)) :=
  real_randomProjection_hasBoundedDensity hGBL hK X P E hE D hLaw
    (orthogonalProjectionCoarea E D.measurable_pdf)

noncomputable def complex_randomProjection_hasBoundedDensity_provedCoarea
    (hGBL : ComplexFiniteGeometricBrascampLieb)
    {n d : Nat} {K : Real} (hK : 0 < K)
    (X : Omega -> CoordinateSpace Complex n) (P : Measure Omega)
    (E : Submodule Complex (CoordinateSpace Complex n))
    (hE : Module.finrank Complex E = d)
    (D : CoordinateDensityData Complex n K)
    (hLaw : CoordinateProductDensityLaw X P D) :
    HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (X omega)) P)
      (subspaceVolume E) (K ^ d * Real.exp d) :=
  complex_randomProjection_hasBoundedDensity hGBL hK X P E hE D hLaw
    (orthogonalProjectionCoarea E D.measurable_pdf)

noncomputable def real_independent_randomProjection_hasBoundedDensity_provedCoarea
    (hGBL : RealFiniteGeometricBrascampLieb)
    {n d : Nat} {K : Real} (hK : 0 < K)
    (X : Omega -> CoordinateSpace Real n) (P : Measure Omega)
    (hX : Measurable X)
    (hIndep : ProbabilityTheory.iIndepFun (fun i omega => X omega i) P)
    (E : Submodule Real (CoordinateSpace Real n))
    (hE : Module.finrank Real E = d)
    (D : CoordinateDensityData Real n K)
    (hmarginal : forall i,
      Measure.map (fun omega => X omega i) P =
        volume.withDensity (D.pdf i)) :
    HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (X omega)) P)
      (subspaceVolume E) (K ^ d * Real.exp (d / 2)) :=
  real_randomProjection_hasBoundedDensity_provedCoarea hGBL hK X P E hE D
    (CoordinateProductDensityLaw.ofIndependentReal X P D hX hIndep hmarginal)

noncomputable def complex_independent_randomProjection_hasBoundedDensity_provedCoarea
    (hGBL : ComplexFiniteGeometricBrascampLieb)
    {n d : Nat} {K : Real} (hK : 0 < K)
    (X : Omega -> CoordinateSpace Complex n) (P : Measure Omega)
    (hX : Measurable X)
    (hIndep : ProbabilityTheory.iIndepFun (fun i omega => X omega i) P)
    (E : Submodule Complex (CoordinateSpace Complex n))
    (hE : Module.finrank Complex E = d)
    (D : CoordinateDensityData Complex n K)
    (hmarginal : forall i,
      Measure.map (fun omega => X omega i) P =
        volume.withDensity (D.pdf i)) :
    HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (X omega)) P)
      (subspaceVolume E) (K ^ d * Real.exp d) :=
  complex_randomProjection_hasBoundedDensity_provedCoarea hGBL hK X P E hE D
    (CoordinateProductDensityLaw.ofIndependentComplex X P D hX hIndep hmarginal)

end

end LivshytsProjectionFormalization

