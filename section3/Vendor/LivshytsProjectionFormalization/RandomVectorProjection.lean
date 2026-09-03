/- Source snapshot: upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/RandomVectorProjection.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.LivshytsProjectionFormalization.FiniteProductDensity

/-!
# Random-vector and conditional-law projection interfaces

This file transports the product-density projection estimates from measures to
random vectors. It also packages pointwise conditional laws, so that after
conditioning on any outside parameter the same theorem can be applied without
adding a new analytic input.
-/

open MeasureTheory

namespace LivshytsProjectionFormalization

variable {Omega Theta : Type*} [MeasurableSpace Omega]

/-- The law of `X` is the product of the supplied one-coordinate densities. -/
structure CoordinateProductDensityLaw
    {K : Real} {k : Type*} [RCLike k] {n : Nat}
    (X : Omega -> CoordinateSpace k n) (P : Measure Omega)
    (D : CoordinateDensityData k n K) : Prop where
  measurable : Measurable X
  map_eq :
    Measure.map X P =
      volume.withDensity (coordinateProductDensity D.pdf)

theorem CoordinateProductDensityLaw.ofIndependentReal
    {n : Nat} {K : Real}
    (X : Omega -> CoordinateSpace Real n) (P : Measure Omega)
    (D : CoordinateDensityData Real n K)
    (hX : Measurable X)
    (hIndep : ProbabilityTheory.iIndepFun (fun i omega => X omega i) P)
    (hmarginal : forall i,
      Measure.map (fun omega => X omega i) P =
        volume.withDensity (D.pdf i)) :
    CoordinateProductDensityLaw X P D where
  measurable := hX
  map_eq := real_independent_map_eq_coordinateProductDensity
    P X hX D hIndep hmarginal

theorem CoordinateProductDensityLaw.ofIndependentComplex
    {n : Nat} {K : Real}
    (X : Omega -> CoordinateSpace Complex n) (P : Measure Omega)
    (D : CoordinateDensityData Complex n K)
    (hX : Measurable X)
    (hIndep : ProbabilityTheory.iIndepFun (fun i omega => X omega i) P)
    (hmarginal : forall i,
      Measure.map (fun omega => X omega i) P =
        volume.withDensity (D.pdf i)) :
    CoordinateProductDensityLaw X P D where
  measurable := hX
  map_eq := complex_independent_map_eq_coordinateProductDensity
    P X hX D hIndep hmarginal

theorem CoordinateProductDensityLaw.projectedMeasure_eq
    {K : Real} {k : Type*} [RCLike k] {n : Nat}
    {X : Omega -> CoordinateSpace k n} {P : Measure Omega}
    {D : CoordinateDensityData k n K}
    (hLaw : CoordinateProductDensityLaw X P D)
    (E : Submodule k (CoordinateSpace k n)) :
    Measure.map (fun omega => E.orthogonalProjectionOnto (X omega)) P =
      Measure.map E.orthogonalProjectionOnto
        (volume.withDensity (coordinateProductDensity D.pdf)) := by
  calc
    Measure.map (fun omega => E.orthogonalProjectionOnto (X omega)) P =
        Measure.map E.orthogonalProjectionOnto (Measure.map X P) := by
      change Measure.map (E.orthogonalProjectionOnto ∘ X) P = _
      exact (Measure.map_map E.orthogonalProjectionOnto.continuous.measurable
        hLaw.measurable).symm
    _ = Measure.map E.orthogonalProjectionOnto
          (volume.withDensity (coordinateProductDensity D.pdf)) := by
      rw [hLaw.map_eq]

noncomputable def real_randomProjection_hasBoundedDensity
    (hGBL : RealFiniteGeometricBrascampLieb)
    {n d : Nat} {K : Real} (hK : 0 < K)
    (X : Omega -> CoordinateSpace Real n) (P : Measure Omega)
    (E : Submodule Real (CoordinateSpace Real n))
    (hE : Module.finrank Real E = d)
    (D : CoordinateDensityData Real n K)
    (hLaw : CoordinateProductDensityLaw X P D)
    (hcoarea : OrthogonalProjectionCoarea E D.pdf) :
    HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (X omega)) P)
      (subspaceVolume E) (K ^ d * Real.exp (d / 2)) := by
  rw [hLaw.projectedMeasure_eq E]
  exact real_orthogonalProjection_hasBoundedDensity hGBL hK E hE D hcoarea

noncomputable def complex_randomProjection_hasBoundedDensity
    (hGBL : ComplexFiniteGeometricBrascampLieb)
    {n d : Nat} {K : Real} (hK : 0 < K)
    (X : Omega -> CoordinateSpace Complex n) (P : Measure Omega)
    (E : Submodule Complex (CoordinateSpace Complex n))
    (hE : Module.finrank Complex E = d)
    (D : CoordinateDensityData Complex n K)
    (hLaw : CoordinateProductDensityLaw X P D)
    (hcoarea : OrthogonalProjectionCoarea E D.pdf) :
    HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (X omega)) P)
      (subspaceVolume E) (K ^ d * Real.exp d) := by
  rw [hLaw.projectedMeasure_eq E]
  exact complex_orthogonalProjection_hasBoundedDensity hGBL hK E hE D hcoarea

noncomputable def real_independent_randomProjection_hasBoundedDensity
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
        volume.withDensity (D.pdf i))
    (hcoarea : OrthogonalProjectionCoarea E D.pdf) :
    HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (X omega)) P)
      (subspaceVolume E) (K ^ d * Real.exp (d / 2)) :=
  real_randomProjection_hasBoundedDensity hGBL hK X P E hE D
    (CoordinateProductDensityLaw.ofIndependentReal X P D hX hIndep hmarginal) hcoarea

noncomputable def complex_independent_randomProjection_hasBoundedDensity
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
        volume.withDensity (D.pdf i))
    (hcoarea : OrthogonalProjectionCoarea E D.pdf) :
    HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (X omega)) P)
      (subspaceVolume E) (K ^ d * Real.exp d) :=
  complex_randomProjection_hasBoundedDensity hGBL hK X P E hE D
    (CoordinateProductDensityLaw.ofIndependentComplex X P D hX hIndep hmarginal) hcoarea

noncomputable def real_randomProjection_dimOne
    (hGBL : RealFiniteGeometricBrascampLieb)
    {n : Nat} {K : Real} (hK : 0 < K)
    (X : Omega -> CoordinateSpace Real n) (P : Measure Omega)
    (E : Submodule Real (CoordinateSpace Real n))
    (hE : Module.finrank Real E = 1)
    (D : CoordinateDensityData Real n K)
    (hLaw : CoordinateProductDensityLaw X P D)
    (hcoarea : OrthogonalProjectionCoarea E D.pdf) :
    HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (X omega)) P)
      (subspaceVolume E) (Real.exp 1 * K) := by
  rw [hLaw.projectedMeasure_eq E]
  exact real_orthogonalProjection_dimOne hGBL hK E hE D hcoarea

noncomputable def real_randomProjection_dimTwo
    (hGBL : RealFiniteGeometricBrascampLieb)
    {n : Nat} {K : Real} (hK : 0 < K)
    (X : Omega -> CoordinateSpace Real n) (P : Measure Omega)
    (E : Submodule Real (CoordinateSpace Real n))
    (hE : Module.finrank Real E = 2)
    (D : CoordinateDensityData Real n K)
    (hLaw : CoordinateProductDensityLaw X P D)
    (hcoarea : OrthogonalProjectionCoarea E D.pdf) :
    HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (X omega)) P)
      (subspaceVolume E) (Real.exp 1 * K ^ 2) := by
  rw [hLaw.projectedMeasure_eq E]
  exact real_orthogonalProjection_dimTwo hGBL hK E hE D hcoarea

noncomputable def complex_randomProjection_dimOne
    (hGBL : ComplexFiniteGeometricBrascampLieb)
    {n : Nat} {K : Real} (hK : 0 < K)
    (X : Omega -> CoordinateSpace Complex n) (P : Measure Omega)
    (E : Submodule Complex (CoordinateSpace Complex n))
    (hE : Module.finrank Complex E = 1)
    (D : CoordinateDensityData Complex n K)
    (hLaw : CoordinateProductDensityLaw X P D)
    (hcoarea : OrthogonalProjectionCoarea E D.pdf) :
    HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (X omega)) P)
      (subspaceVolume E) (Real.exp 2 * K) := by
  rw [hLaw.projectedMeasure_eq E]
  exact complex_orthogonalProjection_dimOne hGBL hK E hE D hcoarea

noncomputable def complex_randomProjection_dimTwo
    (hGBL : ComplexFiniteGeometricBrascampLieb)
    {n : Nat} {K : Real} (hK : 0 < K)
    (X : Omega -> CoordinateSpace Complex n) (P : Measure Omega)
    (E : Submodule Complex (CoordinateSpace Complex n))
    (hE : Module.finrank Complex E = 2)
    (D : CoordinateDensityData Complex n K)
    (hLaw : CoordinateProductDensityLaw X P D)
    (hcoarea : OrthogonalProjectionCoarea E D.pdf) :
    HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (X omega)) P)
      (subspaceVolume E) (Real.exp 2 * K ^ 2) := by
  rw [hLaw.projectedMeasure_eq E]
  exact complex_orthogonalProjection_dimTwo hGBL hK E hE D hcoarea

/-- A parameterized family of product-density laws, as obtained after fixing
the variables on which one conditions. -/
structure ConditionalCoordinateProductDensityLaw
    {K : Real} {k : Type*} [RCLike k] {n : Nat}
    (X : Theta -> Omega -> CoordinateSpace k n)
    (P : Theta -> Measure Omega)
    (D : Theta -> CoordinateDensityData k n K) : Prop where
  measurable : forall theta, Measurable (X theta)
  map_eq : forall theta,
    Measure.map (X theta) (P theta) =
      volume.withDensity (coordinateProductDensity (D theta).pdf)

theorem ConditionalCoordinateProductDensityLaw.at
    {K : Real} {k : Type*} [RCLike k] {n : Nat}
    {X : Theta -> Omega -> CoordinateSpace k n}
    {P : Theta -> Measure Omega}
    {D : Theta -> CoordinateDensityData k n K}
    (hLaw : ConditionalCoordinateProductDensityLaw X P D)
    (theta : Theta) : CoordinateProductDensityLaw (X theta) (P theta) (D theta) where
  measurable := hLaw.measurable theta
  map_eq := hLaw.map_eq theta

noncomputable def real_dimOne_afterConditioning
    (hGBL : RealFiniteGeometricBrascampLieb)
    {n : Nat} {K : Real} (hK : 0 < K)
    (X : Theta -> Omega -> CoordinateSpace Real n)
    (P : Theta -> Measure Omega)
    (D : Theta -> CoordinateDensityData Real n K)
    (hLaw : ConditionalCoordinateProductDensityLaw X P D)
    (E : Submodule Real (CoordinateSpace Real n))
    (hE : Module.finrank Real E = 1)
    (hcoarea : forall theta, OrthogonalProjectionCoarea E (D theta).pdf) :
    (theta : Theta) ->
      HasBoundedDensity
        (Measure.map (fun omega => E.orthogonalProjectionOnto (X theta omega)) (P theta))
        (subspaceVolume E) (Real.exp 1 * K) :=
  fun theta => real_randomProjection_dimOne hGBL hK (X theta) (P theta) E hE
    (D theta) (hLaw.at theta) (hcoarea theta)

noncomputable def real_dimTwo_afterConditioning
    (hGBL : RealFiniteGeometricBrascampLieb)
    {n : Nat} {K : Real} (hK : 0 < K)
    (X : Theta -> Omega -> CoordinateSpace Real n)
    (P : Theta -> Measure Omega)
    (D : Theta -> CoordinateDensityData Real n K)
    (hLaw : ConditionalCoordinateProductDensityLaw X P D)
    (E : Submodule Real (CoordinateSpace Real n))
    (hE : Module.finrank Real E = 2)
    (hcoarea : forall theta, OrthogonalProjectionCoarea E (D theta).pdf) :
    (theta : Theta) ->
      HasBoundedDensity
        (Measure.map (fun omega => E.orthogonalProjectionOnto (X theta omega)) (P theta))
        (subspaceVolume E) (Real.exp 1 * K ^ 2) :=
  fun theta => real_randomProjection_dimTwo hGBL hK (X theta) (P theta) E hE
    (D theta) (hLaw.at theta) (hcoarea theta)

noncomputable def complex_dimOne_afterConditioning
    (hGBL : ComplexFiniteGeometricBrascampLieb)
    {n : Nat} {K : Real} (hK : 0 < K)
    (X : Theta -> Omega -> CoordinateSpace Complex n)
    (P : Theta -> Measure Omega)
    (D : Theta -> CoordinateDensityData Complex n K)
    (hLaw : ConditionalCoordinateProductDensityLaw X P D)
    (E : Submodule Complex (CoordinateSpace Complex n))
    (hE : Module.finrank Complex E = 1)
    (hcoarea : forall theta, OrthogonalProjectionCoarea E (D theta).pdf) :
    (theta : Theta) ->
      HasBoundedDensity
        (Measure.map (fun omega => E.orthogonalProjectionOnto (X theta omega)) (P theta))
        (subspaceVolume E) (Real.exp 2 * K) :=
  fun theta => complex_randomProjection_dimOne hGBL hK (X theta) (P theta) E hE
    (D theta) (hLaw.at theta) (hcoarea theta)

noncomputable def complex_dimTwo_afterConditioning
    (hGBL : ComplexFiniteGeometricBrascampLieb)
    {n : Nat} {K : Real} (hK : 0 < K)
    (X : Theta -> Omega -> CoordinateSpace Complex n)
    (P : Theta -> Measure Omega)
    (D : Theta -> CoordinateDensityData Complex n K)
    (hLaw : ConditionalCoordinateProductDensityLaw X P D)
    (E : Submodule Complex (CoordinateSpace Complex n))
    (hE : Module.finrank Complex E = 2)
    (hcoarea : forall theta, OrthogonalProjectionCoarea E (D theta).pdf) :
    (theta : Theta) ->
      HasBoundedDensity
        (Measure.map (fun omega => E.orthogonalProjectionOnto (X theta omega)) (P theta))
        (subspaceVolume E) (Real.exp 2 * K ^ 2) :=
  fun theta => complex_randomProjection_dimTwo hGBL hK (X theta) (P theta) E hE
    (D theta) (hLaw.at theta) (hcoarea theta)

end LivshytsProjectionFormalization

