/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealProjectionAdapter.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealProjectionSmallBall
import Vendor.LivshytsProjectionFormalization

open scoped ENNReal

open MeasureTheory ProbabilityTheory Set

namespace HighBandLSV.Real

noncomputable section

/-!
This file connects the separately formalized Livshyts projection-density theorem to the
probabilistic interface used by the repaired Section 5.  The only deep analytic input is
`RealFiniteGeometricBrascampLieb`.  All coordinate transport, Radon--Nikodym identification,
constant comparison, and one/two-dimensional interface assembly are proved below.
-/

/-- Push an explicitly bounded density through a measure-preserving measurable equivalence. -/
def mapLivshytsBoundedDensity
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {projected reference : Measure A} {target : Measure B} {M : Real}
    (h : LivshytsProjectionFormalization.HasBoundedDensity projected reference M)
    (e : A ≃ᵐ B) (he : MeasurePreserving e reference target) :
    LivshytsProjectionFormalization.HasBoundedDensity
      (Measure.map e projected) target M := by
  let f := h.density
  have hf : Measurable f := h.measurable_density
  have hprojected : projected = reference.withDensity f := h.map_eq_withDensity
  refine
    { density := f ∘ e.symm
      measurable_density := hf.comp e.symm.measurable
      map_eq_withDensity := ?_
      density_le := ?_ }
  · calc
      Measure.map e projected = Measure.map e (reference.withDensity f) :=
        congrArg (Measure.map e) hprojected
      _ = target.withDensity (f ∘ e.symm) :=
        LivshytsProjectionFormalization.map_withDensity_measurableEquiv_eq e he f hf
  · intro y
    exact h.density_le (e.symm y)

/-- The basis-normalized subspace volume in the Livshyts development is canonical volume. -/
theorem livshyts_subspaceVolume_eq_volume
    {n : Nat}
    (E : Submodule Real (LivshytsProjectionFormalization.CoordinateSpace Real n)) :
    LivshytsProjectionFormalization.subspaceVolume E = (volume : Measure E) := by
  change Measure.map (LivshytsProjectionFormalization.kernelCoordinateBasis E).repr.symm
      (volume : Measure (LivshytsProjectionFormalization.CoordinateSpace Real
        (Module.finrank Real E))) = (volume : Measure E)
  exact
    (LivshytsProjectionFormalization.kernelCoordinateBasis E).repr.symm.measurePreserving.map_eq

/-- Convert an explicit Livshyts density on `Real` into Mathlib's canonical `pdf` interface. -/
def boundedPDFInterfaceOfLivshytsDensity
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (X : Omega -> Real) (M : Real) (hM : 0 <= M) (hX : Measurable X)
    (h : LivshytsProjectionFormalization.HasBoundedDensity
      (Measure.map X P) (volume : Measure Real) M) :
    BoundedPDFInterface Omega P X M where
  hasPDF := hasPDF_of_map_eq_withDensity hX.aemeasurable h.density
    h.measurable_density.aemeasurable h.map_eq_withDensity
  rho_nonneg := hM
  density_le := by
    let f := h.density
    have hf : Measurable f := h.measurable_density
    have hmap : Measure.map X P = volume.withDensity f := h.map_eq_withDensity
    have hpdf : pdf X P volume =ᵐ[volume] f := by
      rw [pdf_def, hmap]
      exact Measure.rnDeriv_withDensity volume hf
    filter_upwards [hpdf] with x hx
    rw [hx]
    exact h.density_le x

/-- Convert an explicit Livshyts density on the real coordinate plane into the local interface. -/
def boundedPlanePDFInterfaceOfLivshytsDensity
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (Y : Omega -> Real × Real) (M : Real) (hM : 0 <= M) (hY : Measurable Y)
    (h : LivshytsProjectionFormalization.HasBoundedDensity
      (Measure.map Y P) realPlaneMeasure M) :
    BoundedPlanePDFInterface Omega P Y M where
  hasPDF := hasPDF_of_map_eq_withDensity hY.aemeasurable h.density
    h.measurable_density.aemeasurable h.map_eq_withDensity
  rho_nonneg := hM
  density_le := by
    let f := h.density
    have hf : Measurable f := h.measurable_density
    have hmap : Measure.map Y P = realPlaneMeasure.withDensity f := h.map_eq_withDensity
    have hpdf : pdf Y P realPlaneMeasure =ᵐ[realPlaneMeasure] f := by
      rw [pdf_def, hmap]
      exact Measure.rnDeriv_withDensity realPlaneMeasure hf
    filter_upwards [hpdf] with y hy
    rw [hy]
    exact h.density_le y

/-- Increasing a one-dimensional density bound preserves the local interface. -/
def BoundedPDFInterface.mono
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : Omega -> Real} {M N : Real}
    (data : BoundedPDFInterface Omega P X M) (hMN : M <= N) :
    BoundedPDFInterface Omega P X N where
  hasPDF := data.hasPDF
  rho_nonneg := data.rho_nonneg.trans hMN
  density_le := data.density_le.mono fun _ hx =>
    hx.trans (ENNReal.ofReal_le_ofReal hMN)

/-- Increasing a planar density bound preserves the local interface. -/
def BoundedPlanePDFInterface.mono
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {Y : Omega -> Real × Real} {M N : Real}
    (data : BoundedPlanePDFInterface Omega P Y M) (hMN : M <= N) :
    BoundedPlanePDFInterface Omega P Y N where
  hasPDF := data.hasPDF
  rho_nonneg := data.rho_nonneg.trans hMN
  density_le := data.density_le.mono fun _ hx =>
    hx.trans (ENNReal.ofReal_le_ofReal hMN)

/-- Copy the separately formalized one-dimensional bounded-pdf interface into this project. -/
def boundedPDFInterfaceOfExternal
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : Omega -> Real} {M : Real}
    (data : LivshytsProjectionFormalization.BoundedPDFInterface Omega P X M) :
    BoundedPDFInterface Omega P X M where
  hasPDF := data.hasPDF
  rho_nonneg := data.rho_nonneg
  density_le := data.density_le

/-- Copy the separately formalized planar bounded-pdf interface into this project. -/
def boundedPlanePDFInterfaceOfExternal
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {Y : Omega -> Real × Real} {M : Real}
    (data : LivshytsProjectionFormalization.BoundedPlanePDFInterface Omega P Y M) :
    BoundedPlanePDFInterface Omega P Y M where
  hasPDF := data.hasPDF
  rho_nonneg := data.rho_nonneg
  density_le := data.density_le

/-- The sharp `sqrt 2, 2` external Section 5 interface implies the local common-constant
interface with constant `2`.  This is an optional adapter; the direct GBL adapter below uses
the (weaker but sufficient) common constant `exp 1`. -/
def oneTwoProjectionDensityInterfaceOfExternal
    {Omega : Type*} [MeasurableSpace Omega] {m : Nat} {P : Measure Omega}
    {xi : Omega -> EuclideanSpace Real (Fin m)} {K : Real}
    (hK : 0 <= K)
    (data : LivshytsProjectionFormalization.LivshytsSection5ProjectionInput
      Omega m P xi K) :
    OneTwoProjectionDensityInterface Omega m P xi K 2 where
  one p hp := by
    apply BoundedPDFInterface.mono
      (boundedPDFInterfaceOfExternal (data.h_one p hp))
    have hsqrt : Real.sqrt 2 <= 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) <= 2), Real.sqrt_nonneg 2]
    exact mul_le_mul_of_nonneg_right hsqrt hK
  two p r hp hr hpr := by
    simpa using boundedPlanePDFInterfaceOfExternal (data.h_two p r hp hr hpr)

/-- A one-dimensional projection density obtained directly from finite geometric BL, independent
coordinate densities, proved coarea, and orthonormal coordinate transport. -/
def realOneProjectionBoundedPDFFromGBL
    {Omega : Type*} [MeasurableSpace Omega] {m : Nat} {P : Measure Omega}
    {xi : Omega -> EuclideanSpace Real (Fin m)} {K : Real}
    (hGBL : LivshytsProjectionFormalization.RealFiniteGeometricBrascampLieb)
    (hK : 0 < K) (hxi : Measurable xi)
    (hIndep : iIndepFun (fun i omega => xi omega i) P)
    (D : LivshytsProjectionFormalization.CoordinateDensityData Real m K)
    (hmarginal : forall i,
      Measure.map (fun omega => xi omega i) P = volume.withDensity (D.pdf i))
    (p : EuclideanSpace Real (Fin m)) (hp : ‖p‖ = 1) :
    BoundedPDFInterface Omega P (fun omega => inner Real (xi omega) p)
      (Real.exp 1 * K) := by
  have hp0 : p ≠ 0 := by
    intro hpzero
    rw [hpzero, norm_zero] at hp
    norm_num at hp
  let E : Submodule Real (EuclideanSpace Real (Fin m)) := Real ∙ p
  have hE : Module.finrank Real E = 1 := by
    simpa [E] using finrank_span_singleton hp0
  let pE : E := ⟨p, Submodule.mem_span_singleton_self p⟩
  have hpE : ‖pE‖ = 1 := by simpa [pE] using hp
  let b : OrthonormalBasis (Fin 1) Real E :=
    FiniteDimensional.orthonormalBasisSingleton (Fin 1) Real hE pE hpE
  let coord : E ≃ᵐ Real :=
    b.repr.toMeasurableEquiv |>.trans
      ((MeasurableEquiv.toLp 2 (Fin 1 -> Real)).symm.trans
        (MeasurableEquiv.funUnique (Fin 1) Real))
  have hcoordPreserving : MeasurePreserving coord (volume : Measure E) volume := by
    exact (volume_preserving_funUnique (Fin 1) Real).comp
      ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1)).comp
        b.repr.measurePreserving)
  let hraw :=
    LivshytsProjectionFormalization.real_independent_randomProjection_hasBoundedDensity_provedCoarea
      hGBL hK xi P hxi hIndep E hE D hmarginal
  have hrawBound : LivshytsProjectionFormalization.HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (xi omega)) P)
      (LivshytsProjectionFormalization.subspaceVolume E)
      (Real.exp 1 * K) := by
    apply hraw.mono
    simp only [pow_one, Nat.cast_one]
    have hexp : Real.exp ((1 : Real) / 2) <= Real.exp 1 :=
      Real.exp_le_exp.mpr (by norm_num)
    calc
      K * Real.exp ((1 : Real) / 2) <= K * Real.exp 1 :=
        mul_le_mul_of_nonneg_left hexp hK.le
      _ = Real.exp 1 * K := mul_comm _ _
  have hvolume : LivshytsProjectionFormalization.HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (xi omega)) P)
      (volume : Measure E) (Real.exp 1 * K) := by
    simpa only [livshyts_subspaceVolume_eq_volume E] using hrawBound
  have hmapped := mapLivshytsBoundedDensity hvolume coord hcoordPreserving
  have hpoint (x : EuclideanSpace Real (Fin m)) :
      coord (E.orthogonalProjectionOnto x) = inner Real x p := by
    simp only [coord, MeasurableEquiv.trans_apply]
    change b.repr (E.orthogonalProjectionOnto x) default = inner Real x p
    rw [OrthonormalBasis.repr_apply_apply]
    have hb0 : b default = pE := by simp [b]
    rw [hb0]
    rw [E.inner_orthogonalProjectionOnto_eq_of_mem_left]
    simpa [pE] using (real_inner_comm p x).symm
  have hmap :
      Measure.map coord
          (Measure.map (fun omega => E.orthogonalProjectionOnto (xi omega)) P) =
        Measure.map (fun omega => inner Real (xi omega) p) P := by
    rw [Measure.map_map coord.measurable (by fun_prop)]
    congr 1
    funext omega
    exact hpoint (xi omega)
  rw [hmap] at hmapped
  exact boundedPDFInterfaceOfLivshytsDensity P
    (fun omega => inner Real (xi omega) p) (Real.exp 1 * K)
    (mul_nonneg (Real.exp_pos _).le hK.le) (by fun_prop) hmapped

/-- A two-dimensional projection density obtained directly from finite geometric BL.  The explicit
orthonormal basis `p,r` identifies the projected subspace with the real coordinate plane. -/
def realTwoProjectionBoundedPDFFromGBL
    {Omega : Type*} [MeasurableSpace Omega] {m : Nat} {P : Measure Omega}
    {xi : Omega -> EuclideanSpace Real (Fin m)} {K : Real}
    (hGBL : LivshytsProjectionFormalization.RealFiniteGeometricBrascampLieb)
    (hK : 0 < K) (hxi : Measurable xi)
    (hIndep : iIndepFun (fun i omega => xi omega i) P)
    (D : LivshytsProjectionFormalization.CoordinateDensityData Real m K)
    (hmarginal : forall i,
      Measure.map (fun omega => xi omega i) P = volume.withDensity (D.pdf i))
    (p r : EuclideanSpace Real (Fin m)) (hp : ‖p‖ = 1) (hr : ‖r‖ = 1)
    (hpr : inner Real p r = 0) :
    BoundedPlanePDFInterface Omega P
      (fun omega => (inner Real (xi omega) p, inner Real (xi omega) r))
      (Real.exp 1 * K ^ 2) := by
  let v : Fin 2 -> EuclideanSpace Real (Fin m) := ![p, r]
  have hv : Orthonormal Real v := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · simp [v, inner_self_eq_norm_sq, hp]
    · simpa [v] using hpr
    · simpa [v, real_inner_comm] using hpr
    · simp [v, inner_self_eq_norm_sq, hr]
  let E : Submodule Real (EuclideanSpace Real (Fin m)) :=
    Submodule.span Real (Set.range v)
  have hE : Module.finrank Real E = 2 := by
    simpa [E] using finrank_span_eq_card hv.linearIndependent
  let vE : Fin 2 -> E := fun i =>
    ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hvE : Orthonormal Real vE := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa [vE] using
      (show inner Real (v i) (v j) = if i = j then 1 else 0 from
        (orthonormal_iff_ite.mp hv i j))
  have hspan : Submodule.span Real (Set.range vE) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hvE.linearIndependent, hE]
    simp
  let b : OrthonormalBasis (Fin 2) Real E := OrthonormalBasis.mk hvE hspan.ge
  have hb (i : Fin 2) : ((b i : E) : EuclideanSpace Real (Fin m)) = v i := by
    simp [b, vE]
  let coord : E ≃ᵐ Real × Real :=
    b.repr.toMeasurableEquiv |>.trans
      ((MeasurableEquiv.toLp 2 (Fin 2 -> Real)).symm.trans
        MeasurableEquiv.finTwoArrow)
  have hcoordPreserving :
      MeasurePreserving coord (volume : Measure E) realPlaneMeasure := by
    exact (volume_preserving_piFinTwo (fun _ : Fin 2 => Real)).comp
      ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).comp
        b.repr.measurePreserving)
  let hraw :=
    LivshytsProjectionFormalization.real_independent_randomProjection_hasBoundedDensity_provedCoarea
      hGBL hK xi P hxi hIndep E hE D hmarginal
  have hrawBound : LivshytsProjectionFormalization.HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (xi omega)) P)
      (LivshytsProjectionFormalization.subspaceVolume E)
      (Real.exp 1 * K ^ 2) := by
    apply hraw.mono
    simpa [mul_comm]
  have hvolume : LivshytsProjectionFormalization.HasBoundedDensity
      (Measure.map (fun omega => E.orthogonalProjectionOnto (xi omega)) P)
      (volume : Measure E) (Real.exp 1 * K ^ 2) := by
    simpa only [livshyts_subspaceVolume_eq_volume E] using hrawBound
  have hmapped := mapLivshytsBoundedDensity hvolume coord hcoordPreserving
  have hcoordinate (x : EuclideanSpace Real (Fin m)) (i : Fin 2) :
      b.repr (E.orthogonalProjectionOnto x) i = inner Real (v i) x := by
    rw [OrthonormalBasis.repr_apply_apply]
    calc
      inner Real (b i) (E.orthogonalProjectionOnto x) =
          inner Real ((b i : E) : EuclideanSpace Real (Fin m)) x :=
        E.inner_orthogonalProjectionOnto_eq_of_mem_left (b i) x
      _ = inner Real (v i) x := by rw [hb]
  have hpoint (x : EuclideanSpace Real (Fin m)) :
      coord (E.orthogonalProjectionOnto x) = (inner Real x p, inner Real x r) := by
    simp only [coord, MeasurableEquiv.trans_apply]
    change (b.repr (E.orthogonalProjectionOnto x) 0,
      b.repr (E.orthogonalProjectionOnto x) 1) = (inner Real x p, inner Real x r)
    apply Prod.ext
    · simpa [v, real_inner_comm] using hcoordinate x 0
    · simpa [v, real_inner_comm] using hcoordinate x 1
  have hmap :
      Measure.map coord
          (Measure.map (fun omega => E.orthogonalProjectionOnto (xi omega)) P) =
        Measure.map
          (fun omega => (inner Real (xi omega) p, inner Real (xi omega) r)) P := by
    rw [Measure.map_map coord.measurable (by fun_prop)]
    congr 1
    funext omega
    exact hpoint (xi omega)
  rw [hmap] at hmapped
  exact boundedPlanePDFInterfaceOfLivshytsDensity P
    (fun omega => (inner Real (xi omega) p, inner Real (xi omega) r))
    (Real.exp 1 * K ^ 2)
    (mul_nonneg (Real.exp_pos _).le (sq_nonneg K)) (by fun_prop) hmapped

/-- Main bridge: independent real coordinates with densities bounded by `K`, together with the
finite geometric Brascamp--Lieb inequality, supply exactly the one/two projection interface used
by the repaired Section 5.  A single common absolute constant `exp 1` is sufficient. -/
def realOneTwoProjectionDensityInterfaceFromGBL
    {Omega : Type*} [MeasurableSpace Omega] {m : Nat} {P : Measure Omega}
    {xi : Omega -> EuclideanSpace Real (Fin m)} {K : Real}
    (hGBL : LivshytsProjectionFormalization.RealFiniteGeometricBrascampLieb)
    (hK : 0 < K) (hxi : Measurable xi)
    (hIndep : iIndepFun (fun i omega => xi omega i) P)
    (D : LivshytsProjectionFormalization.CoordinateDensityData Real m K)
    (hmarginal : forall i,
      Measure.map (fun omega => xi omega i) P = volume.withDensity (D.pdf i)) :
    OneTwoProjectionDensityInterface Omega m P xi K (Real.exp 1) where
  one p hp :=
    realOneProjectionBoundedPDFFromGBL hGBL hK hxi hIndep D hmarginal p hp
  two p r hp hr hpr :=
    realTwoProjectionBoundedPDFFromGBL hGBL hK hxi hIndep D hmarginal p r hp hr hpr

end

end HighBandLSV.Real

#print axioms HighBandLSV.Real.realOneTwoProjectionDensityInterfaceFromGBL

