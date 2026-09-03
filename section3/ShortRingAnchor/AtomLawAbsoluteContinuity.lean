import ShortRingAnchor.AtomAssumption21
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# From independent atom densities to an absolutely continuous joint law

These elementary measure-theoretic adapters discharge the joint-law part of
the nonsingularity argument used around Proposition 3.6.  Independence is an
explicit probabilistic hypothesis; joint absolute continuity is proved, not
assumed.  Both the real and complex branches of Assumption 2.1 are supported.
-/

noncomputable section

namespace ShortRingAnchor

open MeasureTheory ProbabilityTheory

namespace HasBoundedDensityWithRespectTo

/-- Assumption 2.1's bounded-density record in particular implies absolute
continuity.  Only the existence of the density, not its bound, is needed for
this step of the almost-sure nonsingularity argument. -/
theorem absolutelyContinuous
    {E : Type*} [MeasurableSpace E] {nu lambda : Measure E}
    (h : HasBoundedDensityWithRespectTo nu lambda) : nu ≪ lambda := by
  rw [h.law_eq_withDensity]
  exact withDensity_absolutelyContinuous lambda h.density

/-- For the polynomial-zero-set argument, bounded density also implies
that every singleton is null, whenever this holds for the reference law. -/
theorem nullSingletonClass
    {E : Type*} [MeasurableSpace E] {nu lambda : Measure E}
    [NullSingletonClass lambda]
    (h : HasBoundedDensityWithRespectTo nu lambda) : NullSingletonClass nu :=
  ⟨fun x => h.absolutelyContinuous (measure_singleton x)⟩

end HasBoundedDensityWithRespectTo

/-- In Assumption 2.1's real branch, a null-singleton real-part law implies
a null-singleton complex law.  This needs neither planar absolute
continuity nor any assumption on the imaginary part: a complex singleton
lies in the corresponding real-part level set. -/
theorem complex_law_nullSingletonClass_of_realPart
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (atom : Omega → Complex) (hmeas : AEMeasurable atom mu)
    [NullSingletonClass
      (Measure.map (fun sample => (atom sample).re) mu)] :
    NullSingletonClass (Measure.map atom mu) := by
  constructor
  intro z
  rw [Measure.map_apply_of_aemeasurable hmeas (measurableSet_singleton z)]
  have hreal : AEMeasurable (fun sample => (atom sample).re) mu :=
    Complex.continuous_re.measurable.comp_aemeasurable hmeas
  have hzero : mu ((fun sample => (atom sample).re) ⁻¹' {z.re}) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable hreal (measurableSet_singleton z.re)]
    exact measure_singleton z.re
  refine measure_mono_null ?_ hzero
  intro sample hsample
  change atom sample = z at hsample
  change (atom sample).re = z.re
  exact congrArg Complex.re hsample

namespace AtomDensityAlternative21

/-- Either density alternative in Assumption 2.1 yields a complex atom law
with null singletons.  This is the precise marginal property needed by the
independent-coordinate polynomial zero-set theorem. -/
theorem nullSingletonClass
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {atom : Omega → Complex} (h : AtomDensityAlternative21 mu atom)
    (hmeas : AEMeasurable atom mu) :
    NullSingletonClass (Measure.map atom mu) := by
  cases h with
  | real _ hdensity =>
    let := hdensity.nullSingletonClass
    exact complex_law_nullSingletonClass_of_realPart atom hmeas
  | complex hdensity => exact hdensity.nullSingletonClass

end AtomDensityAlternative21

namespace AtomAssumption21

/-- Complete Assumption 2.1 directly supplies the nonatomic marginal law
used in the finite independent-coordinate nonsingularity proof. -/
theorem nullSingletonClass
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {atom : Omega → Complex} (h : AtomAssumption21 mu atom) :
    NullSingletonClass (Measure.map atom mu) :=
  h.densityAlternative.nullSingletonClass
    h.toAtomMomentAssumption21.measurable.aemeasurable

end AtomAssumption21

/-- The finite-product part of the nonsingularity argument: absolute
continuity is preserved by an iterated product. -/
private theorem tprod_absolutelyContinuous
    {ι : Type*} {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (nu lambda : ∀ i, Measure (E i)) [∀ i, SigmaFinite (lambda i)]
    (h : ∀ i, nu i ≪ lambda i) (indices : List ι) :
    Measure.tprod indices nu ≪ Measure.tprod indices lambda := by
  induction indices with
  | nil => simp only [Measure.tprod_nil]; exact Measure.AbsolutelyContinuous.rfl
  | cons i indices ih =>
    rw [Measure.tprod_cons, Measure.tprod_cons]
    exact (h i).prod ih

/-- The finite-product part of the nonsingularity argument, stated for
arbitrary finite coordinate types and arbitrary sigma-finite marginals. -/
theorem finite_product_absolutelyContinuous
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)]
    (nu lambda : ∀ i, Measure (E i))
    [∀ i, SigmaFinite (nu i)] [∀ i, SigmaFinite (lambda i)]
    (h : ∀ i, nu i ≪ lambda i) : Measure.pi nu ≪ Measure.pi lambda := by
  classical
  let : Encodable ι := Fintype.toEncodable ι
  rw [← Measure.pi'_eq_pi nu, ← Measure.pi'_eq_pi lambda]
  unfold Measure.pi'
  exact (tprod_absolutelyContinuous nu lambda h _).map
    (measurable_tProd_elim' Encodable.mem_sortedUniv)

/-- Independence identifies the joint distribution with the product of its
marginals.  Combined with marginal absolute continuity this proves joint
absolute continuity, with no joint-law hypothesis.  This is the probability
step preceding the polynomial-zero-set nonsingularity argument. -/
theorem independent_jointLaw_absolutelyContinuous
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (atom : ∀ i, Omega → E i) (reference : ∀ i, Measure (E i))
    [∀ i, SigmaFinite (reference i)]
    (hmeas : ∀ i, AEMeasurable (atom i) mu)
    (hindep : iIndepFun atom mu)
    (hac : ∀ i, Measure.map (atom i) mu ≪ reference i) :
    Measure.map (fun sample i => atom i sample) mu ≪ Measure.pi reference := by
  rw [hindep.map_fun_eq_pi_map hmeas]
  exact finite_product_absolutelyContinuous _ reference hac

/-- The complex branch of Assumption 2.1: independent complex atoms with
absolutely continuous marginal laws have a joint law absolutely continuous
with respect to finite-dimensional complex Lebesgue measure. -/
theorem independent_complex_jointLaw_absolutelyContinuous
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (atom : ι → Omega → Complex)
    (hmeas : ∀ i, AEMeasurable (atom i) mu)
    (hindep : iIndepFun atom mu)
    (hac : ∀ i, Measure.map (atom i) mu ≪ (volume : Measure Complex)) :
    Measure.map (fun sample i => atom i sample) mu ≪
      (volume : Measure (ι → Complex)) :=
  independent_jointLaw_absolutelyContinuous atom (fun _ => volume) hmeas hindep hac

/-- The complex bounded-density hypothesis in Assumption 2.1 supplies all
the marginal absolute-continuity premises of the joint-law theorem. -/
theorem independent_complex_jointLaw_of_boundedDensity
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (atom : ι → Omega → Complex)
    (hmeas : ∀ i, AEMeasurable (atom i) mu)
    (hindep : iIndepFun atom mu)
    (hdensity : ∀ i, HasBoundedDensityWithRespectTo
      (Measure.map (atom i) mu) (volume : Measure Complex)) :
    Measure.map (fun sample i => atom i sample) mu ≪
      (volume : Measure (ι → Complex)) :=
  independent_complex_jointLaw_absolutelyContinuous atom hmeas hindep
    (fun i => (hdensity i).absolutelyContinuous)

/-- The real branch of Assumption 2.1 uses one-dimensional Lebesgue measure
in each coordinate, not planar complex measure.  This theorem preserves
that distinction in the joint-law nonsingularity argument. -/
theorem independent_real_jointLaw_absolutelyContinuous
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (atom : ι → Omega → Real)
    (hmeas : ∀ i, AEMeasurable (atom i) mu)
    (hindep : iIndepFun atom mu)
    (hac : ∀ i, Measure.map (atom i) mu ≪ (volume : Measure Real)) :
    Measure.map (fun sample i => atom i sample) mu ≪
      (volume : Measure (ι → Real)) :=
  independent_jointLaw_absolutelyContinuous atom (fun _ => volume) hmeas hindep hac

/-- The real bounded-density hypothesis in Assumption 2.1 gives joint
absolute continuity for any finite independent family of real atoms. -/
theorem independent_real_jointLaw_of_boundedDensity
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (atom : ι → Omega → Real)
    (hmeas : ∀ i, AEMeasurable (atom i) mu)
    (hindep : iIndepFun atom mu)
    (hdensity : ∀ i, HasBoundedDensityWithRespectTo
      (Measure.map (atom i) mu) (volume : Measure Real)) :
    Measure.map (fun sample i => atom i sample) mu ≪
      (volume : Measure (ι → Real)) :=
  independent_real_jointLaw_absolutelyContinuous atom hmeas hindep
    (fun i => (hdensity i).absolutelyContinuous)

end ShortRingAnchor
