import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Marginals of finite IID product measures

Restricting a finite IID product sample to any injectively indexed family of
coordinates preserves the corresponding IID product law.  The probability
assumption is essential when the injection is not surjective: projection away
from unused coordinates otherwise multiplies the marginal by their total mass.
-/

open MeasureTheory Set

namespace CircularLawSection4

/-- Restriction of a finite IID product sample along an injection has the IID
product law on the smaller index type. -/
theorem measurePreserving_pi_restrict_injective
    {K κ ι : Type*} [MeasurableSpace K] [Fintype κ] [Fintype ι]
    (e : κ → ι) (he : Function.Injective e) (nu : Measure K)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving
      (fun omega : ι → K => fun k => omega (e k))
      (Measure.pi (fun _ : ι => nu))
      (Measure.pi (fun _ : κ => nu)) := by
  classical
  let p : ι → Prop := fun i => i ∈ Set.range e
  letI : Fintype (Subtype p) := Subtype.fintype p
  letI : Fintype (Subtype (fun i => ¬p i)) := Subtype.fintype (fun i => ¬p i)
  let rangeEquiv : κ ≃ Subtype p := Equiv.ofInjective e he
  have hsplit :
      MeasurePreserving
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => K) p)
        (Measure.pi (fun _ : ι => nu))
        ((Measure.pi (fun _ : Subtype p => nu)).prod
          (Measure.pi (fun _ : Subtype (fun i => ¬p i) => nu))) := by
    simpa only using
      (measurePreserving_piEquivPiSubtypeProd
        (fun _ : ι => nu) p)
  have hproject :
      MeasurePreserving
        (fun omega : ι → K => fun i : Subtype p => omega i)
        (Measure.pi (fun _ : ι => nu))
        (Measure.pi (fun _ : Subtype p => nu)) := by
    have hfst :
        MeasurePreserving
          (Prod.fst :
            (Subtype p → K) × (Subtype (fun i => ¬p i) → K) →
              (Subtype p → K))
          ((Measure.pi (fun _ : Subtype p => nu)).prod
            (Measure.pi (fun _ : Subtype (fun i => ¬p i) => nu)))
          (Measure.pi (fun _ : Subtype p => nu)) :=
      measurePreserving_fst
    simpa only [MeasurableEquiv.piEquivPiSubtypeProd_apply,
      Function.comp_def] using hfst.comp hsplit
  have hreindex :
      MeasurePreserving
        (fun omega : Subtype p → K => fun k : κ => omega (rangeEquiv k))
        (Measure.pi (fun _ : Subtype p => nu))
        (Measure.pi (fun _ : κ => nu)) := by
    have hfun :
        (MeasurableEquiv.piCongrLeft (fun _ : κ => K) rangeEquiv.symm :
          (Subtype p → K) → (κ → K)) =
            (fun omega => fun k => omega (rangeEquiv k)) := by
      funext omega k
      simp only [MeasurableEquiv.coe_piCongrLeft,
        Equiv.piCongrLeft_apply, eq_rec_constant, Equiv.symm_symm]
    rw [← hfun]
    exact measurePreserving_piCongrLeft
      (fun _ : κ => nu) rangeEquiv.symm
  simpa only [p, rangeEquiv, Equiv.ofInjective_apply, Function.comp_def] using
    hreindex.comp hproject

end CircularLawSection4
