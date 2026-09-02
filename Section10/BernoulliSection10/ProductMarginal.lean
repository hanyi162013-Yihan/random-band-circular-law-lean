import BernoulliSection10.PhysicalModel

/-!
# Finite product marginals

This module proves the measure-preserving coordinate-restriction fact needed
to pass one-site estimates to arbitrary intervals.  Mathlib supplies the
finite-product split and reindexing equivalences; the theorem below composes
them and eliminates the auxiliary complement coordinates.
-/

open MeasureTheory

noncomputable section

namespace BernoulliSection10

open Set

/-- Restricting an i.i.d. finite product to any injectively selected family
of coordinates preserves the corresponding smaller product law. -/
theorem measurePreserving_pi_restrict_embedding
    {ι κ X : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ]
    (e : κ ↪ ι) :
    MeasurePreserving (fun x : ι → X => fun k => x (e k))
      (Measure.pi fun _ : ι => ρ) (Measure.pi fun _ : κ => ρ) := by
  classical
  let S : Finset ι := Finset.univ.map e
  let T : Finset ι := Sᶜ
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro a ha haT
    exact (Finset.mem_compl.mp haT) ha
  have hU : (↑(S ∪ T) : Set ι) = Set.univ := by simp [T]
  let eFull : ↥(S ∪ T) ≃ ι :=
    (Equiv.setCongr hU).trans (Equiv.Set.univ ι)
  have hS : (↑S : Set ι) = Set.range e := by
    ext i
    simp [S]
  let eSel : κ ≃ ↥S :=
    (Equiv.ofInjective e e.injective).trans (Equiv.setCongr hS).symm
  have mpFull := measurePreserving_piCongrLeft (fun _ : ι => ρ) eFull
  have mpSplit := measurePreserving_piFinsetUnion hST (fun _ : ι => ρ)
  have mpFst : MeasurePreserving Prod.fst
      ((Measure.pi fun _ : S => ρ).prod (Measure.pi fun _ : T => ρ))
      (Measure.pi fun _ : S => ρ) := measurePreserving_fst
  have mpSel := measurePreserving_piCongrLeft (fun _ : S => ρ) eSel
  have mp := mpSel.symm (MeasurableEquiv.piCongrLeft (fun _ : S => X) eSel) |>.comp
    (mpFst.comp
      (mpSplit.symm (MeasurableEquiv.piFinsetUnion (fun _ : ι => X) hST) |>.comp
        (mpFull.symm (MeasurableEquiv.piCongrLeft (fun _ : ι => X) eFull))))
  let qFull := MeasurableEquiv.piCongrLeft (fun _ : ι => X) eFull
  let qSplit := MeasurableEquiv.piFinsetUnion (fun _ : ι => X) hST
  let qSel := MeasurableEquiv.piCongrLeft (fun _ : S => X) eSel
  have hfun : (⇑qSel.symm ∘ Prod.fst ∘ ⇑qSplit.symm ∘ ⇑qFull.symm) =
      (fun x : ι → X => fun k => x (e k)) := by
    funext x k
    let y := qFull.symm x
    let p := qSplit.symm y
    let qS : S := eSel k
    let qU : ↥(S ∪ T) :=
      ⟨qS.1, Finset.mem_union_left T qS.2⟩
    have hselApply : qSel (qSel.symm p.1) (eSel k) = qSel.symm p.1 k := by
      simpa only [qSel] using
        (MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : S => X) eSel (qSel.symm p.1) k)
    have hselInv : qSel (qSel.symm p.1) = p.1 := qSel.apply_symm_apply p.1
    have hp : qSplit p = y := qSplit.apply_symm_apply y
    have hpq := congrFun hp qU
    have hleft : qSplit p qU = p.1 qS := by
      exact Equiv.piFinsetUnion_left (fun _ : ι => X) hST qS.2 qU.2
    have hfullApply : qFull y (eFull qU) = y qU := by
      simpa only [qFull] using
        (MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : ι => X) eFull y qU)
    have hfullInv : qFull y = x := qFull.apply_symm_apply x
    have hqS : qS = eSel k := rfl
    have hvalU : eFull qU = e k := by rfl
    change qSel.symm p.1 k = x (e k)
    calc
      qSel.symm p.1 k = qSel (qSel.symm p.1) (eSel k) := hselApply.symm
      _ = p.1 (eSel k) := congrFun hselInv (eSel k)
      _ = p.1 qS := by rw [hqS]
      _ = qSplit p qU := hleft.symm
      _ = y qU := hpq
      _ = qFull y (eFull qU) := hfullApply.symm
      _ = x (eFull qU) := congrFun hfullInv (eFull qU)
      _ = x (e k) := by rw [hvalU]
  rw [hfun] at mp
  exact mp

end BernoulliSection10
