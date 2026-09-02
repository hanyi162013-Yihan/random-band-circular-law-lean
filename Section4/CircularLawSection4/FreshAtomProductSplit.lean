import CircularLawSection4.Isolation
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Splitting selected and unselected fresh atoms

A reset word chooses one atom in every fresh row.  This file constructs the
corresponding measurable coordinate split and proves that a finite IID product
law becomes the product of the selected coordinates and all frozen remaining
coordinates.  It is the independence/Fubini bridge used by the literal
one-fresh-block logarithmic closure.
-/

open scoped MeasureTheory
open MeasureTheory

noncomputable section

namespace CircularLawSection4

universe u

/-- One reset-labelled atom in each of `k` fresh rows. -/
abbrev FreshAtomIndex (k : ℕ) := Fin k × ResetLabel k

/-- The atom coordinates not selected by a fixed reset word. -/
def UnselectedFreshIndex {k : ℕ} (word : Fin k → ResetLabel k) :=
  {u : FreshAtomIndex k // u.2 ≠ word u.1}

noncomputable instance unselectedFreshIndexFintype {k : ℕ}
    (word : Fin k → ResetLabel k) : Fintype (UnselectedFreshIndex word) :=
  by
    classical
    exact Fintype.ofFinset
      (Finset.univ.filter fun u : FreshAtomIndex k => u.2 ≠ word u.1)
      (by
        intro u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rfl)

/-- The graph of a reset word is canonically equivalent to its row index. -/
def selectedFreshIndexEquiv {k : ℕ} (word : Fin k → ResetLabel k) :
    Fin k ≃ {u : FreshAtomIndex k // u.2 = word u.1} where
  toFun t := ⟨(t, word t), rfl⟩
  invFun u := u.1.1
  left_inv _ := rfl
  right_inv u := by
    apply Subtype.ext
    rcases u with ⟨⟨t, ell⟩, h⟩
    simp only
    exact Prod.ext rfl h.symm

/-- Split the full fresh-atom index into the selected graph of `word` and
its complement. -/
def freshAtomIndexSumEquiv {k : ℕ} (word : Fin k → ResetLabel k) :
    Fin k ⊕ UnselectedFreshIndex word ≃ FreshAtomIndex k :=
  (Equiv.sumCongr (selectedFreshIndexEquiv word) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun u : FreshAtomIndex k => u.2 = word u.1))

/-- Coordinate split into the selected atom in every row and all remaining
atoms.  All spaces carry their product measurable structures. -/
def splitFreshAtomMeasurableEquiv {K : Type u} [MeasurableSpace K]
    {k : ℕ} (word : Fin k → ResetLabel k) :
    (FreshAtomIndex k → K) ≃ᵐ
      (Fin k → K) × (UnselectedFreshIndex word → K) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : FreshAtomIndex k => K) (freshAtomIndexSumEquiv word)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin k ⊕ UnselectedFreshIndex word => K))

@[simp]
theorem splitFreshAtomMeasurableEquiv_selected
    {K : Type u} [MeasurableSpace K] {k : ℕ}
    (word : Fin k → ResetLabel k) (ω : FreshAtomIndex k → K) (t : Fin k) :
    (splitFreshAtomMeasurableEquiv word ω).1 t = ω (t, word t) := by
  rfl

@[simp]
theorem splitFreshAtomMeasurableEquiv_unselected
    {K : Type u} [MeasurableSpace K] {k : ℕ}
    (word : Fin k → ResetLabel k) (ω : FreshAtomIndex k → K)
    (u : UnselectedFreshIndex word) :
    (splitFreshAtomMeasurableEquiv word ω).2 u = ω u.1 := by
  rfl

@[simp]
theorem splitFreshAtomMeasurableEquiv_symm_selected
    {K : Type u} [MeasurableSpace K] {k : ℕ}
    (word : Fin k → ResetLabel k)
    (x : Fin k → K) (y : UnselectedFreshIndex word → K) (t : Fin k) :
    (splitFreshAtomMeasurableEquiv word).symm (x, y) (t, word t) = x t := by
  have h := congrArg (fun p => p.1 t)
    ((splitFreshAtomMeasurableEquiv word).apply_symm_apply (x, y))
  simpa only [splitFreshAtomMeasurableEquiv_selected] using h

@[simp]
theorem splitFreshAtomMeasurableEquiv_symm_unselected
    {K : Type u} [MeasurableSpace K] {k : ℕ}
    (word : Fin k → ResetLabel k)
    (x : Fin k → K) (y : UnselectedFreshIndex word → K)
    (u : UnselectedFreshIndex word) :
    (splitFreshAtomMeasurableEquiv word).symm (x, y) u.1 = y u := by
  have h := congrArg (fun p => p.2 u)
    ((splitFreshAtomMeasurableEquiv word).apply_symm_apply (x, y))
  simpa only [splitFreshAtomMeasurableEquiv_unselected] using h

/-- The coordinate split is measure preserving for a finite IID atom law.
Thus the selected atoms are IID and independent of all frozen atoms. -/
theorem splitFreshAtom_measurePreserving
    {K : Type u} [MeasurableSpace K] {k : ℕ}
    (word : Fin k → ResetLabel k) (ν : Measure K)
    [SigmaFinite ν] [IsProbabilityMeasure ν] :
    MeasurePreserving (splitFreshAtomMeasurableEquiv word)
      (Measure.pi (fun _ : FreshAtomIndex k => ν))
      ((Measure.pi (fun _ : Fin k => ν)).prod
        (Measure.pi (fun _ : UnselectedFreshIndex word => ν))) := by
  have hreindex :=
    (measurePreserving_piCongrLeft
      (fun _ : FreshAtomIndex k => ν) (freshAtomIndexSumEquiv word)).symm
  have hsplit := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin k ⊕ UnselectedFreshIndex word => ν)
  simpa only [splitFreshAtomMeasurableEquiv, MeasurableEquiv.coe_trans,
    Function.comp_def] using hsplit.comp hreindex

end CircularLawSection4
