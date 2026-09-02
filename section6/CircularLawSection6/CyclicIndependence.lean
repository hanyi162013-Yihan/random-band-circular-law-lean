import CircularLawSection6.CyclicMatrix
import Mathlib.Probability.Independence.Basic

/-! # Independence of actual core and tail matrices

The proof factors the matrices through disjoint coordinate restrictions of
the product atom space. Disjoint matrix support alone would not suffice.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace CircularLawSection6

/-- The product sigma-algebra on the finitely indexed matrix entries. -/
instance cyclicMatrix_measurableSpace (N : ℕ) :
    MeasurableSpace (Matrix (ZMod N) (ZMod N) ℂ) :=
  inferInstanceAs (MeasurableSpace (ZMod N → ZMod N → ℂ))

def zeroExtendAtoms {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (x : S → ℂ) (i : ι) : ℂ :=
  if hi : i ∈ S then x ⟨i, hi⟩ else 0

theorem zeroExtendAtoms_measurable {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    Measurable (zeroExtendAtoms S) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ∈ S
  · simpa only [zeroExtendAtoms, dif_pos hi] using (measurable_pi_apply (⟨i, hi⟩ : S))
  · simpa only [zeroExtendAtoms, dif_neg hi] using
      (measurable_const : Measurable (fun _ : S → ℂ => (0 : ℂ)))

theorem weightedCyclicMatrix_measurable_matrix (N : ℕ) (q : ZMod N → ℝ) :
    Measurable (weightedCyclicMatrix N q) :=
  measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    weightedCyclicMatrix_measurable N q i j

theorem cyclicAtoms_independent (N : ℕ) [NeZero N]
    (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    iIndepFun (fun k (ω : ZMod N × ZMod N → ℂ) => ω k) (cyclicAtomLaw N ν) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

def activeAtomIndices (N : ℕ) [NeZero N] (S : Finset (ZMod N)) :
    Finset (ZMod N × ZMod N) := Finset.univ.filter (fun k => k.2 ∈ S)

theorem weightedCyclicMatrix_core_tail_independent
    (N : ℕ) [NeZero N] (S : Finset (ZMod N)) (q : ZMod N → ℝ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    IndepFun (weightedCyclicMatrix N (maskedWeight S q))
      (weightedCyclicMatrix N (maskedWeight Sᶜ q)) (cyclicAtomLaw N ν) := by
  let I := activeAtomIndices N S
  have hInd := (cyclicAtoms_independent N ν).indepFun_finset I Iᶜ
    disjoint_compl_right (fun _ => measurable_pi_apply _)
  have hm (J : Finset (ZMod N × ZMod N)) :
      Measurable (fun x : J → ℂ => weightedCyclicMatrix N q (zeroExtendAtoms J x)) :=
    (weightedCyclicMatrix_measurable_matrix N q).comp (zeroExtendAtoms_measurable J)
  have h := hInd.comp (hm I) (hm Iᶜ)
  have hcore : (fun ω : ZMod N × ZMod N → ℂ =>
      weightedCyclicMatrix N q (zeroExtendAtoms I (fun i : I => ω i))) =
        weightedCyclicMatrix N (maskedWeight S q) := by
    funext ω i j
    by_cases hs : j - i ∈ S <;>
      simp [weightedCyclicMatrix, zeroExtendAtoms, I, activeAtomIndices, maskedWeight, hs]
  have htail : (fun ω : ZMod N × ZMod N → ℂ =>
      weightedCyclicMatrix N q (zeroExtendAtoms Iᶜ (fun i : ↥(Iᶜ) => ω i))) =
        weightedCyclicMatrix N (maskedWeight Sᶜ q) := by
    funext ω i j
    by_cases hs : j - i ∈ S <;>
      simp [weightedCyclicMatrix, zeroExtendAtoms, I, activeAtomIndices, maskedWeight, hs]
  simpa only [Function.comp_def, hcore, htail] using h

end CircularLawSection6
