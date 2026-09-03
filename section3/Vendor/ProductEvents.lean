/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/ProductEvents.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.MeasureTheory.Constructions.Pi

/-! Exact selected-coordinate event probabilities for the canonical product law. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace HighBandLSV.ProductEvents

 theorem finite_constraints {I Alpha : Type*} [Fintype I] [MeasurableSpace Alpha]
    (mu : I → Measure Alpha) [∀ i, IsProbabilityMeasure (mu i)]
    (S : Finset I) (E : I → Set Alpha) :
    (Measure.pi mu) {omega | ∀ i ∈ S, omega i ∈ E i} = ∏ i ∈ S, mu i (E i) := by
  classical
  have he : {omega | ∀ i ∈ S, omega i ∈ E i} =
      Set.univ.pi (fun i => if i ∈ S then E i else Set.univ) := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ]
    constructor
    · intro h i _
      by_cases hi : i ∈ S
      · simpa only [if_pos hi] using h i hi
      · simp only [if_neg hi, Set.mem_univ]
    · intro h i hi
      simpa only [if_pos hi] using h i True.intro
  rw [he, Measure.pi_pi]
  simp only [apply_ite, measure_univ]
  calc
    (∏ i, if i ∈ S then mu i (E i) else 1) =
        ∏ i ∈ S, if i ∈ S then mu i (E i) else 1 :=
      (Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => if_neg hi)).symm
    _ = ∏ i ∈ S, mu i (E i) := Finset.prod_congr rfl (fun i hi => if_pos hi)

end HighBandLSV.ProductEvents

#print axioms HighBandLSV.ProductEvents.finite_constraints

