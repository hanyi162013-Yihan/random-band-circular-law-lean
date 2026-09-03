/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealColumnExposure.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealRandomMatrixModel
import Mathlib.MeasureTheory.Measure.Prod

/-! Exact product disintegration for a real band-matrix column. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HighBandLSV.RealColumnExposure
open HighBandLSV.RealBandModel

abbrev Rest (n : Nat) := Fin n → AtomColumn (n + 1)

def expose {n : Nat} (j : Fin (n + 1)) :
    Sample (n + 1) ≃ᵐ AtomColumn (n + 1) × Rest n :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => AtomColumn (n + 1)) j

def reconstruct {n : Nat} (j : Fin (n + 1)) (x : AtomColumn (n + 1)) (rest : Rest n) :
    Sample (n + 1) := (expose j).symm (x, rest)

@[simp] theorem reconstruct_same {n : Nat} (j : Fin (n + 1)) (x : AtomColumn (n + 1)) (rest : Rest n) :
    reconstruct j x rest j = x := by
  change Fin.insertNth (α := fun _ : Fin (n + 1) => AtomColumn (n + 1)) j x rest j = x
  simp

@[simp] theorem reconstruct_other {n : Nat} (j : Fin (n + 1)) (x : AtomColumn (n + 1)) (rest : Rest n)
    (k : Fin n) : reconstruct j x rest (j.succAbove k) = rest k := by
  change Fin.insertNth (α := fun _ : Fin (n + 1) => AtomColumn (n + 1)) j x rest (j.succAbove k) = rest k
  simp

theorem measurable_reconstruct {n : Nat} (j : Fin (n + 1)) :
    Measurable (fun p : AtomColumn (n + 1) × Rest n => reconstruct j p.1 p.2) :=
  (expose j).symm.measurable

variable {n W : Nat} {c C rho : Real} (m : RealBandModel (n + 1) W c C rho)

def restLaw (j : Fin (n + 1)) : Measure (Rest n) := Measure.pi (fun k => m.columnLaw (j.succAbove k))

instance restLaw_probability (j : Fin (n + 1)) : IsProbabilityMeasure (restLaw m j) := by
  unfold restLaw
  infer_instance

theorem expose_preserving (j : Fin (n + 1)) :
    MeasurePreserving (expose j) m.law ((m.columnLaw j).prod (restLaw m j)) :=
  measurePreserving_piFinSuccAbove m.columnLaw j

/-- A measurable exposed event is bounded by a pointwise bound on every fresh-column fiber. -/
theorem exposure_probability_bound (j : Fin (n + 1))
    (E : Set (Sample (n + 1))) (F : Set (AtomColumn (n + 1) × Rest n))
    (hF : MeasurableSet F) (hcover : E ⊆ expose j ⁻¹' F) {B : ENNReal}
    (hfiber : ∀ rest, m.columnLaw j ((fun x => (x, rest)) ⁻¹' F) ≤ B) : m.law E ≤ B := by
  have heq : m.law (expose j ⁻¹' F) = ((m.columnLaw j).prod (restLaw m j)) F := by
    rw [← (expose_preserving m j).map_eq, Measure.map_apply (expose j).measurable hF]
  calc
    m.law E ≤ m.law (expose j ⁻¹' F) := measure_mono hcover
    _ = ((m.columnLaw j).prod (restLaw m j)) F := heq
    _ = ∫⁻ rest, m.columnLaw j ((fun x => (x, rest)) ⁻¹' F) ∂restLaw m j :=
      Measure.prod_apply_symm hF
    _ ≤ ∫⁻ _rest, B ∂restLaw m j := lintegral_mono hfiber
    _ = B := by simp

end HighBandLSV.RealColumnExposure

#print axioms HighBandLSV.RealColumnExposure.exposure_probability_bound

