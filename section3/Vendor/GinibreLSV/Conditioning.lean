/- Source snapshot: upstream-sources/i-2/work/ginibre-lsv-lean/GinibreLSV/Conditioning.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Conditioning bounds for product measures

This file isolates the Tonelli/Fubini step used in the square Ginibre argument.
If the bad event has probability at most `p` in the fresh coordinate for every
fixed value of the remaining coordinates, then the full product event also has
probability at most `p`.
-/

open MeasureTheory Set

namespace GinibreLSV

theorem prod_measure_le_of_forall_fiber
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [SFinite ν]
    (S : Set (X × Y)) (hS : MeasurableSet S) (p : ENNReal)
    (hfiber : ∀ x, ν (Prod.mk x ⁻¹' S) ≤ p) :
    μ.prod ν S ≤ p := by
  rw [Measure.prod_apply hS]
  calc
    (∫⁻ x, ν (Prod.mk x ⁻¹' S) ∂μ) ≤ ∫⁻ _ : X, p ∂μ :=
      lintegral_mono fun x => hfiber x
    _ = p := by simp

/-- The same conditioning lemma with the fresh coordinate on the left. -/
theorem prod_measure_le_of_forall_left_fiber
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [IsProbabilityMeasure ν]
    (S : Set (X × Y)) (hS : MeasurableSet S) (p : ENNReal)
    (hfiber : ∀ y, μ ((fun x => (x, y)) ⁻¹' S) ≤ p) :
    μ.prod ν S ≤ p := by
  rw [Measure.prod_apply_symm hS]
  calc
    (∫⁻ y, μ ((fun x => (x, y)) ⁻¹' S) ∂ν) ≤ ∫⁻ _ : Y, p ∂ν :=
      lintegral_mono fun y => hfiber y
    _ = p := by simp

end GinibreLSV

