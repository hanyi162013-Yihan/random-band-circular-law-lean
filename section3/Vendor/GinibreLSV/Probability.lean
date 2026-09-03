/- Source snapshot: upstream-sources/i-2/work/ginibre-lsv-lean/GinibreLSV/Probability.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.GinibreLSV.Deterministic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# A union-bound least-singular-value theorem

This file turns one-column distance small-ball estimates into a square
least-singular-value estimate.  It is distribution-independent; Gaussianity
enters only when proving the one-column hypotheses.
-/

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace GinibreLSV

theorem leastSingularValue_lt_imp_exists_columnDistance_lt {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ)
    (hsmall : leastSingularValue A < δ / (n : ℝ)) :
    ∃ j, columnDistance A j < δ := by
  by_contra h
  push Not at h
  have hlower := delta_div_nat_le_leastSingularValue hn A h
  exact (not_lt_of_ge hlower) hsmall

/-- Abstract square least-singular-value lower-tail bound.

If each column has probability at most `p` of lying within distance `δ` of
the span of the other columns, then the probability that the least singular
value is below `δ / n` is at most `n p`.

No independence or measurability assumptions are needed at this layer: those
belong in the proof of the individual column estimates.
-/
theorem measure_leastSingularValue_lt_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 0 < n)
    (A : Ω → Matrix (Fin n) (Fin n) ℂ) (δ : ℝ) (p : ℝ≥0∞)
    (hcol : ∀ j, μ {ω | columnDistance (A ω) j < δ} ≤ p) :
    μ {ω | leastSingularValue (A ω) < δ / (n : ℝ)} ≤ (n : ℝ≥0∞) * p := by
  let badColumn : Fin n → Set Ω := fun j => {ω | columnDistance (A ω) j < δ}
  have hsubset : {ω | leastSingularValue (A ω) < δ / (n : ℝ)} ⊆ ⋃ j, badColumn j := by
    intro ω hω
    obtain ⟨j, hj⟩ := leastSingularValue_lt_imp_exists_columnDistance_lt hn (A ω) δ hω
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  calc
    μ {ω | leastSingularValue (A ω) < δ / (n : ℝ)} ≤ μ (⋃ j, badColumn j) :=
      measure_mono hsubset
    _ ≤ ∑ j, μ (badColumn j) := measure_iUnion_fintype_le μ badColumn
    _ ≤ ∑ _j : Fin n, p := Finset.sum_le_sum fun j _ => hcol j
    _ = (n : ℝ≥0∞) * p := by simp

end GinibreLSV

