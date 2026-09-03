/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/ProbabilityEvent.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Elementary real-valued event probability bounds

This file contains only notation used throughout the reconstruction.  It is not an external
mathematical interface.
-/

namespace Arxiv2410V3

open MeasureTheory

/-- A real-number lower bound on the measure of an event. -/
def ProbabilityAtLeast {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (event : Set Omega) (p : ℝ) : Prop :=
  ENNReal.ofReal p ≤ mu event

end Arxiv2410V3

