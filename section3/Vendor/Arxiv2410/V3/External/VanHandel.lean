/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/External/VanHandel.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.Analysis.Complex.Norm

/-!
# Explicit external interfaces: van Handel and collaborators

Nothing in this file asserts that an interface is inhabited.  Each item is a `Prop`-valued
structure that must be supplied as an explicit argument to the conditional reconstruction.
This keeps the cited analytic inputs visible to `#print` and avoids custom axioms.

The especially cautious name of the first interface records a v3 issue: Brailovskaya--van
Handel, Remark 6.13 is written under bounded-summand standing assumptions, while
arXiv:2410.16457v3 says that its Lindeberg proof extends verbatim to unbounded entries with a
finite third moment.  That extension is not disguised here as a theorem already in mathlib.
-/

namespace Arxiv2410V3.External

/-- Specialized interface for the finite-third-moment extension of
Brailovskaya--van Handel, Remark 6.13, used in v3 formulas (3.11)--(3.12). -/
structure BVHRemark613UnboundedExtensionHypothesis
    (expectedTrace expectedGaussianTrace : ℂ)
    (v thirdMomentBudget constant : ℝ) : Prop where
  estimate :
    ‖expectedTrace - expectedGaussianTrace‖ ≤
      constant / v ^ 4 * thirdMomentBudget

/-- Specialized interface for Bandeira--Boedihardjo--van Handel, Theorem 2.8,
the Gaussian-to-free term in v3 formula (3.11).

In the final reconstruction `freeTrace` is instantiated by the internally constructed
`freeDysonStieltjes`.  Thus this deliberately specialized interface includes the identification
of the abstract free endpoint with that canonical scalar transform; it does not claim to
formalize the underlying operator-valued free-probability construction. -/
structure BBVTheorem28GaussianFreeHypothesis
    (expectedCircularGaussianTrace freeTrace : ℂ)
    (B v constant : ℝ) : Prop where
  estimate :
    ‖expectedCircularGaussianTrace - freeTrace‖ ≤ constant / (B * v ^ 5)

end Arxiv2410V3.External

