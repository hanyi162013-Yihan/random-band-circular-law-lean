/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/RandomModel.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.VarianceProfile
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Full model assumptions stated in v3 Proposition 3.4

The structure below records the random-matrix assumptions faithfully.  Its fields are metadata
for the conditional theorems; they are not covert axioms and no field asserts the conclusion.
Different entries have the law of *independent copies* of `bᵢⱼ ξ`, rather than sharing one
underlying copy of `ξ`.
-/

namespace Arxiv2410V3

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The entry-law and moment assumptions of v3 Proposition 3.4. -/
structure RandomMatrixModelV3
    (n : ℕ)
    (Omega OmegaXi : Type*) [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    (mu : Measure Omega) (nu : Measure OmegaXi)
    [sample_probability : IsProbabilityMeasure mu]
    [atom_probability : IsProbabilityMeasure nu] where
  matrix : Omega → Matrix (Fin n) (Fin n) ℂ
  atom : OmegaXi → ℂ
  profile : DoublyStochasticVarianceProfile (Fin n)
  entry_measurable : ∀ i j, Measurable (fun omega => matrix omega i j)
  entries_independent :
    iIndepFun (fun ij : Fin n × Fin n => fun omega => matrix omega ij.1 ij.2) mu
  entry_law : ∀ i j,
    IdentDistrib (fun omega => matrix omega i j)
      (fun omegaXi => (profile.coefficient i j : ℂ) * atom omegaXi) mu nu
  atom_integrable : Integrable atom nu
  atom_mean_zero : ∫ omegaXi, atom omegaXi ∂nu = 0
  atom_variance_one : ∫ omegaXi, ‖atom omegaXi‖ ^ 2 ∂nu = 1
  atom_third_moment_finite : Integrable (fun omegaXi => ‖atom omegaXi‖ ^ 3) nu

/-- `log_n B > ε > 0` from v3 Proposition 3.4. -/
structure BandwidthGrowthAssumption (n : ℕ) (B epsilon : ℝ) : Prop where
  epsilon_pos : 0 < epsilon
  logb_gt : epsilon < Real.logb n B

/-- The fixed-parameter scale assumption `|Im η|⁸ B ≥ n^{c'}` in v3 Proposition 3.4. -/
structure EtaScaleAssumption (n : ℕ) (B cPrime : ℝ) (eta : ℂ) : Prop where
  cPrime_pos : 0 < cPrime
  eta_upper : 0 < eta.im
  scale : Real.rpow (n : ℝ) cPrime ≤ |eta.im| ^ 8 * B

end Arxiv2410V3

