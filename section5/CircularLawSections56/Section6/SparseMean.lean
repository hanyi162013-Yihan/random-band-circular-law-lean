import CircularLawSections56.Section6.ProfileMasses
import CircularLawSections56.Section6.RadialAndCutoff

/-!
# Sparse-profile mean limit

This module joins the two deterministic halves of the Section 6 sparse branch.  The
Riemann-mass layer supplies `t_R = 1 - v_R → 0`; the Jensen/Mirsky and hard-edge inputs
supply the lower and upper inequalities consumed by the fourth-root squeeze.
-/

open Filter Topology

namespace CircularLawSections56.Section6

/-- Paper equation `eq:sparse-mean-limit` at the scalar expectation level.

The hypotheses `hLower`, `hUpper`, and `hCutoff` are respectively the tail-Jensen lower
bound, the Mirsky cutoff upper bound, and the linear hard-edge cutoff estimate.  The
compact-core raw potential and its continuity toward the circular potential are recorded
by `hPotential`.  All analytically external facts therefore remain visible inputs; the
choice `a_R = t_R^(1/4)` and the final squeeze are proved locally. -/
theorem sparse_mean_limit_of_core_mass
    (coreMass mean rawCorePotential cutoffCorePotential
      potentialError : ℕ → ℝ)
    (target C : ℝ)
    (hC : 0 ≤ C)
    (hCoreMassOne : Tendsto coreMass atTop (𝓝 1))
    (hTailPositive : ∀ R, 0 < limitingTailMass coreMass R)
    (hLower : ∀ R, rawCorePotential R ≤ mean R)
    (hUpper : ∀ R,
      mean R ≤ cutoffCorePotential R +
        Real.sqrt (limitingTailMass coreMass R) /
          fourthRoot (limitingTailMass coreMass R))
    (hCutoff : ∀ R,
      cutoffCorePotential R - rawCorePotential R ≤
        C * fourthRoot (limitingTailMass coreMass R))
    (hPotential : ∀ R,
      |rawCorePotential R - target| ≤ potentialError R)
    (hPotentialErrorZero : Tendsto potentialError atTop (𝓝 0)) :
    Tendsto mean atTop (𝓝 target) := by
  exact meanSqueeze_fourthRoot_tendsto
    mean rawCorePotential cutoffCorePotential potentialError
    (limitingTailMass coreMass) target C hC hTailPositive hLower hUpper
    hCutoff hPotential (limitingTailMass_tendsto_zero coreMass hCoreMassOne)
    hPotentialErrorZero

/-- Quantitative-tail version of `sparse_mean_limit_of_core_mass`.  It can be used
directly with an integrable-tail majorant without first stating `v_R → 1`. -/
theorem sparse_mean_limit_of_tail_bound
    (coreMass tailMajorant mean rawCorePotential cutoffCorePotential
      potentialError : ℕ → ℝ)
    (target C : ℝ)
    (hC : 0 ≤ C)
    (hTailPositive : ∀ R, 0 < limitingTailMass coreMass R)
    (hTailLe : ∀ R, limitingTailMass coreMass R ≤ tailMajorant R)
    (hTailMajorantZero : Tendsto tailMajorant atTop (𝓝 0))
    (hLower : ∀ R, rawCorePotential R ≤ mean R)
    (hUpper : ∀ R,
      mean R ≤ cutoffCorePotential R +
        Real.sqrt (limitingTailMass coreMass R) /
          fourthRoot (limitingTailMass coreMass R))
    (hCutoff : ∀ R,
      cutoffCorePotential R - rawCorePotential R ≤
        C * fourthRoot (limitingTailMass coreMass R))
    (hPotential : ∀ R,
      |rawCorePotential R - target| ≤ potentialError R)
    (hPotentialErrorZero : Tendsto potentialError atTop (𝓝 0)) :
    Tendsto mean atTop (𝓝 target) := by
  have hTailZero :
      Tendsto (limitingTailMass coreMass) atTop (𝓝 0) :=
    limitingTailMass_tendsto_zero_of_bound coreMass tailMajorant
      (fun R => (hTailPositive R).le) hTailLe hTailMajorantZero
  exact meanSqueeze_fourthRoot_tendsto
    mean rawCorePotential cutoffCorePotential potentialError
    (limitingTailMass coreMass) target C hC hTailPositive hLower hUpper
    hCutoff hPotential hTailZero hPotentialErrorZero

end CircularLawSections56.Section6
