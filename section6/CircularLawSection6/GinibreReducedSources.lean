import CircularLawSection6.GinibreNegativeSources
import CircularLawSection6.PublishedConcreteGaussianProfile

/-! # Proved logarithmic reference source for the compatibility route

The Gaussian negative moment is proved from BBV and the actual Gaussian law.
Raw-potential convergence then implies the Ginibre spectral limit by the
proved Section 5 disk-reference argument. This removes the separate raw,
negative and spectral fields from the user-facing source bundle.

`GinibreLogPotentialInput` is constructed from the Section 5 Gaussian law
and the independently proved correlation formulas. The historical bounded
squared-singular-value test limit remains on this compatibility route;
the preferred BBV-only route does not require it.
-/

open MeasureTheory Filter Topology ShortRingAnchor TaoVuReplacement
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete
  (BBVComparisonInput BC12GinibreInput gaussianSequenceLaw ginibreOnSequence)
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace CircularLawSection6

def GinibreLogPotentialInput : Prop :=
  ∀ (N : ℕ → ℕ), (∀ n, 0 < N n) → Tendsto N atTop atTop →
    ∀ z : ℂ, ConvergesInProbability gaussianSequenceLaw
      (fun n ω => normalizedShiftLogDet (ginibreOnSequence (N n) ω) z)
      (circularLogPotential z)

/-- Exact Gaussian log-potential input, proved without a literature premise. -/
theorem verifiedGinibreLogPotentialInput : GinibreLogPotentialInput :=
  CircularLawSections56.Section5.PublishedSection3Concrete.ginibre_logPotential_on_sequence

namespace NoncompactProfile

structure GaussianProfileReducedSources (p : NoncompactProfile) (W : ℕ → ℝ) : Prop where
  bbv : BBVComparisonInput
  ginibreSquared : ClassicalGinibreSquaredTestInput
  coreSection4 : ∀ R : ℕ,
    (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)).ConcreteSection4Input W

theorem GaussianProfileReducedSources.toConcrete
    (p : NoncompactProfile) (W : ℕ → ℝ) (h : GaussianProfileReducedSources p W) :
    GaussianProfileConcreteSources p W where
  bbv := h.bbv
  ginibreSquared := h.ginibreSquared
  coreSection4 := h.coreSection4

end NoncompactProfile
end CircularLawSection6
