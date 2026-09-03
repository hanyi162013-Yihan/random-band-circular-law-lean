import CircularLawSection6.GinibreNegativeSources
import CircularLawSection6.PublishedConcreteGaussianProfile

/-! # One retained logarithmic reference source, with no duplicate Ginibre inputs

The Gaussian negative moment is proved from BBV and the actual Gaussian law.
Raw-potential convergence then implies the Ginibre spectral limit by the
proved Section 5 disk-reference argument. This removes the separate raw,
negative and spectral fields from the user-facing source bundle.

`GinibreLogPotentialInput` remains an explicit literature hypothesis here;
this module does not claim an independent proof of that limit or of the
classical bounded squared-singular-value test limit.
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

namespace NoncompactProfile

structure GaussianProfileReducedSources (p : NoncompactProfile) (W : ℕ → ℝ) : Prop where
  bbv : BBVComparisonInput
  ginibreLog : GinibreLogPotentialInput
  ginibreSquared : ClassicalGinibreSquaredTestInput
  coreSection4 : ∀ R : ℕ,
    (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)).ConcreteSection4Input W

theorem GaussianProfileReducedSources.toConcrete
    (p : NoncompactProfile) (W : ℕ → ℝ) (h : GaussianProfileReducedSources p W) :
    GaussianProfileConcreteSources p W where
  bbv := h.bbv
  bc12 := bc12_of_bbv_and_logPotential h.bbv h.ginibreLog
  ginibreSquared := h.ginibreSquared
  coreSection4 := h.coreSection4
  ginibreRaw := ae_of_all _ fun z => ginibre_raw_of_bc12
    (bc12_of_bbv_and_logPotential h.bbv h.ginibreLog)
    (fun n => n + 1) (tendsto_add_atTop_nat 1) z
  ginibreNegative := ae_of_all _ fun z => ⟨1 / 128, by norm_num,
    ginibre_negative_of_bbv h.bbv (fun n => n + 1) (tendsto_add_atTop_nat 1) z⟩
  ginibreSpectral := ginibre_spectral_of_bc12
    (bc12_of_bbv_and_logPotential h.bbv h.ginibreLog)

end NoncompactProfile
end CircularLawSection6
