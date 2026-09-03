import CircularLawSection6.BBVOnlyProfileEndpoint
import CircularLawSection6.GinibreFiniteFormulaSources

#print axioms CircularLawSection6.verifiedGinibreFiniteFormulaInput
#print axioms CircularLawSection6.verifiedGinibreLogPotentialInput
#print axioms CircularLawSection6.ginibre_raw_of_sequence_log_limit
#print axioms CircularLawSection6.ginibre_raw_verified
#print axioms CircularLawSection6.ginibre_spectral_of_raw_limit
#print axioms CircularLawSection6.ginibre_spectral_verified
#print axioms CircularLawSection6.NoncompactProfile.GaussianProfileConcreteSources.bc12
#print axioms CircularLawSection6.NoncompactProfile.GaussianProfileConcreteSources.ginibreRaw
#print axioms CircularLawSection6.NoncompactProfile.GaussianProfileConcreteSources.ginibreNegative
#print axioms CircularLawSection6.NoncompactProfile.GaussianProfileConcreteSources.ginibreSpectral
#print axioms CircularLawSection6.NoncompactProfile.GaussianProfileReducedSources.toConcrete
#print axioms CircularLawSection6.CoreRadiusBounds.ConcreteSection4Input.toSection34
#print axioms CircularLawSection6.CoreRadiusBounds.ConcreteSection4Input.logPotential
#print axioms CircularLawSection6.DenseProfile.actualMatrix_conclusion
#print axioms CircularLawSection6.DenseProfile.profile_conclusion
#print axioms CircularLawSection6.DenseProfile.profile_raw_limit
#print axioms CircularLawSection6.NoncompactProfile.dense_profile_spectral_limit_of_section3
#print axioms CircularLawSection6.NoncompactProfile.sparse_profile_probability_of_bbv_section5
#print axioms CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law_of_bbv_core_sources
#print axioms CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law_of_bbv_sources

-- Regression: no projection/correlation or log-potential premise is needed.
example : CircularLawSection6.GinibreFiniteFormulaInput :=
  CircularLawSection6.verifiedGinibreFiniteFormulaInput

example : CircularLawSection6.GinibreLogPotentialInput :=
  CircularLawSection6.verifiedGinibreLogPotentialInput

-- Kernel-checked record constructors: the preferred public sources have
-- only BBV and Section 4 pressure, not hidden Gaussian estimate fields.
open CircularLawSection6 CircularLawSection6.NoncompactProfile
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput)

example (p : NoncompactProfile) (W : ℕ → ℝ) (hBBV : BBVComparisonInput)
    (h4 : ∀ R : ℕ,
      (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)).ConcreteSection4Input W) :
    GaussianProfileBBVCoreSources p W := ⟨hBBV, h4⟩

example (p : NoncompactProfile) (W : ℕ → ℝ) (hBBV : BBVComparisonInput)
    (h4 : ∀ R : ℕ,
      (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)).ConcreteSection4Input W) :
    GaussianProfileBBVSources p W := ⟨hBBV, h4⟩

#print CircularLawSection6.NoncompactProfile.GaussianProfileBBVCoreSources
#print CircularLawSection6.NoncompactProfile.GaussianProfileBBVSources
#print CircularLawSection6.NoncompactProfile.GaussianProfileConcreteSources
#print CircularLawSection6.NoncompactProfile.GaussianProfileReducedSources
#check @CircularLawSection6.DenseProfile.profile_conclusion
#check @CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law_of_bbv_sources
#check @CircularLawSection6.ginibre_raw_verified
#check @CircularLawSection6.ginibre_spectral_verified
