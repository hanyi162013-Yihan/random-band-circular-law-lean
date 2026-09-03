import CircularLawSection6.GinibreFiniteFormulaSources
import Lean.Util.CollectAxioms

/-! Audit the new dense-model and actual Ginibre source adapters, with their
transitive proof dependencies. It does not replace the full Section 6 audit. -/
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : Array Name := #[
    `CircularLawSection6.DenseProfile,
    `CircularLawSection6.GinibreReferenceSources,
    `CircularLawSection6.ginibre_raw_of_bc12,
    `CircularLawSection6.ginibre_spectral_of_bc12,
    `CircularLawSection6.ginibre_negative_of_bbv,
    `CircularLawSection6.singularValue_lipschitz,
    `CircularLawSection6.measurable_matrixNegativeMoment,
    `CircularLawSection6.NoncompactProfile.GaussianProfileReducedSources,
    `CircularLawSection6.NoncompactProfile.dense_profile_spectral_limit_of_section3,
    `CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law_without_Han,
    `CircularLawSection6.bc12_of_bbv_and_logPotential,
    `CircularLawSection6.ginibreLogPotential_of_finiteFormulas,
    `CircularLawSection6.bc12_of_bbv_and_finiteFormulas,
    `ShortRingAnchor.BC12.normalizedGinibre_lower_bad_tendsto_zero,
    `ShortRingAnchor.BC12.negativeMomentTightness_of_ginibreLaw_and_v3,
    `ShortRingAnchor.BC12.negativeMomentTightness_normalizedDenseMatrixProcess,
    `ShortRingAnchor.BC12.gaussian_smallBall_normalization_le]
  let mut checked : Nat := 0
  for (name, _) in env.constants do
    if prefixes.any (fun p => p.isPrefixOf name) then
      checked := checked + 1
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "Dense/Ginibre audit failed: {name} depends on {axiomName}"
  if checked == 0 then
    throwError "Dense/Ginibre audit is empty"
  logInfo m!"Dense/Ginibre source axiom audit PASSED: {checked} declarations."

#check CircularLawSection6.DenseProfile.actualMatrix_minimumInput
#check CircularLawSection6.ginibre_raw_of_bc12
#check CircularLawSection6.ginibre_spectral_of_bc12
#check CircularLawSection6.GinibreReferenceSources.ginibreOnSequence_hasLaw
#check CircularLawSection6.GinibreReferenceSources.ginibre_negative_on_sequence_of_bbv
#check CircularLawSection6.ginibre_negative_of_bbv
#check CircularLawSection6.NoncompactProfile.GaussianProfileReducedSources.toConcrete
#check CircularLawSection6.DenseProfile.actualMatrix_conclusion
#check CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law_without_Han
#check CircularLawSection6.ginibreLogPotential_of_finiteFormulas
