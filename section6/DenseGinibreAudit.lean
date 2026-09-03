import CircularLawSection6.DenseProfileLSV
import CircularLawSection6.DenseProfileScales
import CircularLawSection6.GinibreGaussianLaw
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
    `ShortRingAnchor.BC12.normalizedGinibre,
    `ShortRingAnchor.BC12.negativeMomentTightness,
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
