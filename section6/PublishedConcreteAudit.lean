import CircularLawSection6.PublishedConcreteGaussianProfile
import Lean.Util.CollectAxioms

/-! Only the new concrete Section 6 sources and their proof dependencies. -/
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : Array Name := #[
    `CircularLawSection6.ClassicalGinibreSquaredTestInput,
    `CircularLawSection6.ginibreSquaredTestInput_reindex,
    `CircularLawSection6.publishedLocal_spectralParameter_im_pos,
    `CircularLawSection6.CoreRadiusBounds.publishedLocalInput_of_concrete_literature,
    `CircularLawSection6.CoreRadiusBounds.canonicalCoreSection3Input_of_concrete_literature,
    `CircularLawSection6.CoreRadiusBounds.ConcreteSection4Input,
    `CircularLawSection6.NoncompactProfile.GaussianProfileConcreteSources,
    `CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law_of_concrete_sources]
  let mut checked : Nat := 0
  for (name, _) in env.constants do
    if prefixes.any (fun p => p.isPrefixOf name) then
      checked := checked + 1
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "Concrete Section 6 audit failed: {name} depends on {axiomName}"
  if checked == 0 then
    throwError "Concrete Section 6 audit is empty"
  logInfo m!"Concrete Section 6 interface axiom audit PASSED: {checked} declarations."

#check CircularLawSection6.ginibreSquaredTestInput_reindex
#check CircularLawSection6.CoreRadiusBounds.ConcreteSection4Input.toSection34
#check CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law_of_concrete_sources
