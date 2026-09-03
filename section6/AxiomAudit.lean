import CircularLawSection6
import Lean.Util.CollectAxioms

/-! Transitive audit of every declaration in the new Section 6 namespace.
Ordinary hypotheses are not discharged by this audit. -/

set_option autoImplicit false
set_option maxHeartbeats 0

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut theoremCount : Nat := 0
  for (name, info) in env.constants do
    if (`CircularLawSection6).isPrefixOf name then
      checked := checked + 1
      if info.isTheorem then
        theoremCount := theoremCount + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Section 6 axiom audit failed: {name} depends on {axiomName}"
  if checked == 0 then
    throwError "Section 6 axiom audit found no declarations"
  logInfo m!"Section 6 axiom audit PASSED: {checked} declarations, {theoremCount} theorems."

/-! Check only the newly added Section 3-to-5 adapters, not the already
verified Section 5 library again. Imported proof dependencies are followed. -/
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : Array Name := #[
    `CircularLawSections56.Section5.PublishedSection3Model,
    `CircularLawSections56.Section5.PublishedSection3Anchor,
    `CircularLawSections56.Section5.PublishedSection3AnchorsTri,
    `CircularLawSections56.Section5.literal_canonical_profile_endpoint_of_published_section3,
    `CircularLawSections56.Section5.section3_finEquiv_eq_natCast,
    `CircularLawSections56.Section5.section3_cyclicColumn_finEquiv,
    `CircularLawSections56.Section5.paperSection3Weights,
    `CircularLawSections56.Section5.paperSection3Atoms,
    `CircularLawSections56.Section5.literalIndicatorMatrix_eq_section3,
    `CircularLawSections56.Section5.literalPhysicalLogPotential_eq_section3]
  let mut checked := 0
  for (name, _) in env.constants do
    if prefixes.any (fun prefix => prefix.isPrefixOf name) then
      checked := checked + 1
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "Section 3 integration audit failed: {name} depends on {axiomName}"
  if checked == 0 then
    throwError "Section 3 integration audit found no declarations"
  logInfo m!"Section 3 integration axiom audit PASSED: {checked} adapter declarations."
