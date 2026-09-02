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
