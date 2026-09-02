import CircularLawSections56
import Lean.Util.CollectAxioms

/-! # Exhaustive transitive axiom audit for the public Section 5 namespace

This executable elaboration-time check complements the selected-entry
`#print axioms` audit. It rejects any dependency other than Lean's three usual
classical foundations, including `sorryAx` and user-declared mathematical axioms.
It checks definitions as well as theorems, so a hidden output/input abbreviation
cannot evade the audit. Ordinary theorem hypotheses are still ordinary inputs;
this audit does not purport to prove the permitted Section 3/4 hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut theoremCount : Nat := 0
  for (name, info) in env.constants do
    if (`CircularLawSections56.Section5).isPrefixOf name then
      checked := checked + 1
      if info.isTheorem then
        theoremCount := theoremCount + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Section 5 axiom audit failed: {name} depends on {axiomName}"
  if checked == 0 then
    throwError "Section 5 axiom audit did not find any declarations"
  logInfo m!"Section 5 exhaustive axiom audit PASSED: {checked} declarations, {theoremCount} theorems. Allowed foundations only: propext, Classical.choice, Quot.sound."
