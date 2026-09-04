import CircularLawSections56.Section5.PublishedSection3ConcreteEndpoint
import Lean.Util.CollectAxioms

/-! Narrow audit: new concrete Section 3-to-5 interface and its actual proof dependencies. -/
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants do
    if (`CircularLawSections56.Section5.PublishedSection3Concrete).isPrefixOf name then
      checked := checked + 1
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "Concrete Section 5 interface audit failed: {name} depends on {axiomName}"
  if checked == 0 then
    throwError "Concrete Section 5 interface audit is empty"
  logInfo m!"Concrete Section 5 interface axiom audit PASSED: {checked} declarations."

open MeasureTheory ShortRingAnchor
open CircularLawSections56.Section5.PublishedSection3Concrete

noncomputable example :
    HasBoundedDensityWithRespectTo (Measure.map id circularComplexGaussian) (volume : Measure ℂ) :=
  gaussianDensity

example (ν : Measure ℂ) [IsProbabilityMeasure ν] (L : ℕ) :
    MeasurePreserving (samples L) (sampleLaw ν) (CircularLawSection4.iidMeasure ν L) :=
  samples_measurePreserving ν L

example (L K : ℕ) (h : L ≤ K) (ω : Sample) :
    (fun i => samples K ω (Fin.castLE h i)) = samples L ω :=
  samples_prefix L K h ω

#check ringPotential_limit
#print axioms ginibreOnSequence_hasLaw
#print axioms ginibre_negative_on_sequence_of_bbv
#print axioms ginibre_logPotential_on_sequence
#print axioms provedGinibreInput
#check @provedGinibreInput
#check calibrationRaw_prefix_normalization
#check literal_anchors
#check indicator_complex_full_of_published_literature
#check indicator_real_full_of_published_literature
