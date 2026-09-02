import ShortRingAnchor.ExternalInputs

/-!
# Removing finite initial segments from literature inputs

The manuscript routinely writes estimates "with probability `1-o(1)`" and
uses asymptotic cutoff comparisons.  The structures in `ExternalInputs.lean`
state their pointwise conclusions for every sequence index, so this file
checks the harmless finite-prefix adapter explicitly instead of silently
discarding early indices.
-/

open Filter Set
open scoped ENNReal Topology

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

/-- If the least-singular-value conclusion is valid only eventually, shrink
the finitely many exceptional good events to the empty set.  The resulting
good events satisfy the all-index interface and retain failure probability
`o(1)`. -/
theorem theorem31LeastSingularValueInput_of_eventually
    {Omega : Type*} [MeasurableSpace Omega]
    {I : Nat -> Type*} [forall n, Fintype (I n)]
    {mu : Measure Omega}
    {singularValue : forall n, Omega -> I n -> Real}
    {L : Nat -> Real} {good : Nat -> Set Omega}
    (hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0))
    (hlower : ∀ᶠ n in atTop, forall omega, omega ∈ good n -> forall i,
      Real.exp (-(L n)) <= singularValue n omega i) :
    exists good' : Nat -> Set Omega,
      Theorem31LeastSingularValueInput mu singularValue L good' := by
  classical
  let valid : Nat -> Prop := fun n =>
    forall omega, omega ∈ good n -> forall i,
      Real.exp (-(L n)) <= singularValue n omega i
  let good' : Nat -> Set Omega := fun n => if valid n then good n else ∅
  refine ⟨good', ?_⟩
  constructor
  · apply hbad.congr'
    filter_upwards [hlower] with n hn
    have hvalid : valid n := hn
    simp [good', hvalid]
  · intro n omega homega i
    by_cases hn : valid n
    · exact hn omega (by simpa [good', hn] using homega) i
    · simp [good', hn] at homega

/-- Eventual form of the Proposition 3.4 specialization.  This is the
adapter needed when an asymptotic cutoff comparison, such as
`manuscriptHardEdgeCutoff_le_sourceCutoff_eventually`, is used to choose the
interval. -/
theorem proposition34MesoscopicCountingInput_of_eventually
    {Omega : Type*} [MeasurableSpace Omega]
    {I : Nat -> Type*} [forall n, Fintype (I n)]
    {mu : Measure Omega}
    {singularValue : forall n, Omega -> I n -> Real}
    {a C : Nat -> Real} {good : Nat -> Set Omega}
    (hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0))
    (hcount : ∀ᶠ n in atTop, forall omega, omega ∈ good n ->
      ((smallSingularValueIndices (singularValue n omega) (a n)).card : Real) <=
        C n * (Fintype.card (I n) : Real) * a n) :
    exists good' : Nat -> Set Omega,
      Proposition34MesoscopicCountingInput mu singularValue a C good' := by
  classical
  let valid : Nat -> Prop := fun n =>
    forall omega, omega ∈ good n ->
      ((smallSingularValueIndices (singularValue n omega) (a n)).card : Real) <=
        C n * (Fintype.card (I n) : Real) * a n
  let good' : Nat -> Set Omega := fun n => if valid n then good n else ∅
  refine ⟨good', ?_⟩
  constructor
  · apply hbad.congr'
    filter_upwards [hcount] with n hn
    have hvalid : valid n := hn
    simp [good', hvalid]
  · intro n omega homega
    by_cases hn : valid n
    · exact hn omega (by simpa [good', hn] using homega)
    · simp [good', hn] at homega

/-- A source-shaped version of the Proposition 3.4 consequence: on one
high-probability event, every radius above `threshold n` has the stated
linear counting bound.  This is still an explicit literature hypothesis,
not a proved random-matrix assertion. -/
structure Proposition34AllCutoffsInput
    {Omega : Type*} [MeasurableSpace Omega]
    {I : Nat -> Type*} [forall n, Fintype (I n)]
    (mu : Measure Omega)
    (singularValue : forall n, Omega -> I n -> Real)
    (threshold C : Nat -> Real) (good : Nat -> Set Omega) : Prop where
  badProbability : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0)
  count : forall n omega, omega ∈ good n -> forall r,
    threshold n <= r ->
      ((smallSingularValueIndices (singularValue n omega) r).card : Real) <=
        C n * (Fintype.card (I n) : Real) * r

/-- Specialize an all-cutoff Proposition 3.4 input at a cutoff which
eventually dominates the theorem's minimum scale.  The finite-prefix repair
is performed by `proposition34MesoscopicCountingInput_of_eventually`. -/
theorem Proposition34AllCutoffsInput.specialize_eventually
    {Omega : Type*} [MeasurableSpace Omega]
    {I : Nat -> Type*} [forall n, Fintype (I n)]
    {mu : Measure Omega}
    {singularValue : forall n, Omega -> I n -> Real}
    {threshold a C : Nat -> Real} {good : Nat -> Set Omega}
    (hInput : Proposition34AllCutoffsInput mu singularValue threshold C good)
    (hdom : ∀ᶠ n in atTop, threshold n <= a n) :
    exists good' : Nat -> Set Omega,
      Proposition34MesoscopicCountingInput mu singularValue a C good' := by
  apply proposition34MesoscopicCountingInput_of_eventually
    hInput.badProbability
  filter_upwards [hdom] with n hn
  intro omega homega
  exact hInput.count n omega homega (a n) hn

end ShortRingAnchor
