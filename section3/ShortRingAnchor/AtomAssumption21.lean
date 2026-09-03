import ShortRingAnchor.CyclicSecondMoment
import ShortRingAnchor.NormalizedGinibre

/-!
# Assumption 2.1: atom moments and bounded-density alternatives

This file records the atom hypothesis used by Proposition 3.6 of the v3
manuscript.  The part used in the elementary upper-edge calculation is kept
separate: strong measurability, mean zero, unit second moment, and a finite
third absolute moment.  The real/complex bounded-density alternative is also
encoded faithfully, but no least-singular-value consequence is inferred from
it here.

The final two packages collect these moment assumptions for the supplied
short-ring and dense atom arrays.  They replace four repeated entrywise
hypotheses each and directly construct the corresponding
`CenteredMatrixRowSecondMomentInputs`.
-/

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-! ## The moment part of Assumption 2.1 -/

/-- The moment portion of Assumption 2.1 for a complex-valued atom.

`thirdMomentIntegrable` is the machine-checkable formulation of
`E ‖xi‖^3 < infinity`.  The manuscript's real-valued case is represented by
viewing the real atom in `Complex`; the density alternative below records
when this is the case. -/
structure AtomMomentAssumption21 (mu : Measure Omega)
    (atom : Omega -> Complex) : Prop where
  stronglyMeasurable : StronglyMeasurable atom
  centered : integral mu atom = 0
  unitSecondMoment : integral mu (fun sample => ‖atom sample‖ ^ 2) = 1
  thirdMomentIntegrable :
    Integrable (fun sample => ‖atom sample‖ ^ 3) mu

namespace AtomMomentAssumption21

variable {atom : Omega -> Complex}

/-- Assumption 2.1 in particular gives ordinary Borel measurability of the
atom. -/
theorem measurable (h : AtomMomentAssumption21 mu atom) : Measurable atom :=
  h.stronglyMeasurable.measurable

/-- On a probability space, the finite third absolute moment in Assumption
2.1 implies that the atom itself is Bochner integrable. -/
theorem integrable [IsProbabilityMeasure mu]
    (h : AtomMomentAssumption21 mu atom) : Integrable atom mu := by
  have hnorm : Integrable (fun sample => ‖atom sample‖ ^ (1 : Nat)) mu :=
    integrable_norm_pow_of_le
      h.stronglyMeasurable.aestronglyMeasurable (by omega)
        h.thirdMomentIntegrable
  exact (integrable_norm_iff
    h.stronglyMeasurable.aestronglyMeasurable).mp (by simpa using hnorm)

/-- On a probability space, the finite third absolute moment in Assumption
2.1 implies integrability of the squared norm.  This is the exact
integrability fact needed in the Hilbert--Schmidt computation (3.13). -/
theorem normSqIntegrable [IsProbabilityMeasure mu]
    (h : AtomMomentAssumption21 mu atom) :
    Integrable (fun sample => ‖atom sample‖ ^ 2) mu :=
  integrable_norm_pow_of_le
    h.stronglyMeasurable.aestronglyMeasurable (by omega)
      h.thirdMomentIntegrable

end AtomMomentAssumption21

/-! ## The bounded-density alternative in Assumption 2.1 -/

set_option autoImplicit false in
/-- A finite essential upper bound for a density of `nu` with respect to a
reference measure `lambda`.  This is only a record of a density hypothesis;
it does not assert any anti-concentration or least-singular-value theorem. -/
structure HasBoundedDensityWithRespectTo
    {E : Type*} [MeasurableSpace E]
    (nu lambda : Measure E) where
  density : E -> ENNReal
  densityAEMeasurable : AEMeasurable density lambda
  bound : ENNReal
  bound_lt_top : bound < (⊤ : ENNReal)
  density_le_bound : ∀ᵐ x ∂lambda, density x <= bound
  law_eq_withDensity : nu = lambda.withDensity density

/-- The two alternatives in Assumption 2.1:

* in the real case the complex atom is real almost surely and its real law
  has a bounded density with respect to one-dimensional Lebesgue measure;
* in the complex case its law has a bounded density with respect to planar
  Lebesgue measure on `Complex`.

No probabilistic consequence of either branch is postulated. -/
inductive AtomDensityAlternative21 (mu : Measure Omega)
    (atom : Omega -> Complex) : Prop
  | real
      (imaginaryPart_zero : ∀ᵐ sample ∂mu, (atom sample).im = 0)
      (boundedDensity : HasBoundedDensityWithRespectTo
        (Measure.map (fun sample => (atom sample).re) mu)
        (volume : Measure Real))
  | complex
      (boundedDensity : HasBoundedDensityWithRespectTo
        (Measure.map atom mu) (volume : Measure Complex))

/-- The complete Assumption 2.1 record: its moment part together with the
real/complex bounded-density alternative. -/
structure AtomAssumption21 (mu : Measure Omega)
    (atom : Omega -> Complex) : Prop
    extends AtomMomentAssumption21 mu atom where
  densityAlternative : AtomDensityAlternative21 mu atom

/-! ## Moment-copy packages for the two matrix models -/

/-- Assumption-2.1 moment data for every atom supplied to the cyclic
short-ring construction (3.1).

This package deliberately records only the marginal facts used in (3.13).
It neither asserts nor fabricates independence between copies. -/
structure RingEntryMomentCopies21
    {M W : Nat -> Nat} (mu : Measure Omega)
    (ringEntry : forall n,
      Omega -> Fin (M n) -> BandOffset (W n) -> Complex) : Prop where
  atom : forall n i s,
    AtomMomentAssumption21 mu (fun sample => ringEntry n sample i s)

namespace RingEntryMomentCopies21

/-- A ring-entry Assumption-2.1 moment package directly supplies the
centered row-second-moment input for the genuine cyclic model. -/
theorem centeredMatrixRowSecondMomentInputs
    [IsProbabilityMeasure mu]
    {M W : Nat -> Nat} {c0 C0 : Real}
    (weights : forall n, AdmissibleWeights (W n) c0 C0)
    (hfit : forall n, 2 * W n + 1 <= M n)
    (ringEntry : forall n,
      Omega -> Fin (M n) -> BandOffset (W n) -> Complex)
    (hcopies : RingEntryMomentCopies21 mu ringEntry) :
    CenteredMatrixRowSecondMomentInputs mu
      (fun n sample =>
        cyclicShortRingRandomMatrix (weights n) (hfit n)
          (ringEntry n) sample)
      1 := by
  exact centeredMatrixRowSecondMomentInputs_cyclicShortRing
    weights hfit ringEntry
    (fun n i s => (hcopies.atom n i s).integrable)
    (fun n i s => (hcopies.atom n i s).normSqIntegrable)
    (fun n i s => (hcopies.atom n i s).centered)
    (fun n i s => (hcopies.atom n i s).unitSecondMoment)

end RingEntryMomentCopies21

/-- Assumption-2.1 moment data for every unnormalized atom supplied to the
dense comparison matrix.  As above, independence is not part of this
upper-edge-only package. -/
structure DenseAtomMomentCopies21
    {M : Nat -> Nat} (mu : Measure Omega)
    (denseAtom : forall n,
      Omega -> Fin (M n) -> Fin (M n) -> Complex) : Prop where
  atom : forall n i j,
    AtomMomentAssumption21 mu (fun sample => denseAtom n sample i j)

namespace DenseAtomMomentCopies21

/-- A dense-atom Assumption-2.1 moment package directly supplies the
centered row-second-moment input after division by `sqrt M`. -/
theorem centeredMatrixRowSecondMomentInputs
    [IsProbabilityMeasure mu]
    {M : Nat -> Nat} [forall n, Nonempty (Fin (M n))]
    (denseAtom : forall n,
      Omega -> Fin (M n) -> Fin (M n) -> Complex)
    (hcopies : DenseAtomMomentCopies21 mu denseAtom) :
    CenteredMatrixRowSecondMomentInputs mu
      (normalizedDenseMatrixProcess denseAtom) 1 := by
  exact normalizedDenseMatrixProcess_centeredRowSecondMomentInputs
    denseAtom
    (fun n i j => (hcopies.atom n i j).integrable)
    (fun n i j => (hcopies.atom n i j).normSqIntegrable)
    (fun n i j => (hcopies.atom n i j).centered)
    (fun n i j => (hcopies.atom n i j).unitSecondMoment)

end DenseAtomMomentCopies21

end ShortRingAnchor
