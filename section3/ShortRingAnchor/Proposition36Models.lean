import ShortRingAnchor.Proposition36Source
import ShortRingAnchor.AtomAssumption21
import ShortRingAnchor.HermitizationCounting
import ShortRingAnchor.DensityNonsingularity

/-!
# Proposition 3.6 for the actual short-ring and dense comparison models

This file specializes `proposition36_of_source_scales` to the two matrix
processes used in the v3 manuscript:

* `H` is exactly the cyclic short-ring model (3.1), constructed from the
  profile `weights` and the atom copies `ringEntry`;
* `G` is the normalized dense comparison process, whose entries are
  `denseAtom / sqrt M`.

The upper-edge second-moment inputs are no longer theorem parameters here.
The moment part of Assumption 2.1 is bundled in two atom-copy packages; its
finite third moment is used to derive the required first- and second-moment
integrability before the cyclic and dense row computations are applied.
The genuinely random-matrix conclusions used from Theorem 3.1, Proposition
3.4, Lemma 3.5, and BC12 remain explicit hypotheses.
-/

open Filter Set
open scoped ENNReal Topology

noncomputable section

namespace ShortRingAnchor

open MeasureTheory ProbabilityTheory

/-- **Proposition 3.6 (v3), specialized to the genuine matrix models.**

The conclusion is formula (3.8) for the cyclic matrix (3.1).  All scale
bookkeeping from (3.7) and (3.9)--(3.14), the determinant/singular-value
translation, and the Hilbert--Schmidt calculation in (3.13) are discharged
inside Lean.  The hypotheses named `hLSV`, `hCount`, `hBulk`,
`hBC12Negative`, and `hBC12Full` are the remaining cited random-matrix
inputs; they are stated directly for the concrete processes below rather
than for arbitrary matrices.  Dense nonsingularity is proved internally
from the explicit independence and real/complex density assumptions, using
the fully proved polynomial-zero-set theorem.
-/
theorem proposition36_cyclicShortRing_of_source_scales
    {Omega : Type*} [MeasurableSpace Omega]
    {M W : Nat -> Nat} [forall n, Nonempty (Fin (M n))]
    {c0 C0 : Real}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (weights : forall n, AdmissibleWeights (W n) c0 C0)
    (hfit : forall n, 2 * W n + 1 <= M n)
    (ringEntry : forall n,
      Omega -> Fin (M n) -> BandOffset (W n) -> Complex)
    (denseAtom : forall n,
      Omega -> Fin (M n) -> Fin (M n) -> Complex)
    (z : Complex)
    (omega chi kappa tau K C35 p : Real)
    (R zeta : Nat -> Real)
    (homega : 0 < omega ∧ omega < 1 / 9)
    (hparam : HardEdgeAdmissible
      (v3BandwidthExponent omega) chi kappa tau)
    (hMpos : forall n, 0 < M n)
    (hM : Tendsto M atTop atTop)
    (hW : Tendsto W atTop atTop)
    (hband : forall n,
      (M n : Real) ^ (v3BandwidthExponent omega) <= (W n : Real))
    (hKdom : C0 ^ (1 / 8 : Real) <= K)
    (hC35 : 0 <= C35)
    (hRtop : Tendsto R atTop atTop)
    (hR : forall r, Real.sqrt (Real.exp 1) < R r)
    (hzeta : forall r, 0 < zeta r)
    (hDenseIndependent : ∀ n, iIndepFun
      (fun (ij : Fin (M n) × Fin (M n)) sample =>
        denseAtom n sample ij.1 ij.2) mu)
    (hDenseDensity : ∀ n i j,
      AtomDensityAlternative21 mu (fun sample => denseAtom n sample i j))
    (goodLSV goodCount : Nat -> Set Omega)
    (hLSV : Theorem31MinimumSingularValueInput hMpos mu
      (fun n sample =>
        cyclicShortRingRandomMatrix (weights n) (hfit n)
          (ringEntry n) sample)
      z (sourceHardEdgeScale M W kappa) goodLSV)
    (hCount : HermitizationAllCutoffsCountingInput mu
      (fun n sample =>
        cyclicShortRingRandomMatrix (weights n) (hfit n)
          (ringEntry n) sample)
      z
      (fun n => manuscriptHardEdgeCutoff (weights n) (M n) tau)
      (fun _ => C35) goodCount)
    (hBulk : forall r, Lemma35LocalBulkComparisonInput mu
      (shiftedSingularValueProcess
        (fun n sample =>
          cyclicShortRingRandomMatrix (weights n) (hfit n)
            (ringEntry n) sample) z)
      (shiftedSingularValueProcess
        (normalizedDenseMatrixProcess denseAtom) z)
      (R r) (sourceBulkRate M zeta r))
    (hp : 0 < p)
    (hBC12Negative : BC12GinibreNegativeMomentTightness mu p
      (shiftedSingularValueProcess
        (normalizedDenseMatrixProcess denseAtom) z))
    (hBC12Full : ConvergesInProbability mu
      (fun n sample =>
        normalizedShiftLogDet
          (normalizedDenseMatrixProcess denseAtom n sample) z)
      (circularLogPotential z))
    (hRingCopies : RingEntryMomentCopies21 mu ringEntry)
    (hDenseCopies : DenseAtomMomentCopies21 mu denseAtom) :
    Proposition36SequenceConclusion mu M
      (fun n sample =>
        cyclicShortRingRandomMatrix (weights n) (hfit n)
          (ringEntry n) sample) z := by
  have hGnonsingular : ShiftedNonsingularInProbability mu
      (normalizedDenseMatrixProcess denseAtom) z :=
    normalizedDense_shiftedNonsingularInProbability_of_independent_density
      denseAtom hMpos
      (fun n i j => (hDenseCopies.atom n i j).measurable.aemeasurable)
      hDenseIndependent hDenseDensity z
  have hHSecondMoment : CenteredMatrixRowSecondMomentInputs mu
      (fun n sample =>
        cyclicShortRingRandomMatrix (weights n) (hfit n)
          (ringEntry n) sample) 1 :=
    hRingCopies.centeredMatrixRowSecondMomentInputs weights hfit ringEntry
  have hGSecondMoment : CenteredMatrixRowSecondMomentInputs mu
      (normalizedDenseMatrixProcess denseAtom) 1 :=
    hDenseCopies.centeredMatrixRowSecondMomentInputs denseAtom
  have hCountSingular : Proposition34AllCutoffsInput mu
      (shiftedSingularValueProcess
        (fun n sample =>
          cyclicShortRingRandomMatrix (weights n) (hfit n)
            (ringEntry n) sample) z)
      (fun n => manuscriptHardEdgeCutoff (weights n) (M n) tau)
      (fun _ => 2 * C35) goodCount :=
    proposition34AllCutoffsInput_of_hermitization
      (fun n sample =>
        cyclicShortRingRandomMatrix (weights n) (hfit n)
          (ringEntry n) sample)
      z (fun n => manuscriptHardEdgeCutoff (weights n) (M n) tau)
      (fun _ => C35) goodCount hCount
  exact proposition36_of_source_scales weights
    (fun n sample =>
      cyclicShortRingRandomMatrix (weights n) (hfit n)
        (ringEntry n) sample)
    (normalizedDenseMatrixProcess denseAtom) z
    omega chi kappa tau K (2 * C35) p 1 1 R zeta homega hparam hMpos hM hW
    hband hKdom (mul_nonneg (by norm_num) hC35) hRtop hR hzeta
    hGnonsingular goodLSV goodCount hLSV hCountSingular hBulk hp
    hBC12Negative hBC12Full
    hHSecondMoment hGSecondMoment

end ShortRingAnchor
