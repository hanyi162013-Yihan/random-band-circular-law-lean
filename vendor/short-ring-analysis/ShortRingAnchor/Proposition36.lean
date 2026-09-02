import ShortRingAnchor.ExternalInputs
import ShortRingAnchor.ParameterArithmetic
import ShortRingAnchor.SingularValues
import ShortRingAnchor.HighProbabilityTransfer

/-!
# Proposition 3.6: checked proof from explicit inputs

The main theorem in this file starts at exactly the level of the inputs cited
in the manuscript proof.  Theorem 3.1, Proposition 3.4 / Lemma 3.5, and the
two BC12 conclusions are ordinary theorem parameters.  All deductions from
those parameters through formulas (3.10)--(3.14), including the final
iterated-limit argument, are checked by Lean.
-/

open Filter Set
open scoped ENNReal Topology

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

/-- **Proposition 3.6 in singular-value form.**

This theorem exposes every genuine literature input and proves all remaining
steps of the source proof.  In the application, `h` is the singular-value
family of `H_{M,W}-zI`, `g` is that of normalized circular Ginibre,
`a=a_M`, and `limit=U_circ(z)`.
-/
theorem proposition36_singularValue_form_of_upperCorrections
    {Omega : Type*} [MeasurableSpace Omega]
    {I J : Nat -> Type*}
    [forall n, Fintype (I n)] [forall n, Nonempty (I n)]
    [forall n, Fintype (J n)] [forall n, Nonempty (J n)]
    {mu : Measure Omega}
    (h : forall n, Omega -> I n -> Real)
    (g : forall n, Omega -> J n -> Real)
    (a C L : Nat -> Real) (R : Nat -> Real)
    (bulkRate : Nat -> Nat -> Real)
    (p limit : Real)
    (ha : forall n, 0 < a n)
    (ha1 : forall n, a n <= 1)
    (haZero : Tendsto a atTop (nhds 0))
    (hL : forall n, 0 <= L n)
    (hh : forall n omega i, 0 < h n omega i)
    (hg : forall n omega j, 0 < g n omega j)
    (goodLSV goodCount : Nat -> Set Omega)
    (hLSV : Theorem31LeastSingularValueInput mu h L goodLSV)
    (hCount : Proposition34MesoscopicCountingInput mu h a C goodCount)
    (hHardRate : Tendsto (fun n => C n * a n * L n) atTop (nhds 0))
    (hBulk : forall r,
      Lemma35LocalBulkComparisonInput mu h g (R r) (bulkRate r))
    (hBulkScale : forall r, Tendsto
      (fun n => bulkRate r n * (Real.log (R r) - Real.log (a n)))
      atTop (nhds 0))
    (hp : 0 < p)
    (hBC12Negative : BC12GinibreNegativeMomentTightness mu p g)
    (hBC12Full : BC12GinibreFullLogInput mu g limit)
    (hR : forall r, Real.sqrt (Real.exp 1) < R r)
    (hUpper : UpperCorrectionsUniformlyNegligible mu h g R) :
    ConvergesInProbability mu
      (fun n omega => empiricalLog (h n omega)) limit := by
  have hsqrtOne : (1 : Real) < Real.sqrt (Real.exp 1) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_lt_sqrt (by norm_num)
    simp
  have haR : forall r n, a n <= R r := by
    intro r n
    exact (ha1 n).trans (hsqrtOne.le.trans (hR r).le)

  -- Formula (3.10): intersect the two cited good events, then apply the
  -- completely deterministic hard-edge sum bound.
  let good : Nat -> Set Omega := fun n => goodLSV n ∩ goodCount n
  have hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0) := by
    exact hardEdgeIntersection_badProbability
      hLSV.badProbability hCount.badProbability
  have hHardMass : ConvergesInProbability mu
      (fun n omega => normalizedSmallLogMass (h n omega) (a n)) 0 := by
    apply normalizedSmallLogMass_convergesInProbability_zero
      (good := good) ha1 hL
    · intro n omega homega i
      exact hLSV.lower n omega homega.1 i
    · intro n omega homega
      exact hCount.count n omega homega.2
    · exact hbad
    · exact hHardRate
  have hHardLower : ConvergesInProbability mu
      (fun n omega => empiricalLowerLogCorrection (a n) (h n omega)) 0 :=
    empiricalLowerLogCorrection_convergesInProbability_of_smallLogMass
      ha ha1 hh hHardMass

  -- Formula (3.14), with BC12 appearing only through its named negative
  -- moment tightness premise.
  have hGinibreMass : ConvergesInProbability mu
      (fun n omega => normalizedSmallLogMass (g n omega) (a n)) 0 :=
    ginibreSmallLogMass_convergesInProbability_zero
      hp ha ha1 haZero hg hBC12Negative
  have hGinibreLower : ConvergesInProbability mu
      (fun n omega => empiricalLowerLogCorrection (a n) (g n omega)) 0 :=
    empiricalLowerLogCorrection_convergesInProbability_of_smallLogMass
      ha ha1 hg hGinibreMass

  -- Formulas (3.11)--(3.12): the CDF comparison is external, while the
  -- integration-by-parts bound and its `O_P * o(1)` consequence are internal.
  have hBulkLog : forall r, ConvergesInProbability mu
      (fun n omega =>
        empiricalClippedLog (a n) (R r) (fun i => h n omega i ^ 2) -
          empiricalClippedLog (a n) (R r) (fun j => g n omega j ^ 2)) 0 := by
    intro r
    exact bulkClippedLog_convergesInProbability_zero
      ha (haR r) (hBulk r) (hBulkScale r)

  exact empiricalLog_convergesInProbability_of_truncations
    ha haR hh hg hBC12Full hBulkLog hHardLower hGinibreLower hUpper

/-- **Proposition 3.6 in singular-value form, with formula (3.13) derived
from second moments.**

This is the source-facing version of
`proposition36_singularValue_form_of_upperCorrections`: the elementary
second-moment package is converted internally into the uniform upper-edge
correction estimate. -/
theorem proposition36_singularValue_form
    {Omega : Type*} [MeasurableSpace Omega]
    {I J : Nat -> Type*}
    [forall n, Fintype (I n)] [forall n, Nonempty (I n)]
    [forall n, Fintype (J n)] [forall n, Nonempty (J n)]
    {mu : Measure Omega}
    (h : forall n, Omega -> I n -> Real)
    (g : forall n, Omega -> J n -> Real)
    (a C L : Nat -> Real) (R : Nat -> Real)
    (bulkRate : Nat -> Nat -> Real)
    (p limit CH CG : Real)
    (ha : forall n, 0 < a n)
    (ha1 : forall n, a n <= 1)
    (haZero : Tendsto a atTop (nhds 0))
    (hL : forall n, 0 <= L n)
    (hh : forall n omega i, 0 < h n omega i)
    (hg : forall n omega j, 0 < g n omega j)
    (goodLSV goodCount : Nat -> Set Omega)
    (hLSV : Theorem31LeastSingularValueInput mu h L goodLSV)
    (hCount : Proposition34MesoscopicCountingInput mu h a C goodCount)
    (hHardRate : Tendsto (fun n => C n * a n * L n) atTop (nhds 0))
    (hBulk : forall r,
      Lemma35LocalBulkComparisonInput mu h g (R r) (bulkRate r))
    (hBulkScale : forall r, Tendsto
      (fun n => bulkRate r n * (Real.log (R r) - Real.log (a n)))
      atTop (nhds 0))
    (hp : 0 < p)
    (hBC12Negative : BC12GinibreNegativeMomentTightness mu p g)
    (hBC12Full : BC12GinibreFullLogInput mu g limit)
    (hRtop : Tendsto R atTop atTop)
    (hR : forall r, Real.sqrt (Real.exp 1) < R r)
    (hUpperMoments : UpperSecondMomentInputs mu h g CH CG) :
    ConvergesInProbability mu
      (fun n omega => empiricalLog (h n omega)) limit := by
  have hUpper : UpperCorrectionsUniformlyNegligible mu h g R :=
    upperCorrectionsUniformlyNegligible_of_secondMomentBounds
      hRtop hR hUpperMoments.CH_nonneg hUpperMoments.CG_nonneg
      hUpperMoments.h_integrable hUpperMoments.g_integrable
      hUpperMoments.h_mean hUpperMoments.g_mean
  exact proposition36_singularValue_form_of_upperCorrections
    h g a C L R bulkRate p limit ha ha1 haZero hL hh hg
    goodLSV goodCount hLSV hCount hHardRate hBulk hBulkScale hp
    hBC12Negative hBC12Full hR hUpper

/-- **Matrix / determinant form of Proposition 3.6.**

This is the source-facing wrapper around `proposition36_singularValue_form`.
The determinant--singular-value identity and strict positivity of singular
values are proved in `SingularValues.lean`; neither is an external input.
The pointwise nonsingularity premises select versions of the two ensembles
on their full-probability nonsingular sets.
-/
theorem proposition36_matrix_form
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} [forall n, Nonempty (Fin (M n))]
    {mu : Measure Omega}
    (H G : forall n,
      Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ)
    (a C L : Nat -> Real) (R : Nat -> Real)
    (bulkRate : Nat -> Nat -> Real)
    (p CH CG : Real)
    (ha : forall n, 0 < a n)
    (ha1 : forall n, a n <= 1)
    (haZero : Tendsto a atTop (nhds 0))
    (hL : forall n, 0 <= L n)
    (hHdet : forall n omega,
      (H n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (hGdet : forall n omega,
      (G n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (goodLSV goodCount : Nat -> Set Omega)
    (hLSV : Theorem31LeastSingularValueInput mu
      (shiftedSingularValueProcess H z) L goodLSV)
    (hCount : Proposition34MesoscopicCountingInput mu
      (shiftedSingularValueProcess H z) a C goodCount)
    (hHardRate : Tendsto (fun n => C n * a n * L n) atTop (nhds 0))
    (hBulk : forall r, Lemma35LocalBulkComparisonInput mu
      (shiftedSingularValueProcess H z)
      (shiftedSingularValueProcess G z) (R r) (bulkRate r))
    (hBulkScale : forall r, Tendsto
      (fun n => bulkRate r n * (Real.log (R r) - Real.log (a n)))
      atTop (nhds 0))
    (hp : 0 < p)
    (hBC12Negative : BC12GinibreNegativeMomentTightness mu p
      (shiftedSingularValueProcess G z))
    (hBC12Full : ConvergesInProbability mu
      (fun n omega => normalizedShiftLogDet (G n omega) z)
      (circularLogPotential z))
    (hRtop : Tendsto R atTop atTop)
    (hR : forall r, Real.sqrt (Real.exp 1) < R r)
    (hUpperMoments : UpperSecondMomentInputs mu
      (shiftedSingularValueProcess H z)
      (shiftedSingularValueProcess G z) CH CG) :
    Proposition36SequenceConclusion mu M H z := by
  have hh : forall n omega i,
      0 < shiftedSingularValueProcess H z n omega i := by
    intro n omega i
    exact shiftedSingularValueFamily_pos_of_det_ne_zero
      (H n omega) z (hHdet n omega) i
  have hg : forall n omega i,
      0 < shiftedSingularValueProcess G z n omega i := by
    intro n omega i
    exact shiftedSingularValueFamily_pos_of_det_ne_zero
      (G n omega) z (hGdet n omega) i
  have hGinibreFull : BC12GinibreFullLogInput mu
      (shiftedSingularValueProcess G z) (circularLogPotential z) := by
    unfold BC12GinibreFullLogInput
    have hfun :
        (fun n omega => normalizedShiftLogDet (G n omega) z) =
          (fun n omega =>
            empiricalLog (shiftedSingularValueProcess G z n omega)) := by
      funext n omega
      exact normalizedShiftLogDet_eq_empiricalLog_shiftedSingularValues
        (G n omega) z (hGdet n omega)
    rw [hfun] at hBC12Full
    exact hBC12Full
  have hSingular := proposition36_singularValue_form
    (shiftedSingularValueProcess H z)
    (shiftedSingularValueProcess G z)
    a C L R bulkRate p (circularLogPotential z) CH CG
    ha ha1 haZero hL hh hg goodLSV goodCount hLSV hCount hHardRate
    hBulk hBulkScale hp hBC12Negative hGinibreFull hRtop hR hUpperMoments
  have hDeterminant :=
    normalizedShiftLogDet_convergesInProbability_of_singularValues
      H z (circularLogPotential z) hHdet hSingular
  simpa [Proposition36SequenceConclusion, ConvergesInProbability] using
    hDeterminant

/-- Source-facing matrix theorem with the natural almost-sure
nonsingularity condition.

The literature inputs are evaluated on
`positiveShiftedSingularValueProcess`, which is definitionally positive and
agrees almost everywhere with the genuine singular values.  Thus no
pointwise strengthening of the source assumptions is required. -/
theorem proposition36_matrix_form_ae
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} [forall n, Nonempty (Fin (M n))]
    {mu : Measure Omega}
    (H G : forall n,
      Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ)
    (a C L : Nat -> Real) (R : Nat -> Real)
    (bulkRate : Nat -> Nat -> Real)
    (p CH CG : Real)
    (ha : forall n, 0 < a n)
    (ha1 : forall n, a n <= 1)
    (haZero : Tendsto a atTop (nhds 0))
    (hL : forall n, 0 <= L n)
    (hHdet : forall n, ∀ᵐ omega ∂mu,
      (H n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (hGdet : forall n, ∀ᵐ omega ∂mu,
      (G n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (goodLSV goodCount : Nat -> Set Omega)
    (hLSV : Theorem31LeastSingularValueInput mu
      (positiveShiftedSingularValueProcess H z) L goodLSV)
    (hCount : Proposition34MesoscopicCountingInput mu
      (positiveShiftedSingularValueProcess H z) a C goodCount)
    (hHardRate : Tendsto (fun n => C n * a n * L n) atTop (nhds 0))
    (hBulk : forall r, Lemma35LocalBulkComparisonInput mu
      (positiveShiftedSingularValueProcess H z)
      (positiveShiftedSingularValueProcess G z) (R r) (bulkRate r))
    (hBulkScale : forall r, Tendsto
      (fun n => bulkRate r n * (Real.log (R r) - Real.log (a n)))
      atTop (nhds 0))
    (hp : 0 < p)
    (hBC12Negative : BC12GinibreNegativeMomentTightness mu p
      (positiveShiftedSingularValueProcess G z))
    (hBC12Full : ConvergesInProbability mu
      (fun n omega => normalizedShiftLogDet (G n omega) z)
      (circularLogPotential z))
    (hRtop : Tendsto R atTop atTop)
    (hR : forall r, Real.sqrt (Real.exp 1) < R r)
    (hUpperMoments : UpperSecondMomentInputs mu
      (positiveShiftedSingularValueProcess H z)
      (positiveShiftedSingularValueProcess G z) CH CG) :
    Proposition36SequenceConclusion mu M H z := by
  have hGinibreFull : BC12GinibreFullLogInput mu
      (positiveShiftedSingularValueProcess G z)
      (circularLogPotential z) := by
    unfold BC12GinibreFullLogInput
    unfold ConvergesInProbability at hBC12Full ⊢
    exact hBC12Full.congr_left
      (normalizedShiftLogDet_ae_eq_empiricalLog_positiveProcess
        G z hGdet)
  have hSingular := proposition36_singularValue_form
    (positiveShiftedSingularValueProcess H z)
    (positiveShiftedSingularValueProcess G z)
    a C L R bulkRate p (circularLogPotential z) CH CG
    ha ha1 haZero hL
    (positiveShiftedSingularValueProcess_pos H z)
    (positiveShiftedSingularValueProcess_pos G z)
    goodLSV goodCount hLSV hCount hHardRate hBulk hBulkScale hp
    hBC12Negative hGinibreFull hRtop hR hUpperMoments
  have hDeterminant :=
    normalizedShiftLogDet_convergesInProbability_of_positiveProcess
      H z (circularLogPotential z) hHdet hSingular
  simpa [Proposition36SequenceConclusion, ConvergesInProbability] using
    hDeterminant

/-- **Matrix form adapted to discrete short-ring atoms.**

Unlike `proposition36_matrix_form_ae`, this theorem does not assume that the
short-ring shift is nonsingular almost surely at every fixed dimension.
The Theorem 3.1 good event already forces its determinant to be nonzero, and
the complement of that event has probability `o(1)`.  All uses of the
everywhere-positive representative are therefore transferred across this
same high-probability event.  The dense comparison is also required only to
be nonsingular with probability tending to one; per-dimension almost-sure
nonsingularity is a sufficient but unnecessary strengthening.
-/
theorem proposition36_matrix_form_highProbability
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} [forall n, Nonempty (Fin (M n))]
    {mu : Measure Omega}
    (H G : forall n,
      Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ)
    (a C L : Nat -> Real) (R : Nat -> Real)
    (bulkRate : Nat -> Nat -> Real)
    (p CH CG : Real)
    (ha : forall n, 0 < a n)
    (ha1 : forall n, a n <= 1)
    (haZero : Tendsto a atTop (nhds 0))
    (hL : forall n, 0 <= L n)
    (hGnonsingular : ShiftedNonsingularInProbability mu G z)
    (goodLSV goodCount : Nat -> Set Omega)
    (hLSV : Theorem31LeastSingularValueInput mu
      (shiftedSingularValueProcess H z) L goodLSV)
    (hCount : Proposition34MesoscopicCountingInput mu
      (shiftedSingularValueProcess H z) a C goodCount)
    (hHardRate : Tendsto (fun n => C n * a n * L n) atTop (nhds 0))
    (hBulk : forall r, Lemma35LocalBulkComparisonInput mu
      (shiftedSingularValueProcess H z)
      (shiftedSingularValueProcess G z) (R r) (bulkRate r))
    (hBulkScale : forall r, Tendsto
      (fun n => bulkRate r n * (Real.log (R r) - Real.log (a n)))
      atTop (nhds 0))
    (hp : 0 < p)
    (hBC12Negative : BC12GinibreNegativeMomentTightness mu p
      (shiftedSingularValueProcess G z))
    (hBC12Full : ConvergesInProbability mu
      (fun n omega => normalizedShiftLogDet (G n omega) z)
      (circularLogPotential z))
    (hRtop : Tendsto R atTop atTop)
    (hR : forall r, Real.sqrt (Real.exp 1) < R r)
    (hUpperMoments : UpperSecondMomentInputs mu
      (shiftedSingularValueProcess H z)
      (shiftedSingularValueProcess G z) CH CG) :
    Proposition36SequenceConclusion mu M H z := by
  let agreementGood : Nat -> Set Omega := fun n =>
    goodLSV n ∩ shiftedNonsingularSet G z n
  have hAgreementBad : Tendsto
      (fun n => mu (agreementGood n)ᶜ) atTop (nhds 0) := by
    exact hardEdgeIntersection_badProbability
      hLSV.badProbability hGnonsingular
  have hHdetGood : forall n sample, sample ∈ goodLSV n ->
      (H n sample - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0 :=
    hLSV.det_ne_zero_on_good H z L goodLSV
  have hHeq : forall n sample, sample ∈ agreementGood n ->
      positiveShiftedSingularValueProcess H z n sample =
        shiftedSingularValueProcess H z n sample := by
    intro n sample hsample
    funext i
    simp [positiveShiftedSingularValueProcess,
      shiftedSingularValueProcess, hHdetGood n sample hsample.1]
  have hGeq : forall n sample, sample ∈ agreementGood n ->
      positiveShiftedSingularValueProcess G z n sample =
        shiftedSingularValueProcess G z n sample := by
    intro n sample hsample
    funext i
    have hdet : (G n sample - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0 := hsample.2
    simp [positiveShiftedSingularValueProcess,
      shiftedSingularValueProcess, hdet]
  have hLSVPositive : Theorem31LeastSingularValueInput mu
      (positiveShiftedSingularValueProcess H z) L goodLSV := by
    refine
      { badProbability := hLSV.badProbability
        lower := ?_ }
    intro n sample hsample i
    have heq : positiveShiftedSingularValueProcess H z n sample =
        shiftedSingularValueProcess H z n sample := by
      funext j
      simp [positiveShiftedSingularValueProcess,
        shiftedSingularValueProcess, hHdetGood n sample hsample]
    rw [heq]
    exact hLSV.lower n sample hsample i
  let countGood : Nat -> Set Omega := fun n => goodCount n ∩ goodLSV n
  have hCountPositive : Proposition34MesoscopicCountingInput mu
      (positiveShiftedSingularValueProcess H z) a C countGood := by
    refine
      { badProbability := hardEdgeIntersection_badProbability
          hCount.badProbability hLSV.badProbability
        count := ?_ }
    intro n sample hsample
    have heq : positiveShiftedSingularValueProcess H z n sample =
        shiftedSingularValueProcess H z n sample := by
      funext i
      simp [positiveShiftedSingularValueProcess,
        shiftedSingularValueProcess, hHdetGood n sample hsample.2]
    rw [heq]
    exact hCount.count n sample hsample.1
  have hBulkPositive : forall r, Lemma35LocalBulkComparisonInput mu
      (positiveShiftedSingularValueProcess H z)
      (positiveShiftedSingularValueProcess G z) (R r) (bulkRate r) := by
    intro r
    apply IsBigOInProbability.congr_on_good (hBulk r) hAgreementBad
    intro n sample hsample
    have hHsq :
        (fun i => positiveShiftedSingularValueProcess H z n sample i ^ 2) =
          fun i => shiftedSingularValueProcess H z n sample i ^ 2 := by
      rw [hHeq n sample hsample]
    have hGsq :
        (fun i => positiveShiftedSingularValueProcess G z n sample i ^ 2) =
          fun i => shiftedSingularValueProcess G z n sample i ^ 2 := by
      rw [hGeq n sample hsample]
    change empiricalCdfDistanceOn 0 (R r ^ 2)
        (fun i => positiveShiftedSingularValueProcess H z n sample i ^ 2)
        (fun i => positiveShiftedSingularValueProcess G z n sample i ^ 2) =
      empiricalCdfDistanceOn 0 (R r ^ 2)
        (fun i => shiftedSingularValueProcess H z n sample i ^ 2)
        (fun i => shiftedSingularValueProcess G z n sample i ^ 2)
    rw [hHsq, hGsq]
  have hBC12NegativePositive : BC12GinibreNegativeMomentTightness mu p
      (positiveShiftedSingularValueProcess G z) := by
    unfold BC12GinibreNegativeMomentTightness at hBC12Negative ⊢
    apply hBC12Negative.congr_on_good hGnonsingular
    intro n sample hsample
    have hdet : (G n sample - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0 := hsample
    have heq : positiveShiftedSingularValueProcess G z n sample =
        shiftedSingularValueProcess G z n sample := by
      funext i
      simp [positiveShiftedSingularValueProcess,
        shiftedSingularValueProcess, hdet]
    rw [heq]
  have hGinibreFull : BC12GinibreFullLogInput mu
      (positiveShiftedSingularValueProcess G z)
      (circularLogPotential z) := by
    unfold BC12GinibreFullLogInput
    apply hBC12Full.congr_on_good hGnonsingular
    intro n sample hsample
    have hdet : (G n sample - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0 := hsample
    have heq : positiveShiftedSingularValueProcess G z n sample =
        shiftedSingularValueProcess G z n sample := by
      funext i
      simp [positiveShiftedSingularValueProcess,
        shiftedSingularValueProcess, hdet]
    calc
      empiricalLog (positiveShiftedSingularValueProcess G z n sample) =
          empiricalLog (shiftedSingularValueProcess G z n sample) :=
        congrArg empiricalLog heq
      _ = normalizedShiftLogDet (G n sample) z :=
        (normalizedShiftLogDet_eq_empiricalLog_shiftedSingularValues
          (G n sample) z hdet).symm
  have hUpperActual : UpperCorrectionsUniformlyNegligible mu
      (shiftedSingularValueProcess H z)
      (shiftedSingularValueProcess G z) R :=
    upperCorrectionsUniformlyNegligible_of_secondMomentBounds
      hRtop hR hUpperMoments.CH_nonneg hUpperMoments.CG_nonneg
      hUpperMoments.h_integrable hUpperMoments.g_integrable
      hUpperMoments.h_mean hUpperMoments.g_mean
  have hUpperPositive : UpperCorrectionsUniformlyNegligible mu
      (positiveShiftedSingularValueProcess H z)
      (positiveShiftedSingularValueProcess G z) R :=
    hUpperActual.congr_on_good hAgreementBad hHeq hGeq
  have hSingular : ConvergesInProbability mu
      (fun n sample => empiricalLog
        (positiveShiftedSingularValueProcess H z n sample))
      (circularLogPotential z) :=
    proposition36_singularValue_form_of_upperCorrections
      (positiveShiftedSingularValueProcess H z)
      (positiveShiftedSingularValueProcess G z)
      a C L R bulkRate p (circularLogPotential z)
      ha ha1 haZero hL
      (positiveShiftedSingularValueProcess_pos H z)
      (positiveShiftedSingularValueProcess_pos G z)
      goodLSV countGood hLSVPositive hCountPositive hHardRate
      hBulkPositive hBulkScale hp hBC12NegativePositive hGinibreFull
      hR hUpperPositive
  have hDeterminant : ConvergesInProbability mu
      (fun n sample => normalizedShiftLogDet (H n sample) z)
      (circularLogPotential z) := by
    apply hSingular.congr_on_good hLSV.badProbability
    intro n sample hsample
    have hdet := hHdetGood n sample hsample
    rw [normalizedShiftLogDet_eq_empiricalLog_shiftedSingularValues
      (H n sample) z hdet]
    have heq : positiveShiftedSingularValueProcess H z n sample =
        shiftedSingularValueProcess H z n sample := by
      funext i
      simp [positiveShiftedSingularValueProcess,
        shiftedSingularValueProcess, hdet]
    exact congrArg empiricalLog heq.symm
  simpa [Proposition36SequenceConclusion, ConvergesInProbability] using
    hDeterminant

end ShortRingAnchor
