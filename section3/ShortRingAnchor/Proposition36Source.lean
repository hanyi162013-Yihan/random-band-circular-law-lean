import ShortRingAnchor.Proposition36
import ShortRingAnchor.SourceScales
import ShortRingAnchor.AEInputTransfer
import ShortRingAnchor.SecondMoment
import ShortRingAnchor.CutoffDominance
import ShortRingAnchor.EventualInputAdapters
import ShortRingAnchor.LeastSingularValueAdapter

/-!
# Proposition 3.6 with the manuscript scales substituted

`Proposition36.lean` proves the probabilistic truncation argument from
explicit named inputs.  This file discharges the remaining deterministic
premises using (3.7), (3.9), and the concrete choices

* `a_M = min 1 (K M^(tau-beta/8))`,
* `L_M = M^(1+3*kappa)/W + 2 log M`, and
* the Lemma 3.5 rate `M^(-zeta_R)`.

The cap by one changes only finitely many indices and is useful because Lean's
finite-sequence theorem is stated without silently discarding an initial
segment.  `SourceScales.lean` proves that the cap is eventually inactive.

No random-matrix assertion is introduced here.  The inputs named after
Theorem 3.1, Proposition 3.4, Lemma 3.5, and BC12 remain ordinary theorem
parameters.
-/

open Filter Set
open scoped ENNReal Topology

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

/-- The polynomial comparison rate in manuscript formula (3.11). -/
def sourceBulkRate (M : Nat -> Nat) (zeta : Nat -> Real)
    (r n : Nat) : Real :=
  (M n : Real) ^ (-(zeta r))

/-- The exponent in the v3 bandwidth assumption (3.7). -/
def v3BandwidthExponent (omega : Real) : Real :=
  8 / 9 + omega

/-- **Proposition 3.6, with all deterministic scale bookkeeping checked.**

Compared with `proposition36_matrix_form_ae`, this theorem no longer asks for
`a_M -> 0`, `C a_M L_M -> 0`, or
`M^(-zeta_R) (log R-log a_M) -> 0`.  Those facts follow in Lean from the
source bandwidth condition and (3.9).

The remaining premises are precisely probabilistic/random-matrix inputs:
the preceding hard-edge and bulk estimates, the two explicitly named BC12
conclusions, and nonsingularity of the dense Ginibre comparison with
probability tending to one.
No nonsingularity premise is imposed on the short-ring matrix: its Theorem
3.1 good event already forces invertibility, and the new high-probability
transport proves that its exceptional samples are harmless.  At the upper
edge the theorem asks only for entrywise centering, integrability, and a
constant row second-moment sum; `SecondMoment.lean` proves the
Hilbert--Schmidt calculation and constructs the former
`UpperSecondMomentInputs` internally.
-/
theorem proposition36_of_source_scales
    {Omega : Type*} [MeasurableSpace Omega]
    {M W : Nat -> Nat} [forall n, Nonempty (Fin (M n))]
    {c0 C0 : Real}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (weights : forall n, AdmissibleWeights (W n) c0 C0)
    (H G : forall n,
      Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ)
    (omega chi kappa tau K C p CH0 CG0 : Real)
    (R zeta : Nat -> Real)
    (_homega : 0 < omega ∧ omega < 1 / 9)
    (hparam : HardEdgeAdmissible
      (v3BandwidthExponent omega) chi kappa tau)
    (hMpos : forall n, 0 < M n)
    (hM : Tendsto M atTop atTop)
    (_hW : Tendsto W atTop atTop)
    (hband : forall n,
      (M n : Real) ^ (v3BandwidthExponent omega) <= (W n : Real))
    (hKdom : C0 ^ (1 / 8 : Real) <= K) (hC : 0 <= C)
    (hRtop : Tendsto R atTop atTop)
    (hR : forall r, Real.sqrt (Real.exp 1) < R r)
    (hzeta : forall r, 0 < zeta r)
    (hGnonsingular : ShiftedNonsingularInProbability mu G z)
    (goodLSV goodCount : Nat -> Set Omega)
    (hLSV : Theorem31MinimumSingularValueInput hMpos mu H z
      (sourceHardEdgeScale M W kappa) goodLSV)
    (hCount : Proposition34AllCutoffsInput mu
      (shiftedSingularValueProcess H z)
      (fun n => manuscriptHardEdgeCutoff (weights n) (M n) tau)
      (fun _ => C) goodCount)
    (hBulk : forall r, Lemma35LocalBulkComparisonInput mu
      (shiftedSingularValueProcess H z)
      (shiftedSingularValueProcess G z)
      (R r) (sourceBulkRate M zeta r))
    (hp : 0 < p)
    (hBC12Negative : BC12GinibreNegativeMomentTightness mu p
      (shiftedSingularValueProcess G z))
    (hBC12Full : ConvergesInProbability mu
      (fun n omega => normalizedShiftLogDet (G n omega) z)
      (circularLogPotential z))
    (hHSecondMoment : CenteredMatrixRowSecondMomentInputs mu H CH0)
    (hGSecondMoment : CenteredMatrixRowSecondMomentInputs mu G CG0) :
    Proposition36SequenceConclusion mu M H z := by
  have hK : 0 < K := by
    have hC0pow : 0 < C0 ^ (1 / 8 : Real) :=
      Real.rpow_pos_of_pos (weights 0).C0_pos _
    exact hC0pow.trans_le hKdom
  have hbandEventually : ∀ᶠ n in atTop,
      (M n : Real) ^ (v3BandwidthExponent omega) <= (W n : Real) :=
    Filter.Eventually.of_forall hband
  have ha : forall n,
      0 < sourceCutoff M K (v3BandwidthExponent omega) tau n := by
    intro n
    exact sourceCutoff_pos hK (hMpos n)
  have ha1 : forall n,
      sourceCutoff M K (v3BandwidthExponent omega) tau n <= 1 := by
    intro n
    exact sourceCutoff_le_one
  have haZero : Tendsto
      (sourceCutoff M K (v3BandwidthExponent omega) tau)
      atTop (nhds 0) :=
    sourceCutoff_tendsto_zero hparam hM
  have hL : forall n, 0 <= sourceHardEdgeScale M W kappa n := by
    intro n
    have hMone : 1 <= M n := hMpos n
    have hMoneReal : (1 : Real) <= M n := by exact_mod_cast hMone
    unfold sourceHardEdgeScale
    exact add_nonneg
      (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Nat.cast_nonneg _))
      (mul_nonneg (by norm_num) (Real.log_nonneg hMoneReal))
  have hHardRate : Tendsto
      (fun n => C * sourceCutoff M K (v3BandwidthExponent omega) tau n *
        sourceHardEdgeScale M W kappa n) atTop (nhds 0) := by
    have h := sourceHardEdgeError_tendsto_zero
      hparam hM hbandEventually hK hC
    change Tendsto
      (fun n => C * sourceCutoff M K (v3BandwidthExponent omega) tau n *
        sourceHardEdgeScale M W kappa n) atTop (nhds 0) at h
    exact h
  have hBulkScale : forall r, Tendsto
      (fun n => sourceBulkRate M zeta r n *
        (Real.log (R r) - Real.log
          (sourceCutoff M K (v3BandwidthExponent omega) tau n)))
      atTop (nhds 0) := by
    intro r
    have hRpos : 0 < R r :=
      (Real.sqrt_pos.2 (Real.exp_pos 1)).trans (hR r)
    have h := sourceBulkCutoffBookkeeping_tendsto_zero
      (K := K) hparam hM hK hRpos (hzeta r)
    change Tendsto
      (fun n => (M n : Real) ^ (-(zeta r)) *
        (Real.log (R r) - Real.log
          (sourceCutoff M K (v3BandwidthExponent omega) tau n)))
      atTop (nhds 0) at h
    exact h
  have hCutoffDominance : ∀ᶠ n in atTop,
      manuscriptHardEdgeCutoff (weights n) (M n) tau <=
        sourceCutoff M K (v3BandwidthExponent omega) tau n :=
    manuscriptHardEdgeCutoff_le_sourceCutoff_eventually
      weights hparam hM hbandEventually hKdom
  obtain ⟨specializedGoodCount, hCountSpecialized⟩ :=
    hCount.specialize_eventually hCutoffDominance
  have hLSVAll : Theorem31LeastSingularValueInput mu
      (shiftedSingularValueProcess H z)
      (sourceHardEdgeScale M W kappa) goodLSV :=
    theorem31LeastSingularValueInput_of_minimum
      hMpos H z (sourceHardEdgeScale M W kappa) goodLSV hLSV
  have hUpperMoments : UpperSecondMomentInputs mu
      (shiftedSingularValueProcess H z)
      (shiftedSingularValueProcess G z)
      (CH0 + ‖z‖ ^ 2) (CG0 + ‖z‖ ^ 2) :=
    upperSecondMomentInputs_of_centered_matrix_entries
      H G z CH0 CG0 hHSecondMoment hGSecondMoment
  exact proposition36_matrix_form_highProbability H G z
    (sourceCutoff M K (v3BandwidthExponent omega) tau) (fun _ => C)
    (sourceHardEdgeScale M W kappa) R (sourceBulkRate M zeta)
    p (CH0 + ‖z‖ ^ 2) (CG0 + ‖z‖ ^ 2)
    ha ha1 haZero hL hGnonsingular goodLSV specializedGoodCount
    hLSVAll hCountSpecialized hHardRate hBulk hBulkScale hp
    hBC12Negative hBC12Full hRtop hR hUpperMoments

end ShortRingAnchor
