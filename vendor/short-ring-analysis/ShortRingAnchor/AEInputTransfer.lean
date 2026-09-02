import ShortRingAnchor.ExternalInputs
import ShortRingAnchor.SingularValues

/-!
# Almost-everywhere transfer of singular-value inputs

The logarithmic decomposition in Proposition 3.6 is most convenient for the
everywhere-positive family `positiveShiftedSingularValueProcess`.  The
random-matrix inputs in the source, however, are naturally stated for the
genuine family `shiftedSingularValueProcess`.

This file proves that the BC12 negative-moment input, the local bulk input,
and the upper second-moment input are unchanged by this null-set
modification.  For the pointwise good-event inputs, it intersects the given
good event with the full-measure nonsingularity event.

No random-matrix assertion is made here: every theorem is an
almost-everywhere transport lemma.
-/

open Filter Set
open scoped ENNReal Topology

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

/-- The full-measure event on which the shifted matrix is nonsingular. -/
def shiftedNonsingularSet
    {Omega : Type*} {M : Nat -> Nat}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (n : Nat) : Set Omega :=
  {omega | (A n omega - z •
    (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0}

/-- Intersecting a sequence of good events with full-measure events does not
change the asymptotic failure probability. -/
theorem tendsto_measure_compl_inter_of_ae
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {good full : Nat -> Set Omega}
    (hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0))
    (hfull : forall n, ∀ᵐ omega ∂mu, omega ∈ full n) :
    Tendsto (fun n => mu (good n ∩ full n)ᶜ) atTop (nhds 0) := by
  have heq : (fun n => mu (good n ∩ full n)ᶜ) =
      fun n => mu (good n)ᶜ := by
    funext n
    apply measure_congr
    filter_upwards [hfull n] with omega homega
    apply propext
    change (omega ∉ good n ∩ full n ↔ omega ∉ good n)
    simp [homega]
  rw [heq]
  exact hbad

/-- The empirical negative moment of the genuine singular values agrees
almost everywhere with that of the positive representative. -/
theorem normalizedNegativeMoment_shifted_ae_eq_positive
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (p : Real)
    (hdet : forall n, ∀ᵐ omega ∂mu,
      (A n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0) :
    forall n,
      (fun omega => normalizedNegativeMoment p
        (shiftedSingularValueProcess A z n omega)) =ᵐ[mu]
      (fun omega => normalizedNegativeMoment p
        (positiveShiftedSingularValueProcess A z n omega)) := by
  intro n
  filter_upwards [positiveShiftedSingularValueProcess_ae_eq A z hdet n]
    with omega homega
  rw [homega]

/-- Transfer the BC12 negative-moment tightness premise from the genuine
singular values to the everywhere-positive representative. -/
theorem bc12GinibreNegativeMomentTightness_positive_of_ae
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (p : Real)
    (hdet : forall n, ∀ᵐ omega ∂mu,
      (A n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (hBC12 : BC12GinibreNegativeMomentTightness mu p
      (shiftedSingularValueProcess A z)) :
    BC12GinibreNegativeMomentTightness mu p
      (positiveShiftedSingularValueProcess A z) := by
  unfold BC12GinibreNegativeMomentTightness at hBC12 ⊢
  exact hBC12.congr_ae
    (normalizedNegativeMoment_shifted_ae_eq_positive A z p hdet)

/-- The local squared-singular-value CDF distance is invariant under replacing
both matrix families by their positive representatives. -/
theorem localCdfDistance_shifted_ae_eq_positive
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} {mu : Measure Omega}
    (H G : forall n,
      Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (R : Real)
    (hHdet : forall n, ∀ᵐ omega ∂mu,
      (H n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (hGdet : forall n, ∀ᵐ omega ∂mu,
      (G n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0) :
    forall n,
      (fun omega => empiricalCdfDistanceOn 0 (R ^ 2)
        (fun i => shiftedSingularValueProcess H z n omega i ^ 2)
        (fun i => shiftedSingularValueProcess G z n omega i ^ 2)) =ᵐ[mu]
      (fun omega => empiricalCdfDistanceOn 0 (R ^ 2)
        (fun i => positiveShiftedSingularValueProcess H z n omega i ^ 2)
        (fun i => positiveShiftedSingularValueProcess G z n omega i ^ 2)) := by
  intro n
  filter_upwards
    [positiveShiftedSingularValueProcess_ae_eq H z hHdet n,
      positiveShiftedSingularValueProcess_ae_eq G z hGdet n]
    with omega hHomega hGomega
  rw [hHomega, hGomega]

/-- Transfer manuscript Lemma 3.5's local bulk conclusion from genuine
singular values to the positive representatives used in the truncation
proof. -/
theorem lemma35LocalBulkComparisonInput_positive_of_ae
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} {mu : Measure Omega}
    (H G : forall n,
      Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (R : Real) (rate : Nat -> Real)
    (hHdet : forall n, ∀ᵐ omega ∂mu,
      (H n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (hGdet : forall n, ∀ᵐ omega ∂mu,
      (G n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (hBulk : Lemma35LocalBulkComparisonInput mu
      (shiftedSingularValueProcess H z)
      (shiftedSingularValueProcess G z) R rate) :
    Lemma35LocalBulkComparisonInput mu
      (positiveShiftedSingularValueProcess H z)
      (positiveShiftedSingularValueProcess G z) R rate := by
  unfold Lemma35LocalBulkComparisonInput LocalBulkComparisonInput at hBulk ⊢
  exact hBulk.congr_ae
    (localCdfDistance_shifted_ae_eq_positive H G z R hHdet hGdet)

/-- The empirical squared singular-value average agrees almost everywhere
with the corresponding average for the positive representative. -/
theorem empiricalSecondMoment_shifted_ae_eq_positive
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ)
    (hdet : forall n, ∀ᵐ omega ∂mu,
      (A n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0) :
    forall n,
      (fun omega => empiricalAverage
        (shiftedSingularValueProcess A z n omega) (fun t => t ^ 2)) =ᵐ[mu]
      (fun omega => empiricalAverage
        (positiveShiftedSingularValueProcess A z n omega) (fun t => t ^ 2)) := by
  intro n
  filter_upwards [positiveShiftedSingularValueProcess_ae_eq A z hdet n]
    with omega homega
  rw [homega]

/-- Transfer the complete upper second-moment package from genuine singular
values to positive representatives. -/
theorem upperSecondMomentInputs_positive_of_ae
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} {mu : Measure Omega}
    (H G : forall n,
      Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (CH CG : Real)
    (hHdet : forall n, ∀ᵐ omega ∂mu,
      (H n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (hGdet : forall n, ∀ᵐ omega ∂mu,
      (G n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (hMoments : UpperSecondMomentInputs mu
      (shiftedSingularValueProcess H z)
      (shiftedSingularValueProcess G z) CH CG) :
    UpperSecondMomentInputs mu
      (positiveShiftedSingularValueProcess H z)
      (positiveShiftedSingularValueProcess G z) CH CG := by
  let hHeq := empiricalSecondMoment_shifted_ae_eq_positive H z hHdet
  let hGeq := empiricalSecondMoment_shifted_ae_eq_positive G z hGdet
  refine
    { CH_nonneg := hMoments.CH_nonneg
      CG_nonneg := hMoments.CG_nonneg
      h_integrable := ?_
      g_integrable := ?_
      h_mean := ?_
      g_mean := ?_ }
  · intro n
    exact (hMoments.h_integrable n).congr (hHeq n)
  · intro n
    exact (hMoments.g_integrable n).congr (hGeq n)
  · intro n
    calc
      (∫ omega, empiricalAverage
          (positiveShiftedSingularValueProcess H z n omega)
          (fun t => t ^ 2) ∂mu) =
          ∫ omega, empiricalAverage
            (shiftedSingularValueProcess H z n omega)
            (fun t => t ^ 2) ∂mu :=
        (integral_congr_ae (hHeq n)).symm
      _ ≤ CH := hMoments.h_mean n
  · intro n
    calc
      (∫ omega, empiricalAverage
          (positiveShiftedSingularValueProcess G z n omega)
          (fun t => t ^ 2) ∂mu) =
          ∫ omega, empiricalAverage
            (shiftedSingularValueProcess G z n omega)
            (fun t => t ^ 2) ∂mu :=
        (integral_congr_ae (hGeq n)).symm
      _ ≤ CG := hMoments.g_mean n

/-- Transfer the Theorem 3.1 least-singular-value input by shrinking its good
event to the nonsingular set. -/
theorem theorem31LeastSingularValueInput_positive_of_ae
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (L : Nat -> Real) (good : Nat -> Set Omega)
    (hdet : forall n, ∀ᵐ omega ∂mu,
      (A n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (hLSV : Theorem31LeastSingularValueInput mu
      (shiftedSingularValueProcess A z) L good) :
    Theorem31LeastSingularValueInput mu
      (positiveShiftedSingularValueProcess A z) L
      (fun n => good n ∩ shiftedNonsingularSet A z n) := by
  refine
    { badProbability := ?_
      lower := ?_ }
  · apply tendsto_measure_compl_inter_of_ae hLSV.badProbability
    intro n
    simpa only [shiftedNonsingularSet, Set.mem_ofPred_eq] using hdet n
  · intro n omega homega i
    have hdetomega :
        (A n omega - z •
          (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0 := by
      exact homega.2
    have hfamily :
        positiveShiftedSingularValueProcess A z n omega =
          shiftedSingularValueProcess A z n omega := by
      funext j
      simp [positiveShiftedSingularValueProcess,
        shiftedSingularValueProcess, hdetomega]
    rw [hfamily]
    exact hLSV.lower n omega homega.1 i

/-- Transfer the Proposition 3.4 mesoscopic counting input by shrinking its
good event to the nonsingular set. -/
theorem proposition34MesoscopicCountingInput_positive_of_ae
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (a C : Nat -> Real) (good : Nat -> Set Omega)
    (hdet : forall n, ∀ᵐ omega ∂mu,
      (A n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (hCount : Proposition34MesoscopicCountingInput mu
      (shiftedSingularValueProcess A z) a C good) :
    Proposition34MesoscopicCountingInput mu
      (positiveShiftedSingularValueProcess A z) a C
      (fun n => good n ∩ shiftedNonsingularSet A z n) := by
  refine
    { badProbability := ?_
      count := ?_ }
  · apply tendsto_measure_compl_inter_of_ae hCount.badProbability
    intro n
    simpa only [shiftedNonsingularSet, Set.mem_ofPred_eq] using hdet n
  · intro n omega homega
    have hdetomega :
        (A n omega - z •
          (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0 := by
      exact homega.2
    have hfamily :
        positiveShiftedSingularValueProcess A z n omega =
          shiftedSingularValueProcess A z n omega := by
      funext j
      simp [positiveShiftedSingularValueProcess,
        shiftedSingularValueProcess, hdetomega]
    rw [hfamily]
    exact hCount.count n omega homega.1

end ShortRingAnchor
