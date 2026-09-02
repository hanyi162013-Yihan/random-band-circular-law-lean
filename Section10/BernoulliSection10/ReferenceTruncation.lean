import ShortRingAnchor.HighProbabilityTransfer
import ShortRingAnchor.UpperEdgeAssembly

/-!
# Full logarithms from a reference model with its own hard-edge bound

This version of the truncation argument controls both matrix families by
least-singular-value and counting estimates. In particular, it does not
use a Ginibre negative-moment or full-logarithm assumption. Section 10 uses
the scalar indicator reference supplied by the permitted Proposition 3.5.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace BernoulliSection10.ReferenceTruncation

open ShortRingAnchor

set_option maxHeartbeats 1500000

variable {Ω : Type*} [MeasurableSpace Ω]
variable {N : ℕ → ℕ} [∀ n, Nonempty (Fin (N n))] {P : Measure Ω}

theorem positive_singular_eq_on_lsv_good
    (A : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℂ) (z : ℂ)
    (L : ℕ → ℝ) (good : ℕ → Set Ω)
    (hLSV : Theorem31LeastSingularValueInput P (shiftedSingularValueProcess A z) L good)
    (n : ℕ) (ω : Ω) (hω : ω ∈ good n) :
    positiveShiftedSingularValueProcess A z n ω = shiftedSingularValueProcess A z n ω := by
  have hd := hLSV.det_ne_zero_on_good A z L good n ω hω
  funext i
  simp [positiveShiftedSingularValueProcess, shiftedSingularValueProcess, hd]

theorem positive_lower_correction_tendsto
    (A : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℂ) (z : ℂ)
    (a C L : ℕ → ℝ) (goodLSV goodCount : ℕ → Set Ω)
    (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1) (hL : ∀ n, 0 ≤ L n)
    (hLSV : Theorem31LeastSingularValueInput P (shiftedSingularValueProcess A z) L goodLSV)
    (hCount : Proposition34MesoscopicCountingInput P
      (shiftedSingularValueProcess A z) a C goodCount)
    (hRate : Tendsto (fun n => C n * a n * L n) atTop (𝓝 0)) :
    ConvergesInProbability P (fun n ω => empiricalLowerLogCorrection (a n)
      (positiveShiftedSingularValueProcess A z n ω)) 0 := by
  apply empiricalLowerLogCorrection_convergesInProbability_of_smallLogMass
    ha ha1 (positiveShiftedSingularValueProcess_pos A z)
  apply normalizedSmallLogMass_convergesInProbability_zero
    (good := fun n => goodLSV n ∩ goodCount n) ha1 hL
  · intro n ω hω i
    rw [positive_singular_eq_on_lsv_good A z L goodLSV hLSV n ω hω.1]
    exact hLSV.lower n ω hω.1 i
  · intro n ω hω
    rw [positive_singular_eq_on_lsv_good A z L goodLSV hLSV n ω hω.1]
    exact hCount.count n ω hω.2
  · exact hardEdgeIntersection_badProbability hLSV.badProbability hCount.badProbability
  · exact hRate

/-- Complete, proved truncation with two ordinary hard-edge controls.
The later full-block theorem constructs every analytic premise here from
its actual model and the exact Section 3 inputs. -/
theorem matrix_log_limit_of_reference
    (A B : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℂ) (z : ℂ)
    (a CA CB LA LB R : ℕ → ℝ)
    (goodLA goodCA goodLB goodCB : ℕ → Set Ω)
    (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (hLA : ∀ n, 0 ≤ LA n) (hLB : ∀ n, 0 ≤ LB n)
    (hLSVA : Theorem31LeastSingularValueInput P (shiftedSingularValueProcess A z) LA goodLA)
    (hLSVB : Theorem31LeastSingularValueInput P (shiftedSingularValueProcess B z) LB goodLB)
    (hCountA : Proposition34MesoscopicCountingInput P
      (shiftedSingularValueProcess A z) a CA goodCA)
    (hCountB : Proposition34MesoscopicCountingInput P
      (shiftedSingularValueProcess B z) a CB goodCB)
    (hRateA : Tendsto (fun n => CA n * a n * LA n) atTop (𝓝 0))
    (hRateB : Tendsto (fun n => CB n * a n * LB n) atTop (𝓝 0))
    (hBulk : ∀ r, ConvergesInProbability P (fun n ω =>
      empiricalClippedLog (a n) (R r) (fun i => shiftedSingularValueProcess A z n ω i ^ 2) -
      empiricalClippedLog (a n) (R r) (fun i => shiftedSingularValueProcess B z n ω i ^ 2)) 0)
    (u : ℝ) (hRef : ConvergesInProbability P (fun n ω => normalizedShiftLogDet (B n ω) z) u)
    (hRtop : Tendsto R atTop atTop) (hR : ∀ r, Real.sqrt (Real.exp 1) < R r)
    (MA MB : ℝ) (hMoments : UpperSecondMomentInputs P
      (shiftedSingularValueProcess A z) (shiftedSingularValueProcess B z) MA MB) :
    ConvergesInProbability P (fun n ω => normalizedShiftLogDet (A n ω) z) u := by
  let good := fun n => goodLA n ∩ goodLB n
  have hbad : Tendsto (fun n => P (good n)ᶜ) atTop (𝓝 0) :=
    hardEdgeIntersection_badProbability hLSVA.badProbability hLSVB.badProbability
  have heA (n : ℕ) (ω : Ω) (hω : ω ∈ good n) :
      positiveShiftedSingularValueProcess A z n ω = shiftedSingularValueProcess A z n ω :=
    positive_singular_eq_on_lsv_good A z LA goodLA hLSVA n ω hω.1
  have heB (n : ℕ) (ω : Ω) (hω : ω ∈ good n) :
      positiveShiftedSingularValueProcess B z n ω = shiftedSingularValueProcess B z n ω :=
    positive_singular_eq_on_lsv_good B z LB goodLB hLSVB n ω hω.2
  have hBulkPos : ∀ r, ConvergesInProbability P (fun n ω =>
      empiricalClippedLog (a n) (R r) (fun i => positiveShiftedSingularValueProcess A z n ω i ^ 2) -
      empiricalClippedLog (a n) (R r) (fun i => positiveShiftedSingularValueProcess B z n ω i ^ 2)) 0 := by
    intro r
    apply (hBulk r).congr_on_good hbad
    intro n ω hω
    rw [heA n ω hω, heB n ω hω]
  have hRefPos : ConvergesInProbability P
      (fun n ω => empiricalLog (positiveShiftedSingularValueProcess B z n ω)) u := by
    apply hRef.congr_on_good hLSVB.badProbability
    intro n ω hω
    rw [positive_singular_eq_on_lsv_good B z LB goodLB hLSVB n ω hω]
    exact (normalizedShiftLogDet_eq_empiricalLog_shiftedSingularValues (B n ω) z
      (hLSVB.det_ne_zero_on_good B z LB goodLB n ω hω)).symm
  have hUpper := upperCorrectionsUniformlyNegligible_of_secondMomentBounds hRtop hR
    hMoments.CH_nonneg hMoments.CG_nonneg hMoments.h_integrable hMoments.g_integrable
    hMoments.h_mean hMoments.g_mean
  have hUpperPos := hUpper.congr_on_good hbad heA heB
  have hsqrt : (1 : ℝ) < Real.sqrt (Real.exp 1) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_lt_sqrt (by norm_num)
    simp
  have haR : ∀ r n, a n ≤ R r := fun r n => (ha1 n).trans (hsqrt.le.trans (hR r).le)
  have hPos := empiricalLog_convergesInProbability_of_truncations ha haR
    (positiveShiftedSingularValueProcess_pos A z) (positiveShiftedSingularValueProcess_pos B z)
    hRefPos hBulkPos
    (positive_lower_correction_tendsto A z a CA LA goodLA goodCA ha ha1 hLA hLSVA hCountA hRateA)
    (positive_lower_correction_tendsto B z a CB LB goodLB goodCB ha ha1 hLB hLSVB hCountB hRateB)
    hUpperPos
  apply hPos.congr_on_good hLSVA.badProbability
  intro n ω hω
  rw [normalizedShiftLogDet_eq_empiricalLog_shiftedSingularValues (A n ω) z
    (hLSVA.det_ne_zero_on_good A z LA goodLA n ω hω)]
  rw [positive_singular_eq_on_lsv_good A z LA goodLA hLSVA n ω hω]
  rfl

end BernoulliSection10.ReferenceTruncation
