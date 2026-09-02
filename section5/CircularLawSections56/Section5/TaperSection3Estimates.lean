import CircularLawSections56.Section5.TaperCutoffDominance
import ShortRingAnchor.Proposition36Source

/-! # Taper short-ring limit from the accepted Section 3 estimates

This reruns the existing Section 3 truncation theorem with the actual taper
bandwidth cutoff. No uniform lower bound on all taper weights and no taper
log-potential convergence are hypotheses. The least-singular-value estimate
uses the inner bandwidth `V`; counting uses the actual maximum-variance
cutoff. The random-matrix estimates remain the explicitly accepted Section 3
preinputs, including its existing dense comparison results.
-/

open Filter MeasureTheory Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5
open ShortRingAnchor

theorem section3_short_ring_of_taper_estimates
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : PolynomialTaperProfile) (M W V : ℕ → ℕ) [∀ n, Nonempty (Fin (M n))]
    (H G : ∀ n, Ω → Matrix (Fin (M n)) (Fin (M n)) ℂ) (z : ℂ)
    (β χ κ τ K C a CH CG : ℝ) (R ζ : ℕ → ℝ)
    (hparam : HardEdgeAdmissible β χ κ τ)
    (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop)
    (hWpos : ∀ n, 0 < W n) (hVW : ∀ n, V n ≤ W n)
    (hband : ∀ᶠ n in atTop, (M n : ℝ) ^ β ≤ V n)
    (hKdom : p.upperWeightConstant ^ (1 / 8 : ℝ) ≤ K) (hC : 0 ≤ C)
    (hRtop : Tendsto R atTop atTop) (hR : ∀ r, Real.sqrt (Real.exp 1) < R r)
    (hζ : ∀ r, 0 < ζ r) (ha : 0 < a)
    (hGnonsingular : ShiftedNonsingularInProbability μ G z)
    (goodLSV goodCount : ℕ → Set Ω)
    (hLSV : Theorem31MinimumSingularValueInput hMpos μ H z
      (sourceHardEdgeScale M V κ) goodLSV)
    (hCount : Proposition34AllCutoffsInput μ (shiftedSingularValueProcess H z)
      (fun n => p.hardEdgeCutoff (M n) (W n) τ) (fun _ => C) goodCount)
    (hBulk : ∀ r, Lemma35LocalBulkComparisonInput μ
      (shiftedSingularValueProcess H z) (shiftedSingularValueProcess G z)
      (R r) (sourceBulkRate M ζ r))
    (hBC12Negative : BC12GinibreNegativeMomentTightness μ a (shiftedSingularValueProcess G z))
    (hBC12Full : ConvergesInProbability μ
      (fun n ω => normalizedShiftLogDet (G n ω) z) (circularLogPotential z))
    (hHSecond : CenteredMatrixRowSecondMomentInputs μ H CH)
    (hGSecond : CenteredMatrixRowSecondMomentInputs μ G CG) :
    Proposition36SequenceConclusion μ M H z := by
  have hK : 0 < K := (Real.rpow_pos_of_pos p.upperWeightConstant_pos _).trans_le hKdom
  have hcutPos : ∀ n, 0 < sourceCutoff M K β τ n :=
    fun n => sourceCutoff_pos hK (hMpos n)
  have hcutOne : ∀ n, sourceCutoff M K β τ n ≤ 1 := fun _ => sourceCutoff_le_one
  have hcutZero : Tendsto (sourceCutoff M K β τ) atTop (𝓝 0) :=
    sourceCutoff_tendsto_zero hparam hM
  have hL : ∀ n, 0 ≤ sourceHardEdgeScale M V κ n := by
    intro n
    have hMone : (1 : ℝ) ≤ M n := by exact_mod_cast (hMpos n)
    exact add_nonneg
      (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
      (mul_nonneg (by norm_num) (Real.log_nonneg hMone))
  have hHardRate : Tendsto
      (fun n => C * sourceCutoff M K β τ n * sourceHardEdgeScale M V κ n) atTop (𝓝 0) :=
    sourceHardEdgeError_tendsto_zero hparam hM hband hK hC
  have hBulkScale : ∀ r, Tendsto (fun n => sourceBulkRate M ζ r n *
      (Real.log (R r) - Real.log (sourceCutoff M K β τ n))) atTop (𝓝 0) := by
    intro r
    have hRpos : 0 < R r := (Real.sqrt_pos.2 (Real.exp_pos 1)).trans (hR r)
    exact sourceBulkCutoffBookkeeping_tendsto_zero (K := K) hparam hM hK hRpos (hζ r)
  obtain ⟨specializedGoodCount, hCountSpecialized⟩ := hCount.specialize_eventually
    (p.hardEdgeCutoff_le_sourceCutoff_eventually M W V β χ κ τ K hparam hM hWpos hVW hband hKdom)
  have hLSVAll : Theorem31LeastSingularValueInput μ (shiftedSingularValueProcess H z)
      (sourceHardEdgeScale M V κ) goodLSV :=
    theorem31LeastSingularValueInput_of_minimum hMpos H z (sourceHardEdgeScale M V κ) goodLSV hLSV
  have hUpper : UpperSecondMomentInputs μ (shiftedSingularValueProcess H z)
      (shiftedSingularValueProcess G z) (CH + ‖z‖ ^ 2) (CG + ‖z‖ ^ 2) :=
    upperSecondMomentInputs_of_centered_matrix_entries H G z CH CG hHSecond hGSecond
  exact proposition36_matrix_form_highProbability H G z (sourceCutoff M K β τ)
    (fun _ => C) (sourceHardEdgeScale M V κ) R (sourceBulkRate M ζ)
    a (CH + ‖z‖ ^ 2) (CG + ‖z‖ ^ 2)
    hcutPos hcutOne hcutZero hL hGnonsingular goodLSV specializedGoodCount
    hLSVAll hCountSpecialized hHardRate hBulk hBulkScale ha hBC12Negative hBC12Full
    hRtop hR hUpper

end CircularLawSections56.Section5
