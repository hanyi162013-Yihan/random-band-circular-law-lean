import BernoulliSection10.VarianceProfiles
import BernoulliSection10.Section3HardEdge
import BernoulliSection10.Section3Bulk
import BernoulliSection10.ReferenceTruncation

/-!
# Proposition 10.1 from the permitted Section 3 statements

The comparison ensemble is the actual scalar indicator ring of width
floor((N-1)/2). Its limit comes from Proposition 3.5. Both model-to-Ginibre
comparisons use the same Gaussian array and cancel; therefore neither a
Ginibre log-limit assumption nor an additional literature theorem enters.
-/

open Filter MeasureTheory Topology

noncomputable section

namespace BernoulliSection10.SourceInputs

open ShortRingAnchor ReferenceTruncation

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem fullBlockHighBand_profile_log_limit
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) (hSource : Section3Inputs μ L)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (ω : ℝ) (hω : 0 < ω) (hω1 : ω < 1 / 9)
    (hhigh : ∀ᶠ n in atTop, (((s n + 3) * W n : ℕ) : ℝ) ^ (8 / 9 + ω) ≤ W n)
    (z : ℂ) :
    ConvergesInProbability (inputLaw μ)
      (fun n sample => normalizedShiftLogDet (profileMatrix (physicalProfile (W n) (s n)) sample) z)
      (circularLogPotential z) := by
  letI := hμ.toIsProbabilityMeasure
  let N := fun n => (s n + 3) * W n
  have hN (n : ℕ) : 0 < N n := Nat.mul_pos (by omega) (hW n)
  letI (n : ℕ) : Nonempty (Fin (N n)) := ⟨⟨0, hN n⟩⟩
  have hNtop : Tendsto N atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hWtop
    exact Eventually.of_forall fun n => Nat.le_mul_of_pos_left (W n) (by omega)
  let V := fun n => scalarReferenceWidth (N n)
  have hWV (n : ℕ) : W n ≤ V n := width_le_scalarReferenceWidth (W n) (s n) (hW n)
  have hV (n : ℕ) : 0 < V n := (hW n).trans_le (hWV n)
  have hVtop : Tendsto V atTop atTop :=
    tendsto_atTop_mono' atTop (Eventually.of_forall hWV) hWtop
  have hfit (n : ℕ) : 2 * V n + 1 ≤ N n := scalarReferenceWidth_fit (N n) (hN n)
  let σ := fun n => physicalProfile (W n) (s n)
  let ρ := fun n => scalarIndicatorProfile (uniformIndicatorWeights (V n)) (hfit n)
  have hσ (n : ℕ) : DoublyStochasticProfile (σ n) :=
    physicalProfile_doublyStochastic (W n) (s n) (hW n)
  have hρ (n : ℕ) : DoublyStochasticProfile (ρ n) :=
    scalarIndicatorProfile_doublyStochastic (uniformIndicatorWeights (V n)) (hfit n)
  let β := (8 / 9 : ℝ) + ω
  obtain ⟨χ, κ, τ, hp⟩ := exists_hardEdgeAdmissible_of_omega hω
  have hhighV : ∀ᶠ n in atTop, (N n : ℝ) ^ β ≤ V n := by
    filter_upwards [hhigh] with n hn
    exact hn.trans (Nat.cast_le.mpr (hWV n))
  have hlsvW : ∀ᶠ n in atTop, (N n : ℝ) ^ (1 / 2 + χ) ≤ W n := by
    filter_upwards [hhigh] with n hn
    exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN n)
      hp.2.2.2.1.le).trans hn
  have hlsvV : ∀ᶠ n in atTop, (N n : ℝ) ^ (1 / 2 + χ) ≤ V n := by
    filter_upwards [hlsvW] with n hn
    exact hn.trans (Nat.cast_le.mpr (hWV n))
  have hbσ : ∀ᶠ n in atTop, (N n : ℝ) ^ β ≤ effectiveBandwidth (σ n) := by
    filter_upwards [hhigh] with n hn
    rw [effectiveBandwidth_physicalProfile (W n) (s n) (hW n)]
    nlinarith [Nat.cast_nonneg (α := ℝ) (W n)]
  have hbρ : ∀ᶠ n in atTop, (N n : ℝ) ^ β ≤ effectiveBandwidth (ρ n) := by
    filter_upwards [hhighV] with n hn
    rw [effectiveBandwidth_uniformIndicator (hN n) (hfit n)]
    have hVn : (0 : ℝ) ≤ V n := Nat.cast_nonneg _
    push_cast
    linarith
  have hLA := leastSingularValueInput_of_section3 hμ hSource N W σ hN hW hNtop hσ
    χ κ (1 / 3) 1 hp.1 hp.2.1 hp.2.2.2.2.1 (by norm_num) (by norm_num)
    (fun n => physicalProfile_lsv_upper (W n) (s n) (hW n))
    (fun n i j h => physicalProfile_lsv_lower (W n) (s n) (hW n) i j h) hlsvW z
  have hLB := leastSingularValueInput_of_section3 hμ hSource N V ρ hN hV hNtop hρ
    χ κ (1 / 3) 1 hp.1 hp.2.1 hp.2.2.2.2.1 (by norm_num) (by norm_num)
    (fun n => uniformIndicator_lsv_upper (hN n) (hV n) (hfit n))
    (fun n i j h => uniformIndicator_lsv_lower (hV n) (hfit n) i j h) hlsvV z
  obtain ⟨CA, hCA, goodA, hcountA⟩ := mesoscopicCountingInput_of_section3
    hμ h3 hSource N σ hN hNtop hσ β χ κ τ hp hbσ z
  obtain ⟨CB, hCB, goodB, hcountB⟩ := mesoscopicCountingInput_of_section3
    hμ h3 hSource N ρ hN hNtop hρ β χ κ τ hp hbρ z
  have hRef := hSource.scalarAnchor hμ h3 N V 1 1
    (fun n => uniformIndicatorWeights (V n)) hfit hN hNtop hVtop ω hω hω1 hhighV z
  let R := fun r : ℕ => Real.sqrt (Real.exp 1) + (r : ℝ) + 1
  have hRtop : Tendsto R atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
    exact Eventually.of_forall fun r => by dsimp [R]; have := Real.sqrt_nonneg (Real.exp 1); linarith
  have hR (r : ℕ) : Real.sqrt (Real.exp 1) < R r := by
    dsimp [R]
    have := Nat.cast_nonneg (α := ℝ) r
    linarith
  apply matrix_log_limit_of_reference
    (fun n sample => profileMatrix (σ n) sample) (fun n sample => profileMatrix (ρ n) sample) z
    (sourceCutoff N 1 β τ) (fun _ => CA) (fun _ => CB)
    (sourceHardEdgeScale N W κ) (sourceHardEdgeScale N V κ) R _ goodA _ goodB
    (fun n => sourceCutoff_pos (by norm_num) (hN n))
    (fun _ => sourceCutoff_le_one)
    (fun n => sourceHardEdgeScale_nonneg (hN n) (hW n))
    (fun n => sourceHardEdgeScale_nonneg (hN n) (hV n))
    hLA hLB hcountA hcountB
    (sourceHardEdgeError_tendsto_zero hp hNtop hhigh (by norm_num) hCA.le)
    (sourceHardEdgeError_tendsto_zero hp hNtop hhighV (by norm_num) hCB.le)
    (fun r => clippedLogComparison_of_section3 hμ h3 hSource N σ ρ hN hNtop hσ hρ
      β χ κ τ hp hbσ hbρ z (R r) (by
        dsimp [R]
        have := Real.sqrt_nonneg (Real.exp 1)
        have := Nat.cast_nonneg (α := ℝ) r
        linarith))
    (circularLogPotential z) hRef hRtop hR (1 + ‖z‖ ^ 2) (1 + ‖z‖ ^ 2)
  exact upperSecondMomentInputs_of_centered_matrix_entries _ _ z 1 1
    (profileMatrix_row_moments hμ σ hσ) (profileMatrix_row_moments hμ ρ hρ)

end BernoulliSection10.SourceInputs
