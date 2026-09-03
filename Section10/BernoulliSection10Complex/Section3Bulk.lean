import BernoulliSection10Complex.Section3Counting

/-! # Two permitted Section 3.4 comparisons cancel their common Ginibre reference -/

open Filter MeasureTheory Topology

noncomputable section

namespace BernoulliSection10Complex.SourceInputs

open BernoulliSection10.SourceInputs

open ShortRingAnchor

theorem clippedLogComparison_of_section3
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ) (hSource : Section3Inputs μ L)
    (N : ℕ → ℕ) [∀ n, Nonempty (Fin (N n))]
    (σ ρ : ∀ n, Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (hN : ∀ n, 0 < N n) (hNtop : Tendsto N atTop atTop)
    (hσ : ∀ n, DoublyStochasticProfile (σ n))
    (hρ : ∀ n, DoublyStochasticProfile (ρ n))
    (β χ κ τ : ℝ) (hp : HardEdgeAdmissible β χ κ τ)
    (hbσ : ∀ᶠ n in atTop, (N n : ℝ) ^ β ≤ effectiveBandwidth (σ n))
    (hbρ : ∀ᶠ n in atTop, (N n : ℝ) ^ β ≤ effectiveBandwidth (ρ n))
    (z : ℂ) (R : ℝ) (hR : 1 ≤ R) :
    ConvergesInProbability (inputLaw μ) (fun n ω =>
      empiricalClippedLog (sourceCutoff N 1 β τ n) R
        (fun i => shiftedSingularValueFamily (profileMatrix (σ n) ω) z i ^ 2) -
      empiricalClippedLog (sourceCutoff N 1 β τ n) R
        (fun i => shiftedSingularValueFamily (profileMatrix (ρ n) ω) z i ^ 2)) 0 := by
  have hβ : 0 < β := by have := hp.1; have := hp.2.2.2.1; linarith
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have ha (n : ℕ) : 0 < sourceCutoff N 1 β τ n := sourceCutoff_pos (by norm_num) (hN n)
  have haR (n : ℕ) : sourceCutoff N 1 β τ n ≤ R := sourceCutoff_le_one.trans hR
  obtain ⟨ζσ, hζσ, hbulkσ⟩ := hSource.localBulk hμ h3 N σ hN hNtop hσ β hβ hbσ z R hRp.le
  obtain ⟨ζρ, hζρ, hbulkρ⟩ := hSource.localBulk hμ h3 N ρ hN hNtop hρ β hβ hbρ z R hRp.le
  have hA := bulkClippedLog_convergesInProbability_zero ha haR hbulkσ
    (sourceBulkCutoffBookkeeping_tendsto_zero hp hNtop (by norm_num) hRp hζσ)
  have hB := bulkClippedLog_convergesInProbability_zero ha haR hbulkρ
    (sourceBulkCutoffBookkeeping_tendsto_zero hp hNtop (by norm_num) hRp hζρ)
  have h := hA.sub hB
  simpa only [sub_sub_sub_cancel_right, sub_self] using h

end BernoulliSection10Complex.SourceInputs
