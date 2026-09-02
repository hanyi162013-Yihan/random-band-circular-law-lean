import BernoulliSection10.Section3Inputs
import ShortRingAnchor.SourceScales

/-! # Section 3.3 at the actual, bounded lower cutoff -/

open Filter MeasureTheory Set Topology

noncomputable section

namespace BernoulliSection10.SourceInputs

open ShortRingAnchor

set_option maxHeartbeats 1200000

theorem mesoscopicThreshold_le_sourceCutoff_eventually
    {N : ℕ → ℕ} (hN : ∀ n, 0 < N n) (hNtop : Tendsto N atTop atTop)
    (b : ℕ → ℝ) {β χ κ τ : ℝ} (hp : HardEdgeAdmissible β χ κ τ)
    (hb : ∀ᶠ n in atTop, (N n : ℝ) ^ β ≤ b n) :
    ∀ᶠ n in atTop, b n ^ (-1 / 8 : ℝ) * (N n : ℝ) ^ τ ≤
      sourceCutoff N 1 β τ n := by
  filter_upwards [hb, sourceCutoff_eventually_eq_raw (K := 1) hp hNtop] with n hbn hraw
  rw [hraw, sourceRawCutoff, one_mul]
  have hNp : (0 : ℝ) < N n := Nat.cast_pos.mpr (hN n)
  have hpow := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNp β) hbn
    (by norm_num : (-1 / 8 : ℝ) ≤ 0)
  calc
    b n ^ (-1 / 8 : ℝ) * (N n : ℝ) ^ τ ≤
        ((N n : ℝ) ^ β) ^ (-1 / 8 : ℝ) * (N n : ℝ) ^ τ :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hNp.le _)
    _ = (N n : ℝ) ^ sourceCutoffExponent β τ := by
      rw [← Real.rpow_mul hNp.le, ← Real.rpow_add hNp]
      congr 1
      unfold sourceCutoffExponent
      ring

theorem mesoscopicCountingInput_of_section3
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) (hSource : Section3Inputs μ L)
    (N : ℕ → ℕ) (σ : ∀ n, Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (hN : ∀ n, 0 < N n) (hNtop : Tendsto N atTop atTop)
    (hσ : ∀ n, DoublyStochasticProfile (σ n))
    (β χ κ τ : ℝ) (hp : HardEdgeAdmissible β χ κ τ)
    (hb : ∀ᶠ n in atTop, (N n : ℝ) ^ β ≤ effectiveBandwidth (σ n))
    (z : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∃ good : ℕ → Set InputSpace,
      Proposition34MesoscopicCountingInput (inputLaw μ)
        (shiftedSingularValueProcess (fun n ω => profileMatrix (σ n) ω) z)
        (sourceCutoff N 1 β τ) (fun _ => C) good := by
  have hβ : 0 < β := by have := hp.1; have := hp.2.2.2.1; linarith
  obtain ⟨C, hC, hest⟩ := hSource.mesoscopicCounting hμ h3 N σ hN hNtop hσ
    β hβ hb z τ hp.2.2.1
  let threshold := fun n => effectiveBandwidth (σ n) ^ (-1 / 8 : ℝ) * (N n : ℝ) ^ τ
  let good := fun n => {ω | mesoscopicGood (profileMatrix (σ n) ω - z • 1) (threshold n) C}
  have hpow : Tendsto (fun n => (N n : ℝ) ^ (-10 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_atTop_zero_of_neg (by norm_num)).comp (tendsto_natCast_comp_atTop hNtop)
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hpow
  have hbad : Tendsto (fun n => (inputLaw μ) (good n)ᶜ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds (by simpa only [ENNReal.ofReal_zero] using hlim)
      (Eventually.of_forall fun _ => zero_le)
    exact hest
  have hdom := mesoscopicThreshold_le_sourceCutoff_eventually hN hNtop
    (fun n => effectiveBandwidth (σ n)) hp hb
  obtain ⟨good', hgood'⟩ := proposition34MesoscopicCountingInput_of_eventually
    (C := fun _ => 2 * C) hbad (show ∀ᶠ n in atTop, ∀ ω, ω ∈ good n →
      ((smallSingularValueIndices (shiftedSingularValueProcess
        (fun n ω => profileMatrix (σ n) ω) z n ω) (sourceCutoff N 1 β τ n)).card : ℝ) ≤
          (2 * C) * (Fintype.card (Fin (N n)) : ℝ) * sourceCutoff N 1 β τ n from by
      filter_upwards [hdom] with n hn
      intro ω hω
      let a := sourceCutoff N 1 β τ n
      have ha : 0 < a := sourceCutoff_pos (by norm_num) (hN n)
      have ha1 : a ≤ 1 := sourceCutoff_le_one
      have hc := hω (-a) a (by linarith) (by linarith) (by linarith)
        (by dsimp only [threshold] at *; linarith)
      have hs := smallSingularValue_card_le_smallHermitizationEigenvalue_card
        (profileMatrix (σ n) ω - z • 1) a ha.le
      have hsr : ((smallSingularValueIndices (shiftedSingularValueProcess
          (fun n ω => profileMatrix (σ n) ω) z n ω) a).card : ℝ) ≤
            hermitianIntervalCount (profileMatrix (σ n) ω - z • 1) (-a) a := by
        exact_mod_cast hs
      simp only [Fintype.card_fin]
      dsimp [a] at *
      linarith)
  exact ⟨2 * C, by positivity, good', hgood'⟩

end BernoulliSection10.SourceInputs
