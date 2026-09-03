import BernoulliSection10Complex.CutoffRemoval
import ShortRingAnchor.LeastSingularValueAdapter

/-! # The actual Section 3.1 statement supplies the required lower-edge event -/

open Filter MeasureTheory Set Topology
open scoped BigOperators

noncomputable section

namespace BernoulliSection10Complex.SourceInputs

open BernoulliSection10.SourceInputs

open ShortRingAnchor

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem leastSingularValueInput_of_section3
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (hSource : Section3Inputs μ L)
    (N W : ℕ → ℕ) (σ : ∀ n, Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (hN : ∀ n, 0 < N n) (hW : ∀ n, 0 < W n) (hNtop : Tendsto N atTop atTop)
    (hσ : ∀ n, DoublyStochasticProfile (σ n))
    (χ κ c C : ℝ) (hχ : 0 < χ) (hκ : 0 < κ) (hκχ : κ < χ / 4)
    (hc : 0 < c) (hC : 0 < C)
    (hmax : ∀ n, maxEntryVariance (σ n) ≤ C / W n)
    (hband : ∀ n i j, scalarCyclicDistance i j ≤ W n → c / W n ≤ σ n i j ^ 2)
    (hhigh : ∀ᶠ n in atTop, (N n : ℝ) ^ (1 / 2 + χ) ≤ W n)
    (z : ℂ) :
    Theorem31LeastSingularValueInput (inputLaw μ)
      (shiftedSingularValueProcess (fun n ω => profileMatrix (σ n) ω) z)
      (sourceHardEdgeScale N W κ)
      (fun n => {ω | Real.exp (-(sourceHardEdgeScale N W κ n)) ≤
        SourceInputs.leastSingularValue (profileMatrix (σ n) ω - z • 1)}) := by
  letI := hμ.toIsProbabilityMeasure
  let E := fun n ω => squaredEntryMass (profileMatrix (σ n) ω) / (N n : ℝ)
  let good := fun n => {ω | Real.exp (-(sourceHardEdgeScale N W κ n)) ≤
    SourceInputs.leastSingularValue (profileMatrix (σ n) ω - z • 1)}
  have hE : ∀ n ω, 0 ≤ E n ω := by
    intro n ω
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      (Nat.cast_nonneg _)
  have hEi (n : ℕ) : Integrable (E n) (inputLaw μ) :=
    (profileMatrix_energy_integrable hμ (σ n)).div_const _
  have hEm (n : ℕ) : (∫ ω, E n ω ∂inputLaw μ) ≤ 1 := by
    dsimp only [E]
    rw [integral_div, integral_profileMatrix_energy hμ _ (hσ n),
      div_self (Nat.cast_ne_zero.mpr (hN n).ne')]
  have hbad : Tendsto (fun n => (inputLaw μ) (good n)ᶜ) atTop (𝓝 0) := by
    apply measure_tendsto_zero_of_energy_cutoffs (inputLaw μ) (fun n => (good n)ᶜ)
      E hE hEi hEm
    intro R hR
    obtain ⟨D, hD, hest⟩ := hSource.leastSingularValue hμ N W σ hN hW hNtop hσ
      χ κ c C (‖z‖ + 1) (Real.sqrt R) hχ hκ hκχ hc hC
      (by positivity) (Real.sqrt_pos.mpr hR) hmax hband hhigh
    have hcast := tendsto_natCast_comp_atTop hNtop
    have hpow : Tendsto (fun n => (N n : ℝ) ^ (-2 : ℝ)) atTop (𝓝 0) :=
      (tendsto_rpow_atTop_zero_of_neg (by norm_num)).comp hcast
    have hlarge : Tendsto (fun n => (N n : ℝ) ^ (1 + κ / 4)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 + κ / 4)).comp hcast
    have hexp : Tendsto (fun n => Real.exp (-((N n : ℝ) ^ (1 + κ / 4))))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def] using
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hlarge)
    have hreal : Tendsto (fun n => D * (N n : ℝ) ^ (-2 : ℝ) +
        Real.exp (-((N n : ℝ) ^ (1 + κ / 4)))) atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using (hpow.const_mul D).add hexp
    have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds (by simpa only [ENNReal.ofReal_zero] using hlim)
      (Eventually.of_forall fun _ => zero_le)
    filter_upwards [hest] with n hn
    apply (measure_mono ?_).trans
      (hn z (by linarith) ((N n : ℝ) ^ (-2 : ℝ))
        (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hN n)) _))
    intro ω hω
    have hleast : SourceInputs.leastSingularValue (profileMatrix (σ n) ω - z • 1) <
        Real.exp (-(sourceHardEdgeScale N W κ n)) := lt_of_not_ge hω.1
    refine ⟨?_, ?_⟩
    · rw [exp_neg_sourceHardEdgeScale N W κ n (hN n)] at hleast
      exact hleast.le
    · apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt hR.le, Real.sq_sqrt (Nat.cast_nonneg _)]
      exact (div_le_iff₀ (Nat.cast_pos.mpr (hN n))).mp hω.2
  apply theorem31LeastSingularValueInput_of_minimum hN
  exact ⟨hbad, fun _ _ hω => hω⟩

end BernoulliSection10Complex.SourceInputs
