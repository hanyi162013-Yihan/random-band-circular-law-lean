import ShortRingAnchor.BC12.ScalarConcentration

/-!
# Theorem 3.1: remove the Hilbert--Schmidt cutoff using tightness

For Proposition 3.6 only convergence of the bad-event probability to zero is
needed. Therefore the published truncated least-singular-value estimate does
not require a new law of large numbers for the Hilbert--Schmidt norm. Uniform
second moments give tightness by Markov; first let the dimension tend to
infinity at a fixed cutoff, then let the cutoff grow.
-/

open Filter Set MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace ShortRingAnchor

/-- Theorem 3.1 to Proposition 3.6: an abstract, internally proved cutoff-removal
lemma with the correct two-limit quantifier order. -/
theorem probability_tendsto_zero_of_truncated_and_tight
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {bad : ℕ → Set Omega} {Q : ℕ → Omega → ℝ}
    (htight : BoundedInProbability mu Q)
    (htruncated : ∀ K : ℝ, 0 < K →
      Tendsto (fun n => mu (bad n ∩ {sample | ‖Q n sample‖ ≤ K})) atTop (nhds 0)) :
    Tendsto (fun n => mu (bad n)) atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := ENNReal.half_pos (ne_of_gt hepsilon)
  obtain ⟨K, hK, htail⟩ := htight (epsilon / 2) hhalf
  have hsmall := ENNReal.tendsto_nhds_zero.mp (htruncated K hK) (epsilon / 2) hhalf
  filter_upwards [htail, hsmall] with n hnTail hnSmall
  have hcover : bad n ⊆
      (bad n ∩ {sample | ‖Q n sample‖ ≤ K}) ∪ {sample | K < ‖Q n sample‖} := by
    intro sample hsample
    by_cases hQ : ‖Q n sample‖ ≤ K
    · exact Or.inl ⟨hsample, hQ⟩
    · exact Or.inr (lt_of_not_ge hQ)
  calc
    mu (bad n) ≤ mu (bad n ∩ {sample | ‖Q n sample‖ ≤ K}) +
        mu {sample | K < ‖Q n sample‖} :=
      (measure_mono hcover).trans (measure_union_le _ _)
    _ ≤ epsilon / 2 + epsilon / 2 := add_le_add hnSmall hnTail.le
    _ = epsilon := ENNReal.add_halves epsilon

/-- Theorem 3.1 cutoff removal from a uniform nonnegative expectation bound.
Apply this to `Q = HS(X)^2/N`; the matrix moment identity is proved elsewhere
in this project. No fixed-cutoff Hilbert--Schmidt concentration is assumed. -/
theorem probability_tendsto_zero_of_truncated_and_mean_bound
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {bad : ℕ → Set Omega} {Q : ℕ → Omega → ℝ} {C : ℝ}
    (hint : ∀ n, Integrable (Q n) mu)
    (hnonneg : ∀ n sample, 0 ≤ Q n sample)
    (hmean : ∀ n, ∫ sample, Q n sample ∂mu ≤ C)
    (htruncated : ∀ K : ℝ, 0 < K →
      Tendsto (fun n => mu (bad n ∩ {sample | Q n sample ≤ K})) atTop (nhds 0)) :
    Tendsto (fun n => mu (bad n)) atTop (nhds 0) := by
  apply probability_tendsto_zero_of_truncated_and_tight
    (BC12.boundedInProbability_of_nonneg_integral_bound hint hnonneg hmean)
  intro K hK
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _ _)] using htruncated K hK

end ShortRingAnchor
