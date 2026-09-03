import CircularLawSection6.UniformCyclicSourceBridge
import CircularLawSection6.PhysicalCutoffTransport

/-! # Compact cutoff limits from the precise finite-probability inputs

All-length expectation convergence is now a conclusion, not a premise.
The inputs are exactly the local squared-singular CDF comparison to finite
Ginibre and the reference bounded-test singular-law limit. The actual
periodicization, weighted averaging and paper-model transport are proved.
-/

open MeasureTheory Filter Topology
open CircularLawSection4
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem fullBlock_cutoff_limit_of_section3_inputs_ae
    (q H m₀ : ℕ → ℕ) (len : ∀ n, Fin (q n) → ℕ)
    [∀ n j, NeZero (len n j)] [∀ n, NeZero (∑ j, len n j)]
    (hm₀ : ∀ n, 0 < m₀ n) (hfit : ∀ n, 2 * H n + 1 ≤ m₀ n)
    (hsize : ∀ n j, m₀ n ≤ len n j ∧ len n j ≤ 2 * m₀ n)
    (b : ∀ n, Fin (2 * H n + 1) → ℂ) (hb : ∀ n, ∑ s, ‖b n s‖ ^ 2 = 1)
    (hratio : Tendsto (fun n => (H n : ℝ) / m₀ n) atTop (𝓝 0)) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ σ : Measure ℝ, IsProbabilityMeasure σ →
      (∀ᵐ s ∂σ, 0 ≤ s) → Integrable (fun s : ℝ => s ^ 2) σ →
      (∀ M : ℕ → ℕ+, (∀ n, m₀ n ≤ (M n : ℕ) ∧ (M n : ℕ) ≤ 2 * m₀ n) →
        CyclicGinibreCdfInput M H b z ∧ GinibreSquaredTestInput M z σ) →
      Tendsto (fun n => ∫ ω, matrixCutoffPotential
        (routedBandMatrix (fullBlockRoute (len n) (H n)) (b n) ω - z • 1) a
          ∂Measure.pi (fun _ : ((j : Fin (q n)) × Fin (len n j)) × Fin (2 * H n + 1) => circularComplexGaussian))
        atTop (𝓝 (∫ s, Real.log (max s a) ∂σ)) := by
  filter_upwards [cyclicBlock_all_lengths_of_source_inputs_ae H m₀ hm₀ hfit b hb,
    fullBlock_expected_cutoff_limit_of_all_lengths q H m₀ len hm₀ hsize
      (fun n j => (hfit n).trans (hsize n j).1) b hb circularComplexGaussian
      circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment hratio ha]
    with z hc hf
  intro σ hσ hσpos hσ2 hsource
  exact hf (∫ s, Real.log (max s a) ∂σ) (hc σ hσ hσpos hσ2 hsource a ha)

theorem paperBand_cutoff_limit_of_section3_inputs_ae
    (q H m₀ d : ℕ → ℕ) (len : ∀ n, Fin (q n) → ℕ)
    [∀ n j, NeZero (len n j)] [∀ n, NeZero (∑ j, len n j)]
    (hm₀ : ∀ n, 0 < m₀ n) (hfit : ∀ n, 2 * H n + 1 ≤ m₀ n)
    (hsize : ∀ n j, m₀ n ≤ len n j ∧ len n j ≤ 2 * m₀ n)
    (hwidth : ∀ n, d n + 2 = 2 * H n + 1)
    (center : ∀ n, Fin (d n + 1)) (hcenter : ∀ n, (center n).val = H n)
    (b : ∀ n, Fin (2 * H n + 1) → ℂ) (hb : ∀ n, ∑ s, ‖b n s‖ ^ 2 = 1)
    (hratio : Tendsto (fun n => (H n : ℝ) / m₀ n) atTop (𝓝 0)) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ σ : Measure ℝ, IsProbabilityMeasure σ →
      (∀ᵐ s ∂σ, 0 ≤ s) → Integrable (fun s : ℝ => s ^ 2) σ →
      (∀ M : ℕ → ℕ+, (∀ n, m₀ n ≤ (M n : ℕ) ∧ (M n : ℕ) ≤ 2 * m₀ n) →
        CyclicGinibreCdfInput M H b z ∧ GinibreSquaredTestInput M z σ) →
      Tendsto (fun n => ∫ η, matrixCutoffPotential
        (paperIndicatorX (∑ j, len n j) (d n) (center n) (fun k => b n (finCongr (hwidth n) k)) η - z • 1) a
          ∂paperIndicatorSampleMeasure (∑ j, len n j) (d n) circularComplexGaussian)
        atTop (𝓝 (∫ s, Real.log (max s a) ∂σ)) := by
  have htransport := ae_all_iff.2 (fun n => fullBlock_expected_cutoff_eq_paper_ae
    (len n) (d n) (H n) (hwidth n) (center n) (hcenter n) (b n) circularComplexGaussian)
  filter_upwards [fullBlock_cutoff_limit_of_section3_inputs_ae q H m₀ len hm₀ hfit hsize b hb hratio ha,
    htransport] with z hz heq
  intro σ hσ hσpos hσ2 hsource
  apply (hz σ hσ hσpos hσ2 hsource).congr'
  exact Eventually.of_forall fun n => heq n a ha

end CircularLawSection6
