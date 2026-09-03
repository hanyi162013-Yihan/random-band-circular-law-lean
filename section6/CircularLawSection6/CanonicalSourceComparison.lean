import CircularLawSection6.AutomaticCorePartition
import CircularLawSection6.QuadraticBlockScale

/-! # Canonical core comparison from local Section 3 probability inputs

The only probabilistic inputs are local finite CDF comparison and the
Ginibre bounded-test singular law. Neither a full-matrix comparison nor
cutoff-expectation convergence is assumed. The initial non-fitting prefix
is removed and restored explicitly.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

def CanonicalCoreSection3Input (p : NoncompactProfile) (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (W : ℕ → ℝ) (R : ℝ) : Prop :=
  ∀ K : ℕ, ∀ hH : ∀ n, 0 < ⌊R * W (n + K)⌋₊,
    (∀ n, 2 * ⌊R * W (n + K)⌋₊ + 1 ≤ N (n + K)) →
    ∀ᵐ z ∂(volume : Measure ℂ), ∃ σ : Measure ℝ,
      IsProbabilityMeasure σ ∧ (∀ᵐ s ∂σ, 0 ≤ s) ∧ Integrable (fun s : ℝ => s ^ 2) σ ∧
      GinibreSquaredTestInput (fun n => ⟨N (n + K), NeZero.pos _⟩) z σ ∧
      (∀ M : ℕ → ℕ+,
        (∀ n, 2 * ⌊R * W (n + K)⌋₊ + 1 ≤ (M n : ℕ) ∧
          (M n : ℕ) ≤ 2 * quadraticBlockScale ⌊R * W (n + K)⌋₊) →
        CyclicGinibreCdfInput M (fun n => ⌊R * W (n + K)⌋₊)
          (fun n => p.coreRoutedAmplitude (N (n + K))
            (canonicalCoreBand ⌊R * W (n + K)⌋₊) ⌊R * W (n + K)⌋₊
            (canonicalCoreBand_width (hH n)) (canonicalCoreCenter _ (hH n)) (W (n + K))) z ∧
        GinibreSquaredTestInput M z σ)

theorem canonical_core_cutoff_comparison_of_section3 (p : NoncompactProfile)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (N n : ℝ)) atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) (hSection3 : p.CanonicalCoreSection3Input N W R)
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n =>
        (∫ ω, matrixCutoffPotential (p.unitCoreMatrix (N n) ⌊R * W n⌋₊ (W n) ω - z • 1) a
          ∂gaussianProfileLaw (N n)) -
        ∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) a
          ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 0) := by
  have hgeom := canonical_floor_core_eventually_fits N hN W hW hWlim hsparse hR
  obtain ⟨K, hK⟩ := eventually_atTop.1 hgeom
  have hH (n : ℕ) : 0 < ⌊R * W (n + K)⌋₊ := (hK (n + K) (by omega)).1
  have hfit (n : ℕ) : 2 * ⌊R * W (n + K)⌋₊ + 1 ≤ N (n + K) := by
    have h := (hK (n + K) (by omega)).2
    rwa [canonicalCoreBand_width (hH n)] at h
  have hcore := p.unitCore_cutoff_limit_of_local_inputs_ae
    (fun n => N (n + K)) (fun n => ⌊R * W (n + K)⌋₊)
    (fun n => quadraticBlockScale ⌊R * W (n + K)⌋₊)
    (fun n => canonicalCoreBand ⌊R * W (n + K)⌋₊)
    (fun n => canonicalCoreBand_width (hH n))
    (fun n => (canonicalCoreBand_width (hH n)).trans_le (hfit n))
    (fun n => quadraticBlockScale_fits _)
    (fun n => canonicalCoreCenter _ (hH n)) (fun n => rfl)
    (fun n => W (n + K))
    (quadraticBlockScale_ratio_tendsto _
      (floor_radius_atTop _ (hWlim.comp (tendsto_add_atTop_nat K)) hR)) ha
  filter_upwards [hcore, ginibre_fixedCutoff_mean_of_squared_test_ae (fun n => N (n + K)),
    hSection3 K hH hfit] with z hc hg hs
  obtain ⟨σ, hσ, hσpos, hσ2, hweak, hlocal⟩ := hs
  have hlim := (hc σ hσ hσpos hσ2 hlocal).sub (hg σ hσ hσpos hσ2 hweak a ha)
  simp only [sub_self] at hlim
  exact (tendsto_add_atTop_iff_nat K).mp hlim

end CircularLawSection6.NoncompactProfile
