import CircularLawSection6.PublishedCoreGeometry
import CircularLawSection6.CanonicalSourceComparison

/-! # Replacing the core CDF input by actual published comparison sources

The only local comparison fields below are BBV for the two explicitly built
Gaussian models. Core weights, dimension growth, polynomial bandwidth, finite
probability spaces, and CDF convergence are constructed internally. The common
limiting Ginibre singular law remains the named classical bounded-test input.
-/

open MeasureTheory Filter Topology ShortRingAnchor Arxiv2410V3
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.CoreRadiusBounds

variable {p : NoncompactProfile} {R : ℝ}

def floorLocalWeights (B : CoreRadiusBounds p R) (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (K : ℕ)
    (hH : ∀ n, 0 < ⌊R * W (n + K)⌋₊)
    (hfit : ∀ n, 2 * ⌊R * W (n + K)⌋₊ + 1 ≤ N (n + K)) (n : ℕ) :
    AdmissibleWeights ⌊R * W (n + K)⌋₊ (B.lower / B.upper) (B.upper / B.lower) :=
  B.localSection3Weights (N (n + K)) ⌊R * W (n + K)⌋₊ (hH n) (hfit n)
    (W (n + K)) (hW (n + K)) (Nat.floor_le (mul_nonneg B.radius_nonneg (hW _).le))

def PublishedLocalInput (B : CoreRadiusBounds p R) (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) : Prop :=
  ∀ K : ℕ, ∀ hH : ∀ n, 0 < ⌊R * W (n + K)⌋₊,
    ∀ hfit : ∀ n, 2 * ⌊R * W (n + K)⌋₊ + 1 ≤ N (n + K),
    ∀ᵐ z ∂(volume : Measure ℂ), ∃ σ : Measure ℝ,
      IsProbabilityMeasure σ ∧ (∀ᵐ s ∂σ, 0 ≤ s) ∧ Integrable (fun s : ℝ => s ^ 2) σ ∧
      GinibreSquaredTestInput (fun n => ⟨N (n + K), NeZero.pos _⟩) z σ ∧
      ∃ comparisonConstant : ℝ, ∀ M : ℕ → ℕ+,
        ∀ hwindow : ∀ n, 2 * ⌊R * W (n + K)⌋₊ + 1 ≤ (M n : ℕ) ∧
          (M n : ℕ) ≤ 2 * quadraticBlockScale ⌊R * W (n + K)⌋₊,
        GinibreSquaredTestInput M z σ ∧
        (∀ n u, CanonicalBBVAt
          (publishedJointCyclicModel (B.floorLocalWeights N W hW K hH hfit n) (hwindow n).1) z
          (spectralParameter u (localBulkHeight (1 / 8) (M n)))
          (B.floorLocalWeights N W hW K hH hfit n).bandwidthParameter
          (gaussianSection3ComparisonConstant comparisonConstant)) ∧
        (∀ n u, CanonicalBBVAt (publishedJointDenseModel (M n) ⌊R * W (n + K)⌋₊) z
          (spectralParameter u (localBulkHeight (1 / 8) (M n))) (M n)
          (gaussianSection3ComparisonConstant comparisonConstant))

theorem PublishedLocalInput.toCanonical (B : CoreRadiusBounds p R)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ) (hW : ∀ n, 0 < W n)
    (hR : 0 < R) (hWlim : Tendsto W atTop atTop)
    (h : B.PublishedLocalInput N W hW) : p.CanonicalCoreSection3Input N W R := by
  intro K hH hfit
  filter_upwards [h K hH hfit] with z hz
  obtain ⟨σ, hσ, hpos, hsecond, hweak, cc, hlocal⟩ := hz
  refine ⟨σ, hσ, hpos, hsecond, hweak, ?_⟩
  intro M hwindow
  obtain ⟨hweakM, hbbvA, hbbvG⟩ := hlocal M hwindow
  have hHlim : Tendsto (fun n => ⌊R * W (n + K)⌋₊) atTop atTop :=
    floor_radius_atTop _ (hWlim.comp (tendsto_add_atTop_nat K)) hR
  have hMlim : Tendsto (fun n => (M n : ℕ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by have hf := (hwindow n).1; omega) hHlim
  have hscaleA := cyclic_bandwidth_eighth_power_eventually
    (B.floorLocalWeights N W hW K hH hfit) hHlim
    (fun n => (hwindow n).1) (fun n => (hwindow n).2)
  have hscaleG : ∀ᶠ n in atTop, (M n : ℝ) ^ (1 / 8 : ℝ) ≤ M n := by
    apply Eventually.of_forall
    intro n
    simpa only [show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] using
      dense_bandwidth_ge_half_power (M n).pos (by norm_num : (1 / 4 : ℝ) ≤ 2)
  have hcdf := cyclicGinibreCdfInput_of_published_models M (fun n => ⌊R * W (n + K)⌋₊)
    (B.floorLocalWeights N W hW K hH hfit) (fun n => (hwindow n).1) hMlim z cc
    (by norm_num : (0 : ℝ) < 1 / 8) hscaleA hscaleG hbbvA hbbvG
  refine ⟨?_, hweakM⟩
  exact hcdf

end CircularLawSection6.CoreRadiusBounds
