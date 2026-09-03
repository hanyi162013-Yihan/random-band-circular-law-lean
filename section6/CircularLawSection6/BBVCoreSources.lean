import CircularLawSection6.MovingGinibreCore
import CircularLawSection6.PublishedConcreteLocalInput
import CircularLawSection6.GinibreReducedSources

/-! # Actual local core comparisons from uniform BBV alone

The local finite Gaussian models, their exact bandwidths and the finite
CDF comparison are constructed before calling the moving-reference core
theorem. No bounded-test Ginibre singular law is retained. The separate
raw logarithmic reference source remains explicit in the reduced bundle.
-/

open MeasureTheory Filter Topology ShortRingAnchor Arxiv2410V3
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete
  (BBVComparisonInput canonicalBBVAt_mono)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6
namespace CoreRadiusBounds

variable {p : NoncompactProfile} {R : ℝ}

theorem localCdf_of_bbv (B : CoreRadiusBounds p R)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ) (hW : ∀ n, 0 < W n)
    (hR : 0 < R) (hWlim : Tendsto W atTop atTop) (hBBV : BBVComparisonInput)
    (K : ℕ) (hH : ∀ n, 0 < ⌊R * W (n + K)⌋₊)
    (hfit : ∀ n, 2 * ⌊R * W (n + K)⌋₊ + 1 ≤ N (n + K))
    (z : ℂ) (M : ℕ → ℕ+)
    (hwindow : ∀ n, 2 * ⌊R * W (n + K)⌋₊ + 1 ≤ (M n : ℕ) ∧
      (M n : ℕ) ≤ 2 * quadraticBlockScale ⌊R * W (n + K)⌋₊) :
    CyclicGinibreCdfInput M (fun n => ⌊R * W (n + K)⌋₊)
      (fun n => p.coreRoutedAmplitude (N (n + K))
        (canonicalCoreBand ⌊R * W (n + K)⌋₊) ⌊R * W (n + K)⌋₊
        (canonicalCoreBand_width (hH n)) (canonicalCoreCenter _ (hH n)) (W (n + K))) z := by
  obtain ⟨C, _hCpos, hC⟩ := hBBV
  have hHlim : Tendsto (fun n => ⌊R * W (n + K)⌋₊) atTop atTop :=
    floor_radius_atTop _ (hWlim.comp (tendsto_add_atTop_nat K)) hR
  have hMlim : Tendsto (fun n => (M n : ℕ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by have := (hwindow n).1; omega) hHlim
  have hscaleA := cyclic_bandwidth_eighth_power_eventually
    (B.floorLocalWeights N W hW K hH hfit) hHlim
    (fun n => (hwindow n).1) (fun n => (hwindow n).2)
  have hscaleG : ∀ᶠ n in atTop, (M n : ℝ) ^ (1 / 8 : ℝ) ≤ M n := by
    apply Eventually.of_forall
    intro n
    simpa only [show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] using
      dense_bandwidth_ge_half_power (M n).pos (by norm_num : (1 / 4 : ℝ) ≤ 2)
  apply cyclicGinibreCdfInput_of_published_models M (fun n => ⌊R * W (n + K)⌋₊)
    (B.floorLocalWeights N W hW K hH hfit) (fun n => (hwindow n).1) hMlim z C
    (by norm_num : (0 : ℝ) < 1 / 8) hscaleA hscaleG
  · intro n u
    have hη := publishedLocal_spectralParameter_im_pos (M n) u
    exact canonicalBBVAt_mono
      (hC (cyclicGinibreJointSample (M n) ⌊R * W (n + K)⌋₊) ℂ
        (cyclicGinibreJointLaw (M n) ⌊R * W (n + K)⌋₊) circularComplexGaussian
        (M n) (M n).pos
        (publishedJointCyclicModel (B.floorLocalWeights N W hW K hH hfit n) (hwindow n).1)
        _ (cyclicVarianceProfile_isBandwidth
          (B.floorLocalWeights N W hW K hH hfit n) (hwindow n).1) z _ hη)
      (B.floorLocalWeights N W hW K hH hfit n).bandwidthParameter_pos hη
      (le_max_left _ _)
  · intro n u
    have hη := publishedLocal_spectralParameter_im_pos (M n) u
    exact canonicalBBVAt_mono
      (hC (cyclicGinibreJointSample (M n) ⌊R * W (n + K)⌋₊) ℂ
        (cyclicGinibreJointLaw (M n) ⌊R * W (n + K)⌋₊) circularComplexGaussian
        (M n) (M n).pos (publishedJointDenseModel (M n) ⌊R * W (n + K)⌋₊)
        _ (denseVarianceProfile_isBandwidth (M n).pos) z _ hη)
      (by positivity) hη (le_max_left _ _)

theorem canonical_core_cutoff_comparison_of_bbv (B : CoreRadiusBounds p R)
    (hBBV : BBVComparisonInput)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (N n : ℝ)) atTop (𝓝 0))
    (hR : 0 < R) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n =>
        (∫ ω, matrixCutoffPotential (p.unitCoreMatrix (N n) ⌊R * W n⌋₊ (W n) ω - z • 1) a
          ∂gaussianProfileLaw (N n)) -
        ∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) a
          ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 0) :=
  p.canonical_core_cutoff_comparison_of_local_cdf hBBV N hN W hW hWlim hsparse hR
    (fun K hH hfit => ae_of_all _ fun z M hwindow =>
      B.localCdf_of_bbv N W hW hR hWlim hBBV K hH hfit z M hwindow) ha

end CoreRadiusBounds
namespace NoncompactProfile

/-- Both Gaussian limit fields are discharged by the proved Section 5 reference.
Only BBV and the concrete Section 4 pressure inputs remain. -/
structure GaussianProfileBBVCoreSources (p : NoncompactProfile) (W : ℕ → ℝ) : Prop where
  bbv : BBVComparisonInput
  coreSection4 : ∀ R : ℕ,
    (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)).ConcreteSection4Input W

theorem GaussianProfileBBVCoreSources.coreSection34 (p : NoncompactProfile)
    (W : ℕ → ℝ) (hWlim : Tendsto W atTop atTop)
    (h : GaussianProfileBBVCoreSources p W) (R : ℕ) :
    (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)).Section34Input W :=
  CoreRadiusBounds.ConcreteSection4Input.toSection34
    (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1))
    W (by positivity) hWlim h.bbv
    (h.coreSection4 R)

/-- Sparse actual-profile probability convergence, with local comparisons
constructed from BBV instead of an assumed limiting singular law. -/
theorem sparse_profile_probability_of_bbv_section5 (p : NoncompactProfile)
    (hBBV : BBVComparisonInput)
    (size : ℕ → ℕ) (hsize : Tendsto (fun n => size n + 2) atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (size n + 2 : ℕ)) atTop (𝓝 0))
    (hSection5 : ∀ R : ℕ, p.CanonicalCoreSection5Input size W (R + 1)) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun n => gaussianProfileLaw (size n + 2))
        (fun n ω => matrixRawPotential (p.matrix (size n + 2) (W n) ω - z • 1))
        (circularRadialPotential ‖z‖) := by
  have hmean := p.sparse_profile_mean_of_core_and_reference_inputs
    (fun n => size n + 2) hsize W hW hWlim hsparse
    (fun R => p.canonical_core_raw_mean_of_eventual_section5 size hsize W hW hWlim hsparse
      (by positivity) (hSection5 R))
    (fun R => CoreRadiusBounds.canonical_core_cutoff_comparison_of_bbv
      (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1))
      hBBV (fun n => size n + 2) hsize W hW hWlim hsparse (by positivity)
      (p.referenceCoreCutoff_pos R))
    (ae_of_all _ fun z => ginibre_raw_of_bc12
      (CircularLawSections56.Section5.PublishedSection3Concrete.provedGinibreInput hBBV)
      (fun n => size n + 2) hsize z)
    (ae_of_all _ fun z => ⟨1 / 128, by norm_num,
      ginibre_negative_of_bbv hBBV (fun n => size n + 2) hsize z⟩)
  filter_upwards [hmean] with z hz
  exact p.full_profile_probability_of_mean (fun n => size n + 2) hsize W z hz

end NoncompactProfile
end CircularLawSection6
