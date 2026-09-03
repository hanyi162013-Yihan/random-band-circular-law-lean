import CircularLawSection6.CanonicalSourceComparison
import CircularLawSection6.FinitePrefixCoreBridge
import CircularLawSection6.ProfileProbability

/-! # Sparse noncompact Gaussian profiles: source-level probability endpoint

The Section 3 assumptions concern only local finite-dimensional CDFs and
Ginibre bounded tests. The Section 5 input is the literal core probability
endpoint. No raw-core mean, full-matrix cutoff comparison, concentration,
or tail error is left as an assumption in this assembly.
-/

open MeasureTheory Filter Topology
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

theorem sparse_profile_mean_of_section3_section5 (p : NoncompactProfile)
    (size : ℕ → ℕ) (hsize : Tendsto (fun n => size n + 2) atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (size n + 2 : ℕ)) atTop (𝓝 0))
    (hSection5 : ∀ R : ℕ, p.CanonicalCoreSection5Input size W (R + 1))
    (hSection3 : ∀ R : ℕ, p.CanonicalCoreSection3Input (fun n => size n + 2) W (R + 1))
    (hGinibre : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun n => cyclicAtomLaw (size n + 2) circularComplexGaussian)
        (fun n ω => matrixRawPotential (ginibreMatrix (size n + 2) ω - z • 1)) (circularRadialPotential ‖z‖))
    (hNegative : ∀ᵐ z ∂(volume : Measure ℂ), ∃ q : ℝ, 0 < q ∧
      BC12GinibreNegativeMomentTightnessTri (fun n => size n + 2) z q) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => (∫ ω, p.rawProfileLogDet (size n + 2) (W n) z ω
        ∂gaussianProfileLaw (size n + 2)) / (size n + 2 : ℕ))
        atTop (𝓝 (circularRadialPotential ‖z‖)) := by
  apply p.sparse_profile_mean_of_core_and_reference_inputs
    (fun n => size n + 2) hsize W hW hWlim hsparse ?_ ?_ hGinibre hNegative
  · intro R
    exact p.canonical_core_raw_mean_of_eventual_section5 size hsize W hW hWlim hsparse
      (by positivity) (hSection5 R)
  · intro R
    exact p.canonical_core_cutoff_comparison_of_section3 (fun n => size n + 2) hsize W hW hWlim hsparse
      (by positivity) (hSection3 R) (p.referenceCoreCutoff_pos R)

theorem sparse_profile_probability_of_section3_section5 (p : NoncompactProfile)
    (size : ℕ → ℕ) (hsize : Tendsto (fun n => size n + 2) atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (size n + 2 : ℕ)) atTop (𝓝 0))
    (hSection5 : ∀ R : ℕ, p.CanonicalCoreSection5Input size W (R + 1))
    (hSection3 : ∀ R : ℕ, p.CanonicalCoreSection3Input (fun n => size n + 2) W (R + 1))
    (hGinibre : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun n => cyclicAtomLaw (size n + 2) circularComplexGaussian)
        (fun n ω => matrixRawPotential (ginibreMatrix (size n + 2) ω - z • 1)) (circularRadialPotential ‖z‖))
    (hNegative : ∀ᵐ z ∂(volume : Measure ℂ), ∃ q : ℝ, 0 < q ∧
      BC12GinibreNegativeMomentTightnessTri (fun n => size n + 2) z q) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun n => gaussianProfileLaw (size n + 2))
        (fun n ω => matrixRawPotential (p.matrix (size n + 2) (W n) ω - z • 1))
        (circularRadialPotential ‖z‖) := by
  filter_upwards [p.sparse_profile_mean_of_section3_section5 size hsize W hW hWlim hsparse
    hSection5 hSection3 hGinibre hNegative] with z hz
  exact p.full_profile_probability_of_mean (fun n => size n + 2) hsize W z hz

end CircularLawSection6.NoncompactProfile
