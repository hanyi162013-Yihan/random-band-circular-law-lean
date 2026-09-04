import CircularLawSection6.VerifiedPointwiseProfileEndpoint
import CircularLawSection6.CoreNormalizationPointwise

/-! Signature regression for the fixed-shift Section 6 endpoint. -/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSection6
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput)

noncomputable section
set_option autoImplicit false
set_option warningAsError true

example (p : NoncompactProfile) (W : ℕ → ℝ)
    (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hBBV : BBVComparisonInput) :
    ∀ z : ℂ, TendstoInProbabilityTri (fun n => gaussianProfileLaw (n + 1))
      (fun n ω => matrixRawPotential (p.matrix (n + 1) (W n) ω - z • 1))
      (circularRadialPotential ‖z‖) := by
  intro z
  exact p.gaussian_profile_logPotential_of_bbv W hW hWlim hBBV z

#check @NoncompactProfile.gaussian_profile_logPotential_of_bbv
#check @NoncompactProfile.gaussian_profile_circular_law_of_pointwise_bbv
#check @NoncompactProfile.profile_probability_along_sparse_subsequence_of_bbv_at
#check @CoreRadiusBounds.verifiedClampedLogPotential_at
#check @CoreRadiusBounds.canonical_core_cutoff_comparison_of_bbv_at
#check @NoncompactProfile.gaussian_core_cutoff_normalization_error_at
