import CircularLawSection6.BBVCoreSources
import CircularLawSection6.DenseProfileEndpoint

/-! # Profile circular law without a Ginibre squared-test source

The sparse branch uses actual local BBV comparisons and moving Ginibre
cutoff means. The dense branch uses the proved general Section 3 route.
The two branches are merged without any assumption on the limit of W/N.
The logarithmic Ginibre source is constructed by the proved Section 5
reference, not inferred from a bounded-cutoff comparison.
-/

open MeasureTheory Filter Topology TaoVuReplacement ShortRingAnchor
open CircularLawSections56.Section5 CircularLawSections56.Section6
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

private theorem bbv_profile_raw_bad_dimension (p : NoncompactProfile)
    {N M : ℕ} [NeZero N] [NeZero M] (hNM : N = M) (W : ℝ) (z : ℂ) (a ε : ℝ) :
    (gaussianProfileLaw N).real
        {ω | ε ≤ |matrixRawPotential (p.matrix N W ω - z • 1) - a|} =
      (gaussianProfileLaw M).real
        {ω | ε ≤ |matrixRawPotential (p.matrix M W ω - z • 1) - a|} := by
  subst M
  rfl

theorem profile_probability_along_sparse_subsequence_of_bbv_sources (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsource : GaussianProfileBBVCoreSources p W) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hsparse : Tendsto (fun n => W (φ n) / (φ n + 1 : ℕ)) atTop (𝓝 0)) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun n => gaussianProfileLaw (φ n + 1))
        (fun n ω => matrixRawPotential (p.matrix (φ n + 1) (W (φ n)) ω - z • 1))
        (circularRadialPotential ‖z‖) := by
  have hφ' : Tendsto (fun n => φ (n + 1)) atTop atTop :=
    hφ.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  have hdim : Tendsto (fun n => subsequenceCoreSize φ n + 2) atTop atTop := by
    apply ((tendsto_add_atTop_nat 1).comp hφ').congr'
    exact Eventually.of_forall fun n => (subsequenceCoreSize_dimension φ hφ n).symm
  have hs : Tendsto (fun n => W (φ (n + 1)) / (subsequenceCoreSize φ n + 2 : ℕ)) atTop (𝓝 0) := by
    apply (hsparse.comp (tendsto_add_atTop_nat 1)).congr'
    apply Eventually.of_forall
    intro n
    change W (φ (n + 1)) / ((φ (n + 1) + 1 : ℕ) : ℝ) =
      W (φ (n + 1)) / ((subsequenceCoreSize φ n + 2 : ℕ) : ℝ)
    rw [subsequenceCoreSize_dimension φ hφ n]
  have hSection5 (R : ℕ) : p.CanonicalCoreSection5Input (subsequenceCoreSize φ)
      (fun n => W (φ (n + 1))) (R + 1) :=
    CoreRadiusBounds.Section34Input.toCanonical
      (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)) W
      (by positivity) hW hWlim
      (GaussianProfileBBVCoreSources.coreSection34 p W hWlim hsource R) φ hφ
  have hp := p.sparse_profile_probability_of_bbv_section5 hsource.bbv
    (subsequenceCoreSize φ) hdim (fun n => W (φ (n + 1)))
    (fun n => hW (φ (n + 1))) (hWlim.comp hφ') hs hSection5
  filter_upwards [hp] with z hz
  apply (tendstoInProbabilityTri_shift_iff (fun n => gaussianProfileLaw (φ n + 1))
    (fun n ω => matrixRawPotential (p.matrix (φ n + 1) (W (φ n)) ω - z • 1))
    (circularRadialPotential ‖z‖) 1).mp
  intro ε hε
  apply (hz ε hε).congr'
  exact Eventually.of_forall fun n => p.bbv_profile_raw_bad_dimension
    (subsequenceCoreSize_dimension φ hφ n) (W (φ (n + 1))) z (circularRadialPotential ‖z‖) ε

theorem profile_spectral_limit_along_sparse_subsequence_of_bbv_sources (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsource : GaussianProfileBBVCoreSources p W) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hsparse : Tendsto (fun n => W (φ n) / (φ n + 1 : ℕ)) atTop (𝓝 0)) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix (φ n)
          (p.matrix (φ n + 1) (W (φ n)) (ω (φ n)).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) := by
  have hBC12 := CircularLawSections56.Section5.PublishedSection3Concrete.provedGinibreInput
    hsource.bbv
  have hrep := p.profile_ginibre_replacement_along_subsequence W φ hφ
    (fun z => circularRadialPotential ‖z‖)
    (p.profile_probability_along_sparse_subsequence_of_bbv_sources W hW hWlim hsource φ hφ hsparse)
    (ae_of_all _ fun z => ginibre_raw_of_bc12 hBC12 (fun n => n + 1)
      (tendsto_add_atTop_nat 1) z)
  intro f hf hc
  have hdiff := (tendstoInMeasure_iff_tri (Measure.infinitePi profileGinibrePairLaw) _ 0).1
    (hrep f hf hc)
  have hgin := (tendstoInMeasure_iff_tri (Measure.infinitePi profileGinibrePairLaw) _
    (∫ z, f z ∂circularMeasure)).1
    ((ginibre_spectral_of_bc12 hBC12 f hf hc).comp hφ.tendsto_atTop)
  apply (tendstoInMeasure_iff_tri (Measure.infinitePi profileGinibrePairLaw) _ _).2
  simpa only [esdDifference, Function.comp_apply, sub_add_cancel, zero_add] using
    hdiff.add (fun _ => Measure.infinitePi profileGinibrePairLaw) hgin

/-- Final actual-profile endpoint. Its source bundle contains only BBV
and the two Section 4 inputs; the Ginibre reference is proved internally. -/
theorem gaussian_profile_circular_law_of_bbv_core_sources (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsource : GaussianProfileBBVCoreSources p W) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) := by
  intro f hf hc
  apply tendstoInMeasure_of_sparse_dense_subsequences (Measure.infinitePi profileGinibrePairLaw)
    (fun n ω => realEsdTest (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
    (fun _ => ∫ z, f z ∂circularMeasure) (fun n => W n / (n + 1 : ℕ))
    (fun n => div_nonneg (hW n).le (Nat.cast_nonneg _))
  · intro φ hφ hsparse
    exact p.profile_spectral_limit_along_sparse_subsequence_of_bbv_sources W hW hWlim hsource
      φ hφ hsparse f hf hc
  · intro φ hφ hdense
    exact p.dense_profile_spectral_limit_of_section3 W φ hφ hdense
      hsource.bbv f hf hc

end CircularLawSection6.NoncompactProfile
