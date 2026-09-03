import CircularLawSection6.PublishedConcreteLocalInput
import CircularLawSection6.PublishedConcreteCoreEndpoint
import CircularLawSection6.Section34GaussianProfileTheorem

/-! # Gaussian-profile endpoint with uniform local literature sources

No local CDF conclusion or model-by-model BBV certificate is assumed.
The core-local field of the published source bundle is constructed from
uniform BBV and the single classical actual-Ginibre bounded-test limit.
The short-ring and calibration-prefix anchors are also constructed from
uniform BBV and BC12 for the actual core weights. Only the two Section 4
pressure sources and the named classical Ginibre/Han sources remain explicit.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput BC12GinibreInput)
noncomputable section
set_option autoImplicit false

namespace CircularLawSection6.NoncompactProfile

structure GaussianProfileConcreteSources (p : NoncompactProfile) (W : ℕ → ℝ) : Prop where
  bbv : BBVComparisonInput
  bc12 : BC12GinibreInput
  ginibreSquared : ClassicalGinibreSquaredTestInput
  coreSection4 : ∀ R : ℕ,
    (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)).ConcreteSection4Input W
  ginibreRaw : ∀ᵐ z ∂(volume : Measure ℂ),
    TendstoInProbabilityTri (fun n => cyclicAtomLaw (n + 1) circularComplexGaussian)
      (fun n ω => matrixRawPotential (ginibreMatrix (n + 1) ω - z • 1)) (circularRadialPotential ‖z‖)
  ginibreNegative : ∀ᵐ z ∂(volume : Measure ℂ), ∃ q : ℝ, 0 < q ∧
    BC12GinibreNegativeMomentTightnessTri (fun n => n + 1) z q
  ginibreSpectral : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
    TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
      (fun n ω => realEsdTest (cyclicPhysicalMatrix n (ginibreMatrix (n + 1) (ω n).2)) f)
      atTop (fun _ => ∫ z, f z ∂circularMeasure)

theorem GaussianProfileConcreteSources.toSection34 (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (h : GaussianProfileConcreteSources p W) :
    p.GaussianProfileSection34Inputs W where
  coreSection34 := by
    intro R
    exact CoreRadiusBounds.ConcreteSection4Input.toSection34
      (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1))
      W (by positivity) hWlim h.bbv (h.coreSection4 R)
  coreSection3 := by
    intro φ hφ R
    exact CoreRadiusBounds.canonicalCoreSection3Input_of_concrete_literature
      (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1))
      (fun n => subsequenceCoreSize φ n + 2) (fun n => W (φ (n + 1)))
      (fun n => hW (φ (n + 1))) (by positivity)
      (hWlim.comp (hφ.tendsto_atTop.comp (tendsto_add_atTop_nat 1))) h.bbv h.ginibreSquared
  ginibreRaw := h.ginibreRaw
  ginibreNegative := h.ginibreNegative
  ginibreSpectral := h.ginibreSpectral

theorem gaussian_profile_circular_law_of_concrete_sources (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsource : GaussianProfileConcreteSources p W)
    (hHan : HanGaussianDenseInput) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) :=
  p.gaussian_profile_circular_law_of_section34 W hW hWlim
    (GaussianProfileConcreteSources.toSection34 p W hW hWlim hsource) hHan

end CircularLawSection6.NoncompactProfile
