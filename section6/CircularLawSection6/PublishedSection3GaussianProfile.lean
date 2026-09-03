import CircularLawSection6.PublishedSection3CoreEndpoint
import CircularLawSection6.Section34GaussianProfileTheorem
import CircularLawSection6.GaussianProfileTheorem

/-! # Gaussian profile circular law calling the published Section 3 theorem

The core probability limit is no longer an external premise. Its source
field consists only of Section 4's two finite quantitative estimates and
Section 3's short/calibration anchors for the constructed clamped core.
The verified Section 5 endpoint is invoked and transported internally.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option autoImplicit false

namespace CircularLawSection6.NoncompactProfile

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {νA νG : Measure ℂ}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure νA] [IsProbabilityMeasure νG]

structure GaussianProfilePublishedSection3Inputs (μ : Measure Ω) (νA νG : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure νA] [IsProbabilityMeasure νG]
    (p : NoncompactProfile) (W : ℕ → ℝ) : Prop where
  coreSection34 : ∀ R : ℕ,
    (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)).PublishedSection34Input μ νA νG W
  coreSection3 : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ R : ℕ,
    p.CanonicalCoreSection3Input (fun n => subsequenceCoreSize φ n + 2)
      (fun n => W (φ (n + 1))) (R + 1)
  ginibreRaw : ∀ᵐ z ∂(volume : Measure ℂ),
    TendstoInProbabilityTri (fun n => cyclicAtomLaw (n + 1) circularComplexGaussian)
      (fun n ω => matrixRawPotential (ginibreMatrix (n + 1) ω - z • 1)) (circularRadialPotential ‖z‖)
  ginibreNegative : ∀ᵐ z ∂(volume : Measure ℂ), ∃ q : ℝ, 0 < q ∧
    BC12GinibreNegativeMomentTightnessTri (fun n => n + 1) z q
  ginibreSpectral : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
    TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
      (fun n ω => realEsdTest (cyclicPhysicalMatrix n (ginibreMatrix (n + 1) (ω n).2)) f)
      atTop (fun _ => ∫ z, f z ∂circularMeasure)

theorem GaussianProfilePublishedSection3Inputs.toSection34 (p : NoncompactProfile)
    (W : ℕ → ℝ) (h : GaussianProfilePublishedSection3Inputs μ νA νG p W) :
    p.GaussianProfileSection34Inputs W where
  coreSection34 R := CoreRadiusBounds.PublishedSection34Input.toSection34
    (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)) W (h.coreSection34 R)
  coreSection3 := h.coreSection3
  ginibreRaw := h.ginibreRaw
  ginibreNegative := h.ginibreNegative
  ginibreSpectral := h.ginibreSpectral

theorem gaussian_profile_circular_law_of_published_section3 (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsource : GaussianProfilePublishedSection3Inputs μ νA νG p W)
    (hHan : HanGaussianDenseInput) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) :=
  p.gaussian_profile_circular_law_of_section34 W hW hWlim
    (GaussianProfilePublishedSection3Inputs.toSection34 p W hsource) hHan

end CircularLawSection6.NoncompactProfile
