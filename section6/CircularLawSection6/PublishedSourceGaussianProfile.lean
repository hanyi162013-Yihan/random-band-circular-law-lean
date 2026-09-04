import CircularLawSection6.PublishedCoreLocalInput
import CircularLawSection6.PublishedSection3GaussianProfile

/-! # Gaussian profile circular law without an assumed local CDF conclusion

The new source bundle calls the checked Section 3 density endpoints through
Section 5 and derives the local CDF comparison from Section 3's finite BBV
estimates on the actual models. BBV, Han, and finite Section 4/anchor source
data remain explicit; no Ginibre estimate is an input field.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5 CircularLawSections56.Section6
noncomputable section
set_option autoImplicit false

namespace CircularLawSection6.NoncompactProfile

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {νA νG : Measure ℂ}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure νA] [IsProbabilityMeasure νG]

structure GaussianProfilePublishedSources (μ : Measure Ω) (νA νG : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure νA] [IsProbabilityMeasure νG]
    (p : NoncompactProfile) (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) : Prop where
  coreSection34 : ∀ R : ℕ,
    (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)).PublishedSection34Input μ νA νG W
  coreLocal : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ R : ℕ,
    (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)).PublishedLocalInput
      (fun n => subsequenceCoreSize φ n + 2) (fun n => W (φ (n + 1))) (fun n => hW (φ (n + 1)))
  bbv : CircularLawSections56.Section5.PublishedSection3Concrete.BBVComparisonInput

theorem GaussianProfilePublishedSources.toPublishedSection3 (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (h : GaussianProfilePublishedSources μ νA νG p W hW) :
    GaussianProfilePublishedSection3Inputs μ νA νG p W where
  coreSection34 := h.coreSection34
  coreSection3 := by
    intro φ hφ R
    exact CoreRadiusBounds.PublishedLocalInput.toCanonical
      (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1))
      (fun n => subsequenceCoreSize φ n + 2) (fun n => W (φ (n + 1)))
      (fun n => hW (φ (n + 1))) (by positivity)
      (hWlim.comp (hφ.tendsto_atTop.comp (tendsto_add_atTop_nat 1))) (h.coreLocal φ hφ R)
  bbv := h.bbv

theorem gaussian_profile_circular_law_of_published_sources (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsource : GaussianProfilePublishedSources μ νA νG p W hW)
    (hHan : HanGaussianDenseInput) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) :=
  p.gaussian_profile_circular_law_of_published_section3 W hW hWlim
    (GaussianProfilePublishedSources.toPublishedSection3 p W hW hWlim hsource) hHan

end CircularLawSection6.NoncompactProfile
