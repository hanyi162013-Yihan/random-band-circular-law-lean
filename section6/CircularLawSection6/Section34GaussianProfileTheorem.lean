import CircularLawSection6.ClampedCoreSubsequence
import CircularLawSection6.GaussianProfileTheorem

/-! # Gaussian profile circular law with Section 5 called internally

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

structure GaussianProfileSection34Inputs (p : NoncompactProfile) (W : ℕ → ℝ) : Prop where
  coreSection34 : ∀ R : ℕ,
    (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)).Section34Input W
  coreSection3 : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ R : ℕ,
    p.CanonicalCoreSection3Input (fun n => subsequenceCoreSize φ n + 2)
      (fun n => W (φ (n + 1))) (R + 1)
  bbv : CircularLawSections56.Section5.PublishedSection3Concrete.BBVComparisonInput

theorem GaussianProfileSection34Inputs.toSourceInputs (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsource : p.GaussianProfileSection34Inputs W) : p.GaussianProfileSourceInputs W where
  coreSection5 := by
    intro φ hφ R
    exact CoreRadiusBounds.Section34Input.toCanonical
      (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)) W
      (by positivity) hW hWlim (hsource.coreSection34 R) φ hφ
  coreSection3 := hsource.coreSection3
  bbv := hsource.bbv

theorem gaussian_profile_circular_law_of_section34 (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsource : p.GaussianProfileSection34Inputs W) (hHan : HanGaussianDenseInput) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) :=
  p.gaussian_profile_circular_law W hW hWlim
    (GaussianProfileSection34Inputs.toSourceInputs p W hW hWlim hsource) hHan

end CircularLawSection6.NoncompactProfile
