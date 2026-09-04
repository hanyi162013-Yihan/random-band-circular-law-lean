import CircularLawSection6.VerifiedCorePressure

/-! Public-boundary regressions: neither the concrete Gaussian core nor the
full profile endpoint receives a pressure or Gaussian-limit certificate. -/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSection6
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput)

noncomputable section
set_option autoImplicit false
set_option warningAsError true

example {p : NoncompactProfile} {R : ℝ} (B : CoreRadiusBounds p R) (W : ℕ → ℝ) :
    B.ConcreteSection4Input W := B.verifiedConcreteSection4Input W

example (p : NoncompactProfile) (W : ℕ → ℝ)
    (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop) (hBBV : BBVComparisonInput) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) :=
  p.gaussian_profile_circular_law_of_bbv W hW hWlim hBBV

#check @CoreRadiusBounds.verifiedConcreteSection4Input
#check @NoncompactProfile.gaussian_profile_circular_law_of_bbv
