import CircularLawSection6.BBVProfileEndpoint
import CircularLawSection6.GinibreBBVConsequences

/-! # Actual profile circular law with no independent Ginibre source

The remaining input bundle contains the uniform BBV literature result and
the concrete Section 4 pressure inputs. The logarithmic Ginibre reference,
its negative moments, its spectral limit, and the moving-size local cutoff
comparison are constructed by proved adapters. No Han theorem, Ginibre
raw-log limit, or limiting squared-singular-value test law is a field here.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput)

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

structure GaussianProfileBBVSources (p : NoncompactProfile) (W : ℕ → ℝ) : Prop where
  bbv : BBVComparisonInput
  coreSection4 : ∀ R : ℕ,
    (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)).ConcreteSection4Input W

theorem GaussianProfileBBVSources.toCoreSources
    (p : NoncompactProfile) (W : ℕ → ℝ) (h : GaussianProfileBBVSources p W) :
    GaussianProfileBBVCoreSources p W where
  bbv := h.bbv
  coreSection4 := h.coreSection4

/-- The actual Gaussian profile ESD converges against every continuous
compactly supported test, for arbitrary positive bandwidth tending to
infinity. No separate Ginibre limit is assumed. -/
theorem gaussian_profile_circular_law_of_bbv_sources (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsource : GaussianProfileBBVSources p W) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) :=
  p.gaussian_profile_circular_law_of_bbv_core_sources W hW hWlim
    (GaussianProfileBBVSources.toCoreSources p W hsource)

end CircularLawSection6.NoncompactProfile
