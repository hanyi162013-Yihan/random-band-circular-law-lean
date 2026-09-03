import CircularLawSection6.GinibreBBVLogPotential

/-! # Reusable actual Ginibre consequences of the BBV route

The legacy BC12 bundle and the actual Ginibre circular law can now be
supplied from BBV alone. These wrappers expose the proved consequences to
other sections without assuming a separate Gaussian spectral theorem.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete
  (BBVComparisonInput BC12GinibreInput)

noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace CircularLawSection6

theorem bc12_of_bbv (hBBV : BBVComparisonInput) : BC12GinibreInput :=
  bc12_of_bbv_and_logPotential hBBV (ginibreLogPotential_of_bbv hBBV)

theorem ginibre_spectral_of_bbv (hBBV : BBVComparisonInput) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (ginibreMatrix (n + 1) (ω n).2)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) :=
  ginibre_spectral_of_bc12 (bc12_of_bbv hBBV)

end CircularLawSection6
