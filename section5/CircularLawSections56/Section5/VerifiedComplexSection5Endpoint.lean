import CircularLawSections56.Section5.VerifiedComplexPressureInputs
import CircularLawSections56.Section5.PublishedSection3ConcreteEndpoint

/-! # Complex-density Section 5 endpoint with BBV as its sole literature input

The finite Section 4 pressure contracts are constructed from the literal density
model. Section 3 constructs the calibration anchors and its Gaussian reference.
The older conditional endpoint remains available as a reusable assembly lemma.
-/

open MeasureTheory Filter Topology ShortRingAnchor
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open scoped ENNReal

noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace CircularLawSections56.Section5.PublishedSection3Concrete
open Section6

/-- Section 5 complex-density conclusion: actual sampled matrices, constructed
Section 4 pressure inputs and proved Section 3/Ginibre anchors. Only BBV remains
as an external mathematical theorem, besides the stated model assumptions. -/
theorem indicator_complex_full_of_bbv
    (hBBV : BBVComparisonInput)
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ L : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    (δ γ : ℝ) (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hcenter : ∀ n, (center n).val = W n)
    (hDensity : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L)
    (hMom : AtomMomentAssumption21 (volume.withDensity f) id) :
    LiteralSection5Conclusions d center (fun n => (profile n).b)
      (fun _ => volume.withDensity f) := by
  have hg := centered_band_geometry d W center hwidth hcenter
  have hgeom (n : ℕ) (hn : literalLongActive (paperSafeShortBranch W δ γ) n = true) :=
    paperTransferReady_geometry W δ n (paperSafeShortBranch_active W δ γ n hn).2
  apply indicator_complex_full_of_published_literature hBBV d W center profile f
    δ γ hc₀ hL hδ hδγ hγ hW hfit hwidth hcenter hDensity hMom
  · apply ae_of_all
    intro z
    exact complex_literalModelCalibration_quantitative
      (literalLongActive (paperSafeShortBranch W δ γ)) d (paperBandCellLength W δ)
      profile center z (fun _ => f)
      (fun n hn => (hgeom n hn).2.2.2.2.2)
      (fun n hn => by rw [hg.1 n]; exact (hgeom n hn).2.2.2.2.1)
      (fun _ _ => hc₀)
      (fun n _ => normalized_profile_lower_scale_le_one (d n) (profile n) hc₀)
      (fun n _ => hg.2 n) hL (fun _ _ => hDensity)
      (fun _ _ => hMom.normSqIntegrable) (fun _ _ => hMom.unitSecondMoment.le)
  · apply ae_of_all
    intro z
    exact complex_literalModelFinal_quantitative
      (literalLongActive (paperSafeShortBranch W δ γ)) d profile center z (fun _ => f)
      (fun n hn => by rw [hg.1 n]; exact (Nat.le_succ _).trans (hgeom n hn).2.1)
      (fun _ _ => hc₀)
      (fun n _ => normalized_profile_lower_scale_le_one (d n) (profile n) hc₀)
      (fun n _ => hg.2 n) hL (fun _ _ => hDensity)
      (fun _ _ => hMom.normSqIntegrable) (fun _ _ => hMom.unitSecondMoment.le)

end CircularLawSections56.Section5.PublishedSection3Concrete
