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

/-- Pointwise-in-spectral-parameter Section 5 logarithmic-potential limit.
For every fixed `z`, both quantitative pressure estimates and both Section 3
anchors are constructed before invoking the fixed-`z` assembly theorem.  The
constants may depend on `z`; no uniform exceptional-set statement is asserted. -/
theorem indicator_complex_logPotential_at_of_bbv
    (hBBV : BBVComparisonInput)
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ L : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    (δ γ : ℝ) (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hcenter : ∀ n, (center n).val = W n)
    (hDensity : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L)
    (hMom : AtomMomentAssumption21 (volume.withDensity f) id)
    (z : ℂ) :
    let : ∀ n, IsProbabilityMeasure
        (iidMeasure (volume.withDensity f) ((n + 1) * (d n + 2))) :=
      fun n => iidMeasure_isProbability (volume.withDensity f) _
    TendstoInProbabilityTri
      (fun n => iidMeasure (volume.withDensity f) ((n + 1) * (d n + 2)))
      (fun n ω => physicalLogPotential
        (literalIndicatorMatrix n (d n) (center n) (profile n).b ω) z)
      (circularLogPotential z) := by
  let : ∀ n, IsProbabilityMeasure
      (iidMeasure (volume.withDensity f) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (volume.withDensity f) _
  have hg := centered_band_geometry d W center hwidth hcenter
  have hgeom (n : ℕ) (hn : literalLongActive (paperSafeShortBranch W δ γ) n = true) :=
    paperTransferReady_geometry W δ n (paperSafeShortBranch_active W δ γ n hn).2
  have hProfile (n : ℕ) : |Real.log c₀| ≤ |Real.log c₀| * dimensionLogScale (d n) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_dimensionLogScale (d n)) (abs_nonneg (Real.log c₀))
  have hCalQ := complex_literalModelCalibration_quantitative
    (literalLongActive (paperSafeShortBranch W δ γ)) d (paperBandCellLength W δ)
    profile center z (fun _ => f)
    (fun n hn => (hgeom n hn).2.2.2.2.2)
    (fun n hn => by rw [hg.1 n]; exact (hgeom n hn).2.2.2.2.1)
    (fun _ _ => hc₀)
    (fun n _ => normalized_profile_lower_scale_le_one (d n) (profile n) hc₀)
    (fun n _ => hg.2 n) hL (fun _ _ => hDensity)
    (fun _ _ => hMom.normSqIntegrable) (fun _ _ => hMom.unitSecondMoment.le)
  have hFinQ := complex_literalModelFinal_quantitative
    (literalLongActive (paperSafeShortBranch W δ γ)) d profile center z (fun _ => f)
    (fun n hn => by rw [hg.1 n]; exact (Nat.le_succ _).trans (hgeom n hn).2.1)
    (fun _ _ => hc₀)
    (fun n _ => normalized_profile_lower_scale_le_one (d n) (profile n) hc₀)
    (fun n _ => hg.2 n) hL (fun _ _ => hDensity)
    (fun _ _ => hMom.normSqIntegrable) (fun _ _ => hMom.unitSecondMoment.le)
  have hCal := ComplexQuantitativeSection4PressureInput.toCompleted hCalQ
    (paperBandCellLength W δ) W |Real.log c₀| (abs_nonneg _)
    (fun n hn => (paperSafeShortBranch_active W δ γ n hn).2.1)
    (fun n _ => hg.1 n) (fun n _ => Nat.sub_le _ _) (fun _ _ => hc₀)
    (fun n _ => hProfile n)
  have hFin := ComplexQuantitativeSection4PressureInput.toCompleted hFinQ
    (fun n => n + 1) W |Real.log c₀| (abs_nonneg _)
    (fun n hn => (paperSafeShortBranch_active W δ γ n hn).2.1)
    (fun n _ => hg.1 n) (fun n _ => Nat.sub_le _ _) (fun _ _ => hc₀)
    (fun n _ => hProfile n)
  exact literal_canonical_profile_logPotential_at_of_section34 d W center profile
    |Real.log c₀| (uniformFreshNegativeConstant L)
    ((Real.log (max 1 (Real.pi * L)) + 1) / 2)
    (complexLogarithmicSection4Constant |Real.log c₀| L)
    (fun _ => volume.withDensity f) δ γ (fun _ => hc₀) (abs_nonneg _)
    (by
      unfold uniformFreshNegativeConstant
      linarith [Real.log_nonneg (le_max_left 1 (Real.pi * L))])
    (by linarith [Real.log_nonneg (le_max_left 1 (Real.pi * L))])
    hδ hδγ hγ hW hfit hg.1 hg.2 hProfile
    (fun _ => AtomTransferControl.complex f L hL hDensity
      hMom.normSqIntegrable hMom.unitSecondMoment.le)
    z hCal hFin
    (literal_anchors hBBV (volume.withDensity f) hMom
      (complex_density_input f L hDensity) d W center profile hc₀ hwidth hcenter
      δ γ hδ hδγ hγ hW hfit z)

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
