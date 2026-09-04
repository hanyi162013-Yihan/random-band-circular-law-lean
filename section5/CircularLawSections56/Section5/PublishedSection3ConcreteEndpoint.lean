import CircularLawSections56.Section5.PublishedSection3ConcreteAnchors
import CircularLawSections56.Section5.IndicatorFullEndpoints
import CircularLawSections56.Section5.SourceAtomMoments
import ShortRingAnchor.AtomDensityTransport

/-! # Full Section 5 for actual matrices, from the original atom assumptions

No Section 3 anchor, matrix identity, sampling map, or convergence certificate
is an input. The original real and complex density branches both call the
checked Section 3 theorem internally. Only the two quantitative Section 4
estimates and the stated literature hypotheses remain external.
-/

open MeasureTheory ProbabilityTheory Filter Topology ShortRingAnchor
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open scoped ENNReal
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5.PublishedSection3Concrete
open Section6

/-- Reuse the Section 10 Radon--Nikodym construction; a density representative
is produced even when the originally supplied density is only an a.e. input. -/
def boundedDensityOfMeasureLe
    {E : Type*} [MeasurableSpace E] {μ ν : Measure E}
    [SigmaFinite μ] [SigmaFinite ν] {L : ℝ}
    (h : μ ≤ ENNReal.ofReal L • ν) : HasBoundedDensityWithRespectTo μ ν := by
  have hac : μ ≪ ν := by
    intro s hs
    apply le_antisymm ?_ zero_le
    simpa only [Measure.smul_apply, smul_eq_mul, hs, mul_zero] using h s
  refine
    { density := μ.rnDeriv ν
      densityAEMeasurable := (μ.measurable_rnDeriv ν).aemeasurable
      bound := ENNReal.ofReal L
      bound_lt_top := ENNReal.ofReal_lt_top
      density_le_bound := ?_
      law_eq_withDensity := (Measure.withDensity_rnDeriv_eq μ ν hac).symm }
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν)
  intro s _ _
  have he := (Measure.setLIntegral_rnDeriv_le (μ := μ) (ν := ν) s).trans (h s)
  simpa only [lintegral_const, Measure.restrict_apply_univ, Measure.smul_apply, smul_eq_mul] using he

theorem withDensity_le_of_bound {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ENNReal) (L : ℝ) (hf : ∀ᵐ x ∂μ, f x ≤ ENNReal.ofReal L) :
    μ.withDensity f ≤ ENNReal.ofReal L • μ := by
  calc
    μ.withDensity f ≤ μ.withDensity (fun _ => ENNReal.ofReal L) := withDensity_mono hf
    _ = _ := withDensity_const _

theorem complex_density_input
    (f : ℂ → ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    (L : ℝ) (hf : ∀ᵐ z ∂(volume : Measure ℂ), f z ≤ ENNReal.ofReal L) :
    DensityInput (volume.withDensity f) := by
  apply Or.inl
  refine ⟨?_⟩
  rw [Measure.map_id]
  exact boundedDensityOfMeasureLe (withDensity_le_of_bound volume f L hf)

theorem real_density_input
    (f : ℝ → ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    (L : ℝ) (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ ENNReal.ofReal L)
    (hGBL : LivshytsProjectionFormalization.RealFiniteGeometricBrascampLieb) :
    DensityInput (realComplexAtomLaw (volume.withDensity f)) := by
  have hsource : AtomDensityAlternative21 (volume.withDensity f) Complex.ofReal := by
    refine .real (Eventually.of_forall fun _ => rfl) ?_
    change HasBoundedDensityWithRespectTo
      (Measure.map (id : ℝ → ℝ) (volume.withDensity f)) volume
    rw [Measure.map_id]
    exact boundedDensityOfMeasureLe (withDensity_le_of_bound volume f L hf)
  have hcopy : IdentDistrib (id : ℂ → ℂ) Complex.ofReal
      (realComplexAtomLaw (volume.withDensity f)) (volume.withDensity f) := by
    refine ⟨measurable_id.aemeasurable, Complex.continuous_ofReal.measurable.aemeasurable, ?_⟩
    rw [Measure.map_id]
    rfl
  exact Or.inr ⟨hsource.of_identDistrib hcopy, hGBL⟩

theorem centered_band_geometry
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hcenter : ∀ n, (center n).val = W n) :
    (∀ n, d n + 1 = 2 * W n) ∧ (∀ n, center n ≠ 0) := by
  constructor
  · intro n
    have := hwidth n
    omega
  · intro n hn
    have hv := hcenter n
    rw [hn] at hv
    have := hwidth n
    simp only [Fin.val_zero] at hv
    omega

theorem indicator_complex_full_of_published_literature
    (hBBV : BBVComparisonInput)
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ L : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (f : ℂ → ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    (δ γ : ℝ) (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hcenter : ∀ n, (center n).val = W n)
    (hDensity : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L)
    (hMom : AtomMomentAssumption21 (volume.withDensity f) id)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), ComplexQuantitativeSection4PressureInput
      (fun n => iidMeasure (volume.withDensity f) ((n + 1) * (d n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      d (fun n => paperBandCellLength W δ n - (d n + 1))
      (fun n => literalModelCalibrationRaw n (d n) (paperBandCellLength W δ n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (paperBandCellLength W δ n) (profile n) (center n) z)
      (fun _ => c₀) L z)
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), ComplexQuantitativeSection4PressureInput
      (fun n => iidMeasure (volume.withDensity f) ((n + 1) * (d n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      d (fun n => n + 1 - (d n + 1))
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (fun _ => c₀) L z) :
    LiteralSection5Conclusions d center (fun n => (profile n).b) (fun _ => volume.withDensity f) := by
  have hg := centered_band_geometry d W center hwidth hcenter
  apply indicator_complex_full_of_quantitative_section34 d W center profile (fun _ => f)
    δ γ hc₀ hL hδ hδγ hγ hW hfit hg.1 hg.2 (fun _ => hDensity)
    (fun _ => hMom.normSqIntegrable) (fun _ => hMom.unitSecondMoment.le) hCalibration hFinal
  exact Eventually.of_forall fun z => literal_anchors hBBV (volume.withDensity f) hMom
    (complex_density_input f L hDensity) d W center profile hc₀ hwidth hcenter
    δ γ hδ hδγ hγ hW hfit z

theorem indicator_real_full_of_published_literature
    (hBBV : BBVComparisonInput)
    (hGBL : LivshytsProjectionFormalization.RealFiniteGeometricBrascampLieb)
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ L : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (f : ℝ → ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    (δ γ : ℝ) (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hcenter : ∀ n, (center n).val = W n)
    (hDensity : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ ENNReal.ofReal L)
    (hMom : AtomMomentAssumption21 (volume.withDensity f) Complex.ofReal)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), RealQuantitativeSection4PressureInput
      (fun n => iidMeasure (realComplexAtomLaw (volume.withDensity f)) ((n + 1) * (d n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      d (fun n => paperBandCellLength W δ n - (d n + 1))
      (fun n => literalModelCalibrationRaw n (d n) (paperBandCellLength W δ n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (paperBandCellLength W δ n) (profile n) (center n) z)
      (fun _ => c₀) L z)
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), RealQuantitativeSection4PressureInput
      (fun n => iidMeasure (realComplexAtomLaw (volume.withDensity f)) ((n + 1) * (d n + 2)))
      (literalLongActive (paperSafeShortBranch W δ γ))
      d (fun n => n + 1 - (d n + 1))
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (fun _ => c₀) L z) :
    RealLiteralSection5Conclusions d center (fun n => (profile n).b)
      (fun _ => volume.withDensity f) := by
  have hg := centered_band_geometry d W center hwidth hcenter
  apply indicator_real_full_of_quantitative_section34 d W center profile (fun _ => volume.withDensity f)
    δ γ hc₀ hL hδ hδγ hγ hW hfit hg.1 hg.2
    (fun _ => real_source_density_interval_bound f L hDensity)
    (fun _ => real_source_moments_second_integrable _ hMom)
    (fun _ => (real_source_moments_second_eq_one _ hMom).le) hCalibration hFinal
  exact Eventually.of_forall fun z => literal_anchors hBBV
    (realComplexAtomLaw (volume.withDensity f)) (real_source_moments_complexify _ hMom)
    (real_density_input f L hDensity hGBL) d W center profile hc₀ hwidth hcenter
    δ γ hδ hδγ hγ hW hfit z

end CircularLawSections56.Section5.PublishedSection3Concrete
