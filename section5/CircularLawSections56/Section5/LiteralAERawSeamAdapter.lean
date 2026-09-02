import CircularLawSections56.Section5.LiteralCenteredMesoscopicTelescope
import CircularLawSections56.Section5.LiteralDeterminantFreshAdapter

/-!
# Fresh determinant seam with almost-sure outside positivity

Physical outside products are invertible almost surely, not at every sample.  This
adapter integrates the existing Section 4 fixed-family absolute-log bound using the
AE Fubini lemma.  No modification of the physical outside family on its null bad set
is required, and the conclusion is an absolute `L¹` seam, not only a signed mean bound.
-/

open scoped ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

/-- The Section 4 raw fresh seam requires positivity only almost everywhere in the
outside sample.  All other parameters are the literal profile and atom-law inputs. -/
theorem complex_paperIndicatorFlatFreshZ_rawJointClosure_ae_withDensity
    {Past : Type*} [MeasurableSpace Past]
    (muPast : Measure Past) [IsProbabilityMeasure muPast]
    (N d : ℕ) [NeZero N] (hsize : d + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (z : ℂ) (start : ZMod N)
    (B : Past → (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hBpos : ∀ᵐ a ∂muPast, 0 < exteriorFamilyMaxL2OpNorm (B a))
    (hBmeas : ∀ q i j, Measurable (fun a => B a q i j))
    (hBnorm : ∀ q, Measurable (fun a => ‖B a q‖))
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity f))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(volume.withDensity f) ≤ 1) :
    let muFresh := paperIndicatorSampleMeasure N d (volume.withDensity f)
    let g := fun w : Past × (Fin (N * (d + 2)) → ℂ) =>
      |Real.log ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N d start w.2) (B w.1)‖ -
          Real.log (exteriorFamilyMaxL2OpNorm (B w.1))|
    Integrable g (muPast.prod muFresh) ∧
      (∫ w, g w ∂(muPast.prod muFresh)) ≤
        paperIsolatedCoefficientLoss d c₀ + complexFreshNegativeBound d L +
          paperFreshPositiveBound d z := by
  classical
  let muFresh := paperIndicatorSampleMeasure N d (volume.withDensity f)
  let : IsProbabilityMeasure muFresh := by
    simpa only [muFresh, paperIndicatorSampleMeasure] using
      iidMeasure_isProbability (volume.withDensity f) (N * (d + 2))
  let radius := fun w : Past × (Fin (N * (d + 2)) → ℂ) =>
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtoms N d start w.2) (B w.1)‖
  let scale := fun a : Past => exteriorFamilyMaxL2OpNorm (B a)
  let g := fun w => |Real.log (radius w) - Real.log (scale w.1)|
  have hradius : Measurable radius := by
    dsimp only [radius]
    apply profile.measurable_norm_paperIndicatorFreshZ_of_measurable_family
    · intro t ell
      exact (measurable_paperIndicatorFreshAtoms N d start t ell).comp measurable_snd
    · intro q i j
      exact (hBmeas q i j).comp measurable_fst
  have hscale : Measurable scale :=
    measurable_exteriorFamilyMaxL2OpNorm B hBnorm
  have hg : Measurable g := by
    change Measurable (fun w => ‖Real.log (radius w) - Real.log (scale w.1)‖)
    exact ((Real.measurable_log.comp hradius).sub
      (Real.measurable_log.comp (hscale.comp measurable_fst))).norm
  apply integrable_prod_and_integral_le_of_ae_integrable_integral_le
    muPast muFresh g hg (fun _ => abs_nonneg _)
    (paperIsolatedCoefficientLoss d c₀ + complexFreshNegativeBound d L +
      paperFreshPositiveBound d z)
  · filter_upwards [hBpos] with a ha
    exact (profile.complex_paperIndicatorFlatFreshZ_absLog_L1_withDensity
      N d hsize hc₀ hsqrt center z start (B a) ha
      f hL hf hsecondInt hsecond).2.1
  · filter_upwards [hBpos] with a ha
    exact (profile.complex_paperIndicatorFlatFreshZ_absLog_L1_withDensity
      N d hsize hc₀ hsqrt center z start (B a) ha
      f hL hf hsecondInt hsecond).2.2

end CircularLawSections56.Section5
