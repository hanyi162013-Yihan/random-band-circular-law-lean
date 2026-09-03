import CircularLawSection6.CutoffReindexing
import CircularLawSection6.RoutedBandIdentification
import CircularLawSection6.CoreBandIdentification
import CircularLawSections56.Section5.LiteralPhysicalDeterminantSeam

/-! # Actual cutoff expectations on the routed, paper and core sample spaces

Both the sample-law map and the matrix coordinate permutation are explicit.
The nonsingular event is obtained for planar-a.e. spectral parameter from
the previously proved polynomial nonvanishing result. No equality of
cutoff expectations or additional integrability premise is assumed.
-/

open MeasureTheory CircularLawSection4 CircularLawSections56.Section5
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

local instance physicalCutoffPaperLaw_probability (N d : ℕ) [NeZero N]
    (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (paperIndicatorSampleMeasure N d ν) :=
  iidMeasure_isProbability ν _

theorem expected_shifted_cutoff_of_reindex_law_ae
    {ι κ Ω Ξ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsFiniteMeasure ν]
    (T : Ω → Ξ) (hT : MeasurePreserving T μ ν) (e : ι ≃ κ)
    (A : Ω → Matrix ι ι ℂ) (B : Ξ → Matrix κ κ ℂ) (hB : Measurable B)
    (hAB : ∀ ω, (A ω).submatrix e.symm e.symm = B (T ω)) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ a : ℝ, 0 < a →
      (∫ ω, matrixCutoffPotential (A ω - z • 1) a ∂μ) =
        ∫ η, matrixCutoffPotential (B η - z • 1) a ∂ν := by
  filter_upwards [ae_shifted_matrix_det_ne_zero ν B hB] with z hz
  intro a ha
  have hdet := hT.quasiMeasurePreserving.ae hz
  have heq : (fun ω => matrixCutoffPotential (A ω - z • 1) a) =ᵐ[μ]
      (fun ω => matrixCutoffPotential (B (T ω) - z • 1) a) := by
    filter_upwards [hdet] with ω hω
    have hm : (A ω - z • 1).submatrix e.symm e.symm = B (T ω) - z • 1 := by
      rw [← hAB]
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, e.symm.injective.eq_iff]
    have hA : (A ω - z • 1).det ≠ 0 := by
      rwa [← hm, Matrix.det_submatrix_equiv_self] at hω
    rw [← hAB]
    exact (matrixCutoffPotential_shifted_reindex e (A ω) z hA ha).symm
  have hmeas : AEStronglyMeasurable (fun η => matrixCutoffPotential (B η - z • 1) a) (μ.map T) := by
    rw [hT.map_eq]
    exact aestronglyMeasurable_matrixCutoffPotential ν _ (hB.sub measurable_const) hz ha
  calc
    _ = ∫ ω, matrixCutoffPotential (B (T ω) - z • 1) a ∂μ := integral_congr_ae heq
    _ = ∫ η, matrixCutoffPotential (B η - z • 1) a ∂μ.map T :=
      (integral_map hT.measurable.aemeasurable hmeas).symm
    _ = _ := by rw [hT.map_eq]

theorem measurable_paperIndicatorMatrix (N d : ℕ) [NeZero N]
    (center : Fin (d + 1)) (b : Fin (d + 2) → ℂ) :
    Measurable (paperIndicatorX N d center b) := by
  simpa only [paperIndicatorXSubZI, zero_smul, sub_zero] using
    (continuous_paperIndicatorXSubZI N d center b 0).measurable

theorem fullBlock_expected_cutoff_eq_paper_ae
    {q : ℕ} (len : Fin q → ℕ) [NeZero (∑ b, len b)]
    (d H : ℕ) (hwidth : d + 2 = 2 * H + 1)
    (center : Fin (d + 1)) (hcenter : center.val = H)
    (b : Fin (2 * H + 1) → ℂ) (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ a : ℝ, 0 < a →
      (∫ ω, matrixCutoffPotential (routedBandMatrix (fullBlockRoute len H) b ω - z • 1) a
        ∂Measure.pi (fun _ : ((i : Fin q) × Fin (len i)) × Fin (2 * H + 1) => ν)) =
      ∫ η, matrixCutoffPotential
        (paperIndicatorX (∑ i, len i) d center (fun k => b (finCongr hwidth k)) η - z • 1) a
        ∂paperIndicatorSampleMeasure (∑ i, len i) d ν := by
  let : Nonempty ((i : Fin q) × Fin (len i)) :=
    (blockZModEquiv len).nonempty
  exact expected_shifted_cutoff_of_reindex_law_ae _ _
    (fullBlockPaperSample len d H hwidth) (fullBlockPaperSample_measurePreserving len d H hwidth ν)
    (blockZModEquiv len) _ _ (measurable_paperIndicatorMatrix _ _ _ _)
    (fullBlockMatrix_eq_paperIndicatorX len d H hwidth center hcenter b)

namespace NoncompactProfile

theorem unitCore_expected_cutoff_eq_paper_ae (p : NoncompactProfile)
    (N d : ℕ) [NeZero N] (hfit : d + 2 ≤ N)
    (center : Fin (d + 1)) (hsym : d + 1 = 2 * center.val) (W : ℝ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ a : ℝ, 0 < a →
      (∫ ω, matrixCutoffPotential (p.unitCoreMatrix N center.val W ω - z • 1) a ∂cyclicAtomLaw N ν) =
      ∫ η, matrixCutoffPotential
        (paperIndicatorX N d center (fun k => (Real.sqrt (p.coreBandWeight N d center W k) : ℂ)) η - z • 1) a
        ∂paperIndicatorSampleMeasure N d ν := by
  apply expected_shifted_cutoff_of_reindex_law_ae _ _
    (coreBandSample N d center) (coreBandSample_measurePreserving N d hfit center ν)
    (Equiv.refl (ZMod N)) _ _ (measurable_paperIndicatorMatrix _ _ _ _)
  intro ω
  simpa only [Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id] using
    p.unitCoreMatrix_eq_paperIndicatorX N d hfit center hsym W ω

theorem unitCore_expected_cutoff_eq_fullBlock_ae (p : NoncompactProfile)
    {q : ℕ} (len : Fin q → ℕ) [NeZero (∑ i, len i)]
    (d H : ℕ) (hwidth : d + 2 = 2 * H + 1) (hfit : d + 2 ≤ ∑ i, len i)
    (center : Fin (d + 1)) (hcenter : center.val = H) (W : ℝ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ a : ℝ, 0 < a →
      (∫ ω, matrixCutoffPotential (p.unitCoreMatrix (∑ i, len i) H W ω - z • 1) a
        ∂cyclicAtomLaw (∑ i, len i) ν) =
      ∫ η, matrixCutoffPotential (routedBandMatrix (fullBlockRoute len H)
        (fun s => (Real.sqrt (p.coreBandWeight (∑ i, len i) d center W ((finCongr hwidth).symm s)) : ℂ)) η - z • 1) a
        ∂Measure.pi (fun _ : ((i : Fin q) × Fin (len i)) × Fin (2 * H + 1) => ν) := by
  have hsym : d + 1 = 2 * center.val := by omega
  filter_upwards [p.unitCore_expected_cutoff_eq_paper_ae (∑ i, len i) d hfit center hsym W ν,
    fullBlock_expected_cutoff_eq_paper_ae len d H hwidth center hcenter
      (fun s => (Real.sqrt (p.coreBandWeight (∑ i, len i) d center W ((finCongr hwidth).symm s)) : ℂ)) ν]
    with z hz₁ hz₂
  intro a ha
  simpa only [hcenter, Equiv.symm_apply_apply] using (hz₁ a ha).trans (hz₂ a ha).symm

end NoncompactProfile
end CircularLawSection6
