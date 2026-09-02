import CircularLawSection6.ReusedLogDetIntegrability
import CircularLawSection6.ExpectedCutoffComparison

/-! # Parameter nonvanishing and expected cutoff comparison on finite index sets

The replacement theorem already gives the planar-a.e. nonvanishing of
shifted cyclic-indexed matrices. Reindexing transports it to an arbitrary
finite matrix, including block sigma indices. Empty matrices have determinant
one. Consequently the expected shifted cutoff comparison needs only
measurability and finite difference energy, not a separate nonsingularity
hypothesis for the block-periodic construction.
-/

open MeasureTheory
open TaoVuReplacement

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem ae_shifted_matrix_det_ne_zero {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Ω → Matrix ι ι ℂ) (hA : Measurable A) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ ω ∂μ, (A ω - z • 1).det ≠ 0 := by
  classical
  by_cases hn : Fintype.card ι = 0
  · letI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    exact ae_of_all _ (fun _ => ae_of_all _ (fun _ => by simp))
  · letI : NeZero (Fintype.card ι) := ⟨hn⟩
    let e : ZMod (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (by simp)
    have h := ae_shifted_cyclic_det_ne_zero μ (Fintype.card ι)
      (fun ω => (A ω).submatrix e e)
      (fun i j => (measurable_pi_apply (e j)).comp ((measurable_pi_apply (e i)).comp hA))
    have heq (ω : Ω) (z : ℂ) :
        ((A ω).submatrix e e - z • 1).det = (A ω - z • 1).det := by
      rw [← Matrix.submatrix_one_equiv e, ← Matrix.submatrix_smul,
        ← Matrix.submatrix_sub, Matrix.det_submatrix_equiv_self]
    simpa only [heq] using h

theorem expected_shifted_matrixCutoff_difference_ae
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Ω → Matrix ι ι ℂ) (hA : Measurable A) (hB : Measurable B)
    (hE : Integrable (fun ω => hilbertSchmidtSq (A ω - B ω)) μ) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ a : ℝ, 0 < a →
      Integrable (fun ω => |matrixCutoffPotential (A ω - z • 1) a -
        matrixCutoffPotential (B ω - z • 1) a|) μ ∧
      (∫ ω, |matrixCutoffPotential (A ω - z • 1) a -
        matrixCutoffPotential (B ω - z • 1) a| ∂μ) ≤
        Real.sqrt (∫ ω, hilbertSchmidtSq (A ω - B ω) ∂μ) /
          (a * Real.sqrt (Fintype.card ι : ℝ)) := by
  filter_upwards [ae_shifted_matrix_det_ne_zero μ A hA,
    ae_shifted_matrix_det_ne_zero μ B hB] with z hzA hzB
  intro a ha
  have heq (ω : Ω) : (A ω - z • 1) - (B ω - z • 1) = A ω - B ω := by abel
  have hi : Integrable (fun ω => hilbertSchmidtSq ((A ω - z • 1) - (B ω - z • 1))) μ := by
    simpa only [heq] using hE
  simpa only [heq] using expected_matrixCutoff_difference_le μ
    (fun ω => A ω - z • 1) (fun ω => B ω - z • 1)
    (hA.sub measurable_const) (hB.sub measurable_const) hzA hzB hi ha

end CircularLawSection6
