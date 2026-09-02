import CircularLawSection6.CutoffMeasurability
import CircularLawSection6.NormalizedConcentration

/-! # Expected cutoff stability from the actual mean-square coupling

Cauchy--Schwarz and the proved matrix comparison yield the expected
cutoff error. Measurability and integrability of the difference are derived,
not additional input hypotheses.
-/

open MeasureTheory ProbabilityTheory
open TaoVuReplacement CircularLawSection4

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem memLp_sqrt_of_integrable_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) (hpos : 0 ≤ᵐ[μ] f) :
    MemLp (fun ω => Real.sqrt (f ω)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)).2
  apply hf.congr
  filter_upwards [hpos] with ω hω
  exact (Real.sq_sqrt hω).symm

theorem integral_sqrt_le_sqrt_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hpos : 0 ≤ᵐ[μ] f) :
    (∫ ω, Real.sqrt (f ω) ∂μ) ≤ Real.sqrt (∫ ω, f ω ∂μ) := by
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ)
    Real.HolderConjugate.two_two (ae_of_all _ fun ω => Real.sqrt_nonneg (f ω))
    (ae_of_all _ fun _ : Ω => (zero_le_one : (0 : ℝ) ≤ 1))
    (memLp_sqrt_of_integrable_nonneg μ f hf hpos)
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ))
  have h : (∫ ω, Real.sqrt (f ω) ∂μ) ≤
      Real.sqrt (∫ ω, (Real.sqrt (f ω)) ^ 2 ∂μ) := by
    simpa [Real.rpow_two, Real.sqrt_eq_rpow] using hcs
  have heq : (∫ ω, (Real.sqrt (f ω)) ^ 2 ∂μ) = ∫ ω, f ω ∂μ := by
    apply integral_congr_ae
    filter_upwards [hpos] with ω hω
    exact Real.sq_sqrt hω
  rwa [heq] at h

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem expected_matrixCutoff_difference_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Ω → Matrix ι ι ℂ) (hA : Measurable A) (hB : Measurable B)
    (hAdet : ∀ᵐ ω ∂μ, (A ω).det ≠ 0) (hBdet : ∀ᵐ ω ∂μ, (B ω).det ≠ 0)
    (hE : Integrable (fun ω => hilbertSchmidtSq (A ω - B ω)) μ)
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun ω => |matrixCutoffPotential (A ω) a - matrixCutoffPotential (B ω) a|) μ ∧
      (∫ ω, |matrixCutoffPotential (A ω) a - matrixCutoffPotential (B ω) a| ∂μ) ≤
        Real.sqrt (∫ ω, hilbertSchmidtSq (A ω - B ω) ∂μ) /
          (a * Real.sqrt (Fintype.card ι : ℝ)) := by
  let e := fun ω => hilbertSchmidtSq (A ω - B ω)
  have hpos : 0 ≤ᵐ[μ] e := ae_of_all _ fun ω => hilbertSchmidtSq_nonneg _
  have hroot := (memLp_sqrt_of_integrable_nonneg μ e hE hpos).integrable (by norm_num)
  have hbound := hroot.div_const (a * Real.sqrt (Fintype.card ι : ℝ))
  have hm := ((aestronglyMeasurable_matrixCutoffPotential μ A hA hAdet ha).sub
    (aestronglyMeasurable_matrixCutoffPotential μ B hB hBdet ha)).norm
  have hm' : AEStronglyMeasurable (fun ω =>
      |matrixCutoffPotential (A ω) a - matrixCutoffPotential (B ω) a|) μ := by
    simpa only [Real.norm_eq_abs] using hm
  have hb : (fun ω => |matrixCutoffPotential (A ω) a - matrixCutoffPotential (B ω) a|) ≤ᵐ[μ]
      (fun ω => Real.sqrt (e ω) / (a * Real.sqrt (Fintype.card ι : ℝ))) := by
    filter_upwards [hAdet, hBdet] with ω hω hω'
    exact matrixCutoffPotential_difference_le _ _ hω hω' ha
  have hi := hbound.mono' hm' (by simpa only [Real.norm_eq_abs, abs_abs] using hb)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, Real.sqrt (e ω) / (a * Real.sqrt (Fintype.card ι : ℝ)) ∂μ := integral_mono_ae hi hbound hb
    _ = (∫ ω, Real.sqrt (e ω) ∂μ) / (a * Real.sqrt (Fintype.card ι : ℝ)) := integral_div_const _ _
    _ ≤ _ := div_le_div_of_nonneg_right (integral_sqrt_le_sqrt_integral μ e hE hpos)
      (mul_nonneg ha.le (Real.sqrt_nonneg _))

end CircularLawSection6
