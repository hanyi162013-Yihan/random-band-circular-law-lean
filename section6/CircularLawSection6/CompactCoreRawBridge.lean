import CircularLawSection6.CoreBandIdentification
import CircularLawSection6.ProfileConcentration
import CircularLawSection6.TriangularLawTransport
import CircularLawSections56.Section6.LiteralIndicatorModel

/-! # Section 5's literal probability limit gives the core mean limit

The input is precisely a Section 5 probability conclusion on the literal
finite-band sample space. The exact core identification and IID marginal
transport are proved, and the concentration premise is discharged by the
actual Gaussian theorem. No expectation-convergence input is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology CircularLawSection4
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

attribute [local instance] iidMeasure_isProbability

local instance paperSample_probability (N d : ℕ) [NeZero N] :
    IsProbabilityMeasure (paperIndicatorSampleMeasure N d circularComplexGaussian) :=
  iidMeasure_isProbability circularComplexGaussian _

def unitCoreLogPotential (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) (z : ℂ)
    (ω : ZMod N × ZMod N → ℂ) : ℝ :=
  Real.log ‖(p.unitCoreMatrix N H W ω - z • 1).det‖ / (N : ℝ)

theorem unitCoreLogPotential_eq_literal (p : NoncompactProfile) (k d : ℕ)
    (hfit : d + 2 ≤ k + 2) (center : Fin (d + 1)) (hsym : d + 1 = 2 * center.val)
    (W : ℝ) (z : ℂ) (ω : ZMod (k + 2) × ZMod (k + 2) → ℂ) :
    p.unitCoreLogPotential (k + 2) center.val W z ω =
      physicalLogPotential (literalIndicatorMatrix (k + 1) d center
        (fun s => (Real.sqrt (p.coreBandWeight (k + 2) d center W s) : ℂ))
        (coreBandSample (k + 2) d center ω)) z := by
  rw [literalIndicatorMatrix_logPotential]
  unfold unitCoreLogPotential paperIndicatorXSubZI
  rw [p.unitCoreMatrix_eq_paperIndicatorX (k + 2) d hfit center hsym]
  norm_num [Nat.cast_add, Nat.cast_one, add_assoc]

theorem unitCore_probability_of_section5 (p : NoncompactProfile)
    (size band : ℕ → ℕ) (center : ∀ n, Fin (band n + 1))
    (hfit : ∀ n, band n + 2 ≤ size n + 2)
    (hsym : ∀ n, band n + 1 = 2 * (center n).val) (W : ℕ → ℝ) (z : ℂ) (target : ℝ)
    (hSection5 : TendstoInProbabilityTri
      (fun n => paperIndicatorSampleMeasure (size n + 2) (band n) circularComplexGaussian)
      (fun n ω => physicalLogPotential (literalIndicatorMatrix (size n + 1) (band n) (center n)
        (fun s => (Real.sqrt (p.coreBandWeight (size n + 2) (band n) (center n) (W n) s) : ℂ)) ω) z)
      target) :
    TendstoInProbabilityTri (fun n => gaussianProfileLaw (size n + 2))
      (fun n => p.unitCoreLogPotential (size n + 2) (center n).val (W n) z) target := by
  have hm (n : ℕ) : Measurable (fun ω => physicalLogPotential
      (literalIndicatorMatrix (size n + 1) (band n) (center n)
        (fun s => (Real.sqrt (p.coreBandWeight (size n + 2) (band n) (center n) (W n) s) : ℂ)) ω) z) := by
    unfold physicalLogPotential
    apply Measurable.div_const
    apply measurable_log_norm_matrix_det
    intro i j
    exact (literalIndicatorMatrix_measurable _ _ _ _ i j).sub measurable_const
  have h := tendstoInProbabilityTri_comp_measurePreserving
    (fun n => gaussianProfileLaw (size n + 2))
    (fun n => paperIndicatorSampleMeasure (size n + 2) (band n) circularComplexGaussian)
    (fun n => coreBandSample (size n + 2) (band n) (center n))
    (fun n => coreBandSample_measurePreserving _ _ (hfit n) _ circularComplexGaussian)
    _ hm hSection5
  apply h.congr (fun n ω => ?_) rfl
  exact (p.unitCoreLogPotential_eq_literal (size n) (band n) (hfit n) (center n)
    (hsym n) (W n) z ω).symm

/-- The fixed-core raw mean convergence follows from Section 5 and the
proved Gaussian concentration on every branch, including the direct one. -/
theorem unitCore_mean_of_section5 (p : NoncompactProfile)
    (size band : ℕ → ℕ) (hsize : Tendsto (fun n => size n + 2) atTop atTop)
    (center : ∀ n, Fin (band n + 1)) (hfit : ∀ n, band n + 2 ≤ size n + 2)
    (hsym : ∀ n, band n + 1 = 2 * (center n).val) (W : ℕ → ℝ) (z : ℂ) (target : ℝ)
    (hSection5 : TendstoInProbabilityTri
      (fun n => paperIndicatorSampleMeasure (size n + 2) (band n) circularComplexGaussian)
      (fun n ω => physicalLogPotential (literalIndicatorMatrix (size n + 1) (band n) (center n)
        (fun s => (Real.sqrt (p.coreBandWeight (size n + 2) (band n) (center n) (W n) s) : ℂ)) ω) z)
      target) :
    Tendsto (fun n => ∫ ω, p.unitCoreLogPotential (size n + 2) (center n).val (W n) z ω
      ∂gaussianProfileLaw (size n + 2)) atTop (𝓝 target) := by
  apply deterministic_center_tendsto_of_tri_anchor_and_close
    (fun n => gaussianProfileLaw (size n + 2))
    (fun n => p.unitCoreLogPotential (size n + 2) (center n).val (W n) z)
    (fun n => ∫ ω, p.unitCoreLogPotential (size n + 2) (center n).val (W n) z ω
      ∂gaussianProfileLaw (size n + 2)) target
  · exact p.unitCore_probability_of_section5 size band center hfit hsym W z target hSection5
  · simpa only [unitCoreLogPotential, Complex.ofReal_one, one_smul, Nat.cast_add, Nat.cast_ofNat] using
      p.unitCore_profile_concentration size hsize (fun n => (center n).val) W (r := 1) zero_lt_one z

end CircularLawSection6.NoncompactProfile
