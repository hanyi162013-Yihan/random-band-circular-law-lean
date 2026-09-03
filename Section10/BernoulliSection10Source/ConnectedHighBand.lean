import BernoulliSection10Source.FullBlockLogLimit
import BernoulliSection10Source.PlanarHighBand
import BernoulliSection10Source.RealHighBand
import BernoulliSection10.HighBandClosure
import BernoulliSection10Complex.HighBandClosure

/-! # Construct both high-band anchors: no `Section3Inputs` premise remains -/

open MeasureTheory Filter
open scoped Topology
noncomputable section
set_option autoImplicit false
namespace BernoulliSection10Source
open BernoulliSection10 ShortRingAnchor
open LivshytsProjectionFormalization

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem planar_highBandLogLimit
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    {μ : Measure ℂ} {L : ℝ} (hμ : BernoulliSection10Complex.IsPlanarDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ) :
    BernoulliSection10Complex.HighBandLogLimit μ := by
  letI := hμ.toIsProbabilityMeasure
  intro W s hW hWtop ω hω hω1 hhigh z
  let N := fun n => (s n + 3) * W n
  have hN (n : ℕ) : 0 < N n := Nat.mul_pos (by omega) (hW n)
  have hNtop : Tendsto N atTop atTop :=
    tendsto_atTop_mono' atTop
      (Eventually.of_forall fun n => Nat.le_mul_of_pos_left (W n) (by omega)) hWtop
  obtain ⟨χ, κ, τ, hp⟩ := exists_hardEdgeAdmissible_of_omega hω
  have hβ1 : (8 / 9 : ℝ) + ω ≤ 1 := by linarith
  have hχ1 : χ ≤ 1 / 2 := by have := hp.2.2.2.1; linarith
  have hlsv : ∀ᶠ n in atTop, (N n : ℝ) ^ (1 / 2 + χ) ≤ W n := by
    filter_upwards [hhigh] with n hn
    exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN n)
      hp.2.2.2.1.le).trans hn
  have hmin := physical_planar_minimum_input hμ h3 W s hW hNtop
    hp.1 hχ1 hp.2.1 hlsv z
  have hmom := BernoulliSection10Complex.SourceInputs.profileMatrix_row_moments
    hμ.normalized (fun n => physicalProfile (W n) (s n))
    (fun n => SourceInputs.physicalProfile_doublyStochastic (W n) (s n) (hW n))
  exact fullBlock_log_limit_from_source hBBV hBC12 μ id (planarAtomMoments hμ h3)
    W s hW hWtop hp hβ1 hhigh z hmom hmin

theorem real_highBandLogLimit
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    (hGBL : RealFiniteGeometricBrascampLieb)
    {μ : Measure ℝ} {L : ℝ} (hμ : BernoulliSection10.IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    BernoulliSection10.HighBandLogLimit μ := by
  letI := hμ.toIsProbabilityMeasure
  intro W s hW hWtop ω hω hω1 hhigh z
  let N := fun n => (s n + 3) * W n
  have hN (n : ℕ) : 0 < N n := Nat.mul_pos (by omega) (hW n)
  have hNtop : Tendsto N atTop atTop :=
    tendsto_atTop_mono' atTop
      (Eventually.of_forall fun n => Nat.le_mul_of_pos_left (W n) (by omega)) hWtop
  obtain ⟨χ, κ, τ, hp⟩ := exists_hardEdgeAdmissible_of_omega hω
  have hβ1 : (8 / 9 : ℝ) + ω ≤ 1 := by linarith
  have hχ1 : χ ≤ 1 / 2 := by have := hp.2.2.2.1; linarith
  have hlsv : ∀ᶠ n in atTop, (N n : ℝ) ^ (1 / 2 + χ) ≤ W n := by
    filter_upwards [hhigh] with n hn
    exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN n)
      hp.2.2.2.1.le).trans hn
  have hmin := physical_real_minimum_input hμ h3 hGBL W s hW hNtop
    hp.1 hχ1 hp.2.1 hlsv z
  have hmom := SourceInputs.profileMatrix_row_moments hμ
    (fun n => physicalProfile (W n) (s n))
    (fun n => SourceInputs.physicalProfile_doublyStochastic (W n) (s n) (hW n))
  have heq (n : ℕ) : actualProfileMatrix Complex.ofReal (physicalProfile (W n) (s n)) =
      SourceInputs.profileMatrix (physicalProfile (W n) (s n)) := by
    funext sample i j
    exact (Complex.ofReal_mul _ _).symm
  have h := fullBlock_log_limit_from_source hBBV hBC12 μ Complex.ofReal (realAtomMoments hμ h3)
    W s hW hWtop hp hβ1 hhigh z
    (by simpa only [heq, sampleLaw, SourceInputs.inputLaw] using hmom)
    (by simpa only [heq, sampleLaw, SourceInputs.inputLaw] using hmin)
  simpa only [heq, sampleLaw, SourceInputs.inputLaw] using h

end BernoulliSection10Source
