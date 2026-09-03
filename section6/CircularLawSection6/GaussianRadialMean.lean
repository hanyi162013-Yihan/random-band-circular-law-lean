import CircularLawSection6.GaussianAllDimensions
import CircularLawSection6.ProfileDiagonalBound
import CircularLawSection6.GaussianTailJensen
import CircularLawSection6.VaryingNormalization
import CircularLawSection6.PotentialContinuity

/-! # The actual Gaussian core mean is radially monotone

The positive-scale logarithm is integrable by the already proved Gaussian
row estimate. Rotation invariance and invariant Fubini averaging identify
its expectation with the actual determinant-polynomial circle mean.
Jensen monotonicity then applies to the original matrix expectation.
This discharges the monotonicity premise in the varying-radius argument.
-/

open MeasureTheory Filter Topology Set Real
open CircularLawSections56.Section6

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

def scaledUnitCoreLogDet (p : NoncompactProfile) (N H : ℕ) [NeZero N]
    (W r : ℝ) (z : ℂ) (ω : ZMod N × ZMod N → ℂ) : ℝ :=
  Real.log ‖((r : ℂ) • p.unitCoreMatrix N H W ω - z • 1).det‖

def scaledUnitCoreMean (p : NoncompactProfile) (N H : ℕ) [NeZero N]
    (W r : ℝ) (z : ℂ) : ℝ :=
  (∫ ω, p.scaledUnitCoreLogDet N H W r z ω ∂gaussianProfileLaw N) / (N : ℝ)

theorem scaledUnitCoreLogDet_measurable (p : NoncompactProfile) (N H : ℕ) [NeZero N]
    (W r : ℝ) (z : ℂ) : Measurable (p.scaledUnitCoreLogDet N H W r z) := by
  apply measurable_log_norm_matrix_det
  intro i j
  exact (measurable_const.mul (weightedCyclicMatrix_measurable N
    (maskedWeight (coreOffsets N H) (p.normalizedCoreWeight N H W)) i j)).sub measurable_const

theorem scaledUnitCoreLogDet_memLp (p : NoncompactProfile) (N H : ℕ) [NeZero N]
    (W : ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    MemLp (p.scaledUnitCoreLogDet N H W r z) 2 (gaussianProfileLaw N) := by
  have hq : p.diagonalComparisonConstant / (N : ℝ) ≤
      maskedWeight (coreOffsets N H) (p.normalizedCoreWeight N H W) 0 := by
    simpa only [maskedWeight, if_pos (zero_mem_coreOffsets N H)] using
      p.diagonal_normalizedCoreWeight_ge N H W
  have h := (gaussian_cyclic_memLp_and_variance_all N _
    p.diagonalComparisonConstant_pos hr z hq).1
  unfold scaledUnitCoreLogDet unitCoreMatrix gaussianProfileLaw
  unfold cyclicRawLogDet at h
  exact h

theorem unitCoreMatrix_global_phase (p : NoncompactProfile) (N H : ℕ) [NeZero N]
    (W : ℝ) (a : Circle) (ω : ZMod N × ZMod N → ℂ) :
    p.unitCoreMatrix N H W (tailRotation N ∅ a ω) =
      (a : ℂ) • p.unitCoreMatrix N H W ω := by
  have h := tailMatrix_tailRotation N ∅
    (maskedWeight (coreOffsets N H) (p.normalizedCoreWeight N H W)) a ω
  have hmask (q : ZMod N → ℝ) : maskedWeight Finset.univ q = q := by
    funext t
    simp [maskedWeight]
  rw [Finset.compl_empty, hmask] at h
  exact h

theorem scaledUnitCore_phaseAverage_eq (p : NoncompactProfile) (N H : ℕ) [NeZero N]
    (W r : ℝ) (z : ℂ) (ω : ZMod N × ZMod N → ℂ) :
    phaseAverage (fun θ => p.scaledUnitCoreLogDet N H W r z
      (tailRotation N ∅ (Circle.exp θ) ω)) =
      polynomialCircleMean (affineDeterminantPolynomial (-z • 1) (p.unitCoreMatrix N H W ω)) r := by
  unfold phaseAverage polynomialCircleMean circleAverage
  simp only [smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [affineDeterminantPolynomial_eval]
  unfold scaledUnitCoreLogDet
  rw [p.unitCoreMatrix_global_phase]
  have hm : (r : ℂ) • ((Circle.exp θ : ℂ) • p.unitCoreMatrix N H W ω) - z • 1 =
      circleMap 0 r θ • p.unitCoreMatrix N H W ω + (-z) • 1 := by
    ext i j
    simp [circleMap_zero, Circle.coe_exp, Matrix.smul_apply, smul_eq_mul, mul_assoc, sub_eq_add_neg]
  rw [hm]

theorem scaledUnitCore_phase_integral (p : NoncompactProfile) (N H : ℕ) [NeZero N]
    (W : ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Integrable (fun ω => polynomialCircleMean
      (affineDeterminantPolynomial (-z • 1) (p.unitCoreMatrix N H W ω)) r) (gaussianProfileLaw N) ∧
      (∫ ω, polynomialCircleMean
        (affineDeterminantPolynomial (-z • 1) (p.unitCoreMatrix N H W ω)) r ∂gaussianProfileLaw N) =
        ∫ ω, p.scaledUnitCoreLogDet N H W r z ω ∂gaussianProfileLaw N := by
  have h := invariant_phaseAverage_integral
    (fun θ => tailRotation N ∅ (Circle.exp θ))
    (tailRotation_joint_measurable N ∅)
    (fun θ => gaussianProfileLaw_tailRotation_preserving N ∅ (Circle.exp θ))
    (p.scaledUnitCoreLogDet_measurable N H W r z)
    ((p.scaledUnitCoreLogDet_memLp N H W hr z).integrable (by norm_num))
  simpa only [p.scaledUnitCore_phaseAverage_eq] using h

theorem scaledUnitCoreMean_monotoneOn (p : NoncompactProfile) (N H : ℕ) [NeZero N]
    (W : ℝ) (z : ℂ) : MonotoneOn (fun r => p.scaledUnitCoreMean N H W r z) (Ioi 0) := by
  intro r hr s hs hrs
  have hir := p.scaledUnitCore_phase_integral N H W hr z
  have his := p.scaledUnitCore_phase_integral N H W hs z
  unfold scaledUnitCoreMean
  dsimp only
  rw [← hir.2, ← his.2]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact integral_mono hir.1 his.1 (fun ω => polynomialCircleMean_monotoneOn
    (affineDeterminantPolynomial (-z • 1) (p.unitCoreMatrix N H W ω)) hr hs hrs)

theorem rawCoreMean_eq_scaledUnitCoreMean (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) (z : ℂ) :
    (∫ ω, p.rawCoreLogDet N H W z ω ∂gaussianProfileLaw N) / (N : ℝ) =
      p.scaledUnitCoreMean N H W (Real.sqrt (p.coreMass N H W)) z := by
  unfold rawCoreLogDet scaledUnitCoreMean scaledUnitCoreLogDet
  simp_rw [p.coreMatrix_eq_scale_unitCoreMatrix]

/-- The fixed-scale raw limits are the compact-core Section 5 input. The
varying normalization, its integrability, and its radial squeeze are proved
for the actual model here, on a countable common full-measure set. -/
theorem gaussian_core_raw_mean_of_fixed_scales (p : NoncompactProfile)
    (N H : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ)
    {v : ℝ} (hv : 0 < v)
    (hmass : Tendsto (fun n => p.coreMass (N n) (H n) (W n)) atTop (𝓝 v))
    {S : Set ℝ} (hS : Dense S) (hCount : S.Countable)
    (hfixed : ∀ r ∈ S, ∀ᵐ z ∂(volume : Measure ℂ), 0 < r →
      Tendsto (fun n => p.scaledUnitCoreMean (N n) (H n) (W n) r z) atTop
        (𝓝 (varianceScaledRadialPotential (r ^ 2) ‖z‖))) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => (∫ ω, p.rawCoreLogDet (N n) (H n) (W n) z ω
        ∂gaussianProfileLaw (N n)) / (N n : ℝ)) atTop
        (𝓝 (varianceScaledRadialPotential v ‖z‖)) := by
  have hroot : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hcont (z : ℂ) : ContinuousAt (fun r : ℝ => varianceScaledRadialPotential (r ^ 2) ‖z‖)
      (Real.sqrt v) := by
    exact (continuousAt_varianceScaledRadialPotential (radius := ‖z‖) (sq_pos_of_pos hroot)).comp
      (f := fun r : ℝ => r ^ 2)
      (show ContinuousAt (fun r : ℝ => r ^ 2) (Real.sqrt v) from (continuous_id.pow 2).continuousAt)
  have h := ae_tendsto_varying_radius_of_countable_dense (volume : Measure ℂ) hS hCount
    (fun z n r => p.scaledUnitCoreMean (N n) (H n) (W n) r z)
    (fun z r => varianceScaledRadialPotential (r ^ 2) ‖z‖)
    (fun n => Real.sqrt (p.coreMass (N n) (H n) (W n))) hroot hmass.sqrt
    (ae_of_all _ fun z n => p.scaledUnitCoreMean_monotoneOn (N n) (H n) (W n) z)
    hfixed (ae_of_all _ hcont)
  simpa only [p.rawCoreMean_eq_scaledUnitCoreMean, Real.sq_sqrt hv.le] using h

end CircularLawSection6.NoncompactProfile
