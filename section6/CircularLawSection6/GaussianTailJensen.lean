import CircularLawSection6.GaussianProfile
import CircularLawSection6.DeterminantJensen
import CircularLawSection6.InvariantPhaseAverage

/-! # Expected Jensen lower bound for the actual Gaussian profile

Rotation invariance and the product-space Fubini step are discharged here.
The two raw-log integrability inputs and almost-sure nonvanishing of the
shifted core remain explicit analytic obligations; they are not axioms.
-/

open MeasureTheory Real

noncomputable section

namespace CircularLawSection6

theorem tailRotation_joint_measurable (N : ℕ) [NeZero N] (S : Finset (ZMod N)) :
    Measurable (fun v : ℝ × (ZMod N × ZMod N → ℂ) =>
      tailRotation N S (Circle.exp v.1) v.2) := by
  classical
  apply measurable_pi_lambda
  intro k
  by_cases hk : k.2 ∈ S <;>
    simp only [tailRotation, rotateCyclicAtoms, hk, if_true, if_false, Circle.coe_one, one_mul]
  · exact (measurable_pi_apply k).comp measurable_snd
  · simp only [Circle.coe_exp]
    fun_prop

theorem measurable_log_norm_matrix_det {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Ω → Matrix ι ι ℂ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j)) :
    Measurable (fun ω => Real.log ‖(A ω).det‖) := by
  classical
  apply Real.measurable_log.comp
  apply Measurable.norm
  simp only [Matrix.det_apply]
  fun_prop

namespace NoncompactProfile

def rawProfileLogDet (p : NoncompactProfile) (N : ℕ) [NeZero N] (W : ℝ) (z : ℂ)
    (ω : ZMod N × ZMod N → ℂ) : ℝ := Real.log ‖(p.matrix N W ω - z • 1).det‖

def rawCoreLogDet (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) (z : ℂ)
    (ω : ZMod N × ZMod N → ℂ) : ℝ := Real.log ‖(p.coreMatrix N H W ω - z • 1).det‖

theorem rawProfileLogDet_measurable (p : NoncompactProfile) (N : ℕ) [NeZero N]
    (W : ℝ) (z : ℂ) : Measurable (p.rawProfileLogDet N W z) := by
  apply measurable_log_norm_matrix_det
  intro i j
  simp only [matrix, weightedCyclicMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

theorem phaseAverage_rawProfileLogDet_eq (p : NoncompactProfile) (N H : ℕ) [NeZero N]
    (W : ℝ) (z : ℂ) (ω : ZMod N × ZMod N → ℂ) :
    phaseAverage (fun θ => p.rawProfileLogDet N W z
      (tailRotation N (coreOffsets N H) (Circle.exp θ) ω)) =
    circleAverage (fun w => Real.log ‖(w • p.tailMatrix N H W ω +
      (p.coreMatrix N H W ω - z • 1)).det‖) 0 1 := by
  unfold phaseAverage circleAverage
  simp only [smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  unfold rawProfileLogDet
  dsimp only
  rw [p.matrix_tailRotation]
  congr 3
  simp only [circleMap_zero, Complex.ofReal_one, one_mul, Circle.coe_exp]
  abel

theorem gaussian_expected_tail_jensen (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) (z : ℂ)
    (hfull : Integrable (p.rawProfileLogDet N W z) (gaussianProfileLaw N))
    (hcore : Integrable (p.rawCoreLogDet N H W z) (gaussianProfileLaw N))
    (hdet : ∀ᵐ ω ∂gaussianProfileLaw N, (p.coreMatrix N H W ω - z • 1).det ≠ 0) :
    (∫ ω, p.rawCoreLogDet N H W z ω ∂gaussianProfileLaw N) / (N : ℝ) ≤
      (∫ ω, p.rawProfileLogDet N W z ω ∂gaussianProfileLaw N) / (N : ℝ) := by
  have hav := invariant_phaseAverage_integral
    (fun θ => tailRotation N (coreOffsets N H) (Circle.exp θ))
    (tailRotation_joint_measurable N _)
    (fun θ => gaussianProfileLaw_tailRotation_preserving N _ (Circle.exp θ))
    (p.rawProfileLogDet_measurable N W z) hfull
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  rw [← hav.2]
  apply integral_mono_ae hcore hav.1
  filter_upwards [hdet] with ω hω
  rw [p.phaseAverage_rawProfileLogDet_eq]
  exact log_norm_det_le_circleAverage_affine_det
    (p.coreMatrix N H W ω - z • 1) (p.tailMatrix N H W ω) hω

end NoncompactProfile
end CircularLawSection6
