import CircularLawSection6.GaussianAllDimensions
import CircularLawSection6.RoutedCutoffExpectation
import CircularLawSection6.LowerCutoffSecondMoment

/-! # The concrete normalized circular Ginibre reference

All cyclic weights are exactly `1/N`. The row/displacement-to-entry map
preserves the IID circular Gaussian law. Energy, logarithmic L2 and
vanishing normalized variance are proved from the existing Gaussian
estimates. Only the source raw logarithmic probability limit is an input
to the final second-moment-limit theorem.
-/

open MeasureTheory ProbabilityTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

def ginibreMatrix (N : ℕ) (ω : ZMod N × ZMod N → ℂ) : Matrix (ZMod N) (ZMod N) ℂ :=
  weightedCyclicMatrix N (fun _ => 1 / (N : ℝ)) ω

def ginibreEntryAtoms (N : ℕ) (ω : ZMod N × ZMod N → ℂ) : ZMod N × ZMod N → ℂ :=
  fun k => ω (k.1, k.2 - k.1)

theorem ginibreEntryAtoms_measurePreserving (N : ℕ) [NeZero N] :
    MeasurePreserving (ginibreEntryAtoms N) (cyclicAtomLaw N circularComplexGaussian)
      (cyclicAtomLaw N circularComplexGaussian) := by
  apply CircularLawSection4.measurePreserving_pi_restrict_injective
    (fun k : ZMod N × ZMod N => (k.1, k.2 - k.1))
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp only at h₁ h₂
  apply Prod.ext h₁
  rw [h₁] at h₂
  exact sub_left_inj.mp h₂

theorem ginibreMatrix_entry (N : ℕ) (ω : ZMod N × ZMod N → ℂ) (i j : ZMod N) :
    ginibreMatrix N ω i j = (Real.sqrt (1 / (N : ℝ)) : ℂ) * ginibreEntryAtoms N ω (i, j) := rfl

theorem ginibreMatrix_measurable (N : ℕ) : Measurable (ginibreMatrix N) :=
  measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => weightedCyclicMatrix_measurable N _ i j

theorem ginibre_expected_energy (N : ℕ) [NeZero N] :
    Integrable (fun ω => hilbertSchmidtSq (ginibreMatrix N ω)) (cyclicAtomLaw N circularComplexGaussian) ∧
      (∫ ω, hilbertSchmidtSq (ginibreMatrix N ω) ∂cyclicAtomLaw N circularComplexGaussian) = N := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h := weightedCyclicMatrix_expected_energy N (fun _ => 1 / (N : ℝ))
    (fun _ => div_nonneg zero_le_one (Nat.cast_nonneg _)) circularComplexGaussian
    circularComplexGaussian_sq_integrable
  have heq : (∫ ω, cyclicEnergy N (ginibreMatrix N ω) ∂cyclicAtomLaw N circularComplexGaussian) = 1 := by
    simpa only [ginibreMatrix, circularComplexGaussian_secondMoment, mul_one, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one_div_cancel hN] using h.2
  have hpoint (ω : ZMod N × ZMod N → ℂ) :
      cyclicEnergy N (ginibreMatrix N ω) * (N : ℝ) = hilbertSchmidtSq (ginibreMatrix N ω) := by
    exact div_mul_cancel₀ _ hN
  refine ⟨?_, ?_⟩
  · have hi := h.1.mul_const (N : ℝ)
    exact hi.congr (ae_of_all _ hpoint)
  · calc
      _ = ∫ ω, cyclicEnergy N (ginibreMatrix N ω) * (N : ℝ) ∂cyclicAtomLaw N circularComplexGaussian := by
        simp only [hpoint]
      _ = _ := by rw [integral_mul_const, heq, one_mul]

theorem ginibre_shifted_expected_energy (N : ℕ) [NeZero N] (z : ℂ) :
    Integrable (fun ω => hilbertSchmidtSq (ginibreMatrix N ω - z • 1))
      (cyclicAtomLaw N circularComplexGaussian) ∧
      (∫ ω, hilbertSchmidtSq (ginibreMatrix N ω - z • 1)
        ∂cyclicAtomLaw N circularComplexGaussian) / (N : ℝ) ≤ 2 + 2 * ‖z‖ ^ 2 := by
  simpa only [one_smul, norm_one, one_pow, mul_one, ZMod.card] using
    expected_shifted_scaled_energy_le (cyclicAtomLaw N circularComplexGaussian)
      (ginibreMatrix N) (ginibreMatrix_measurable N) (ginibre_expected_energy N).1
      (by simpa only [ZMod.card] using (ginibre_expected_energy N).2) (1 : ℂ) z

theorem ginibre_raw_memLp (N : ℕ) [NeZero N] (z : ℂ) :
    MemLp (fun ω => matrixRawPotential (ginibreMatrix N ω - z • 1)) 2
      (cyclicAtomLaw N circularComplexGaussian) := by
  have h := (gaussian_cyclic_memLp_and_variance_all N (fun _ => 1 / (N : ℝ))
    (c := 1) (r := 1) zero_lt_one zero_lt_one z le_rfl).1
  simpa only [matrixRawPotential, ginibreMatrix, ZMod.card, cyclicRawLogDet,
    Complex.ofReal_one, one_smul, div_eq_mul_inv] using h.mul_const ((N : ℝ)⁻¹)

theorem ginibre_raw_variance_tendsto (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (z : ℂ) :
    Tendsto (fun n => variance (fun ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1))
      (cyclicAtomLaw (N n) circularComplexGaussian)) atTop (𝓝 0) := by
  have hb (n : ℕ) := normalized_variance_le
    (cyclicAtomLaw (N n) circularComplexGaussian)
    (cyclicRawLogDet (N n) (fun _ => 1 / (N n : ℝ)) 1 z)
    (Nat.cast_pos.mpr (NeZero.pos (N n)))
    (gaussian_cyclic_memLp_and_variance_all (N n) (fun _ => 1 / (N n : ℝ))
      (c := 1) (r := 1) zero_lt_one zero_lt_one z le_rfl).2
  have hlim : Tendsto (fun n => gaussianCyclicVarianceConstantAll 1 1 z *
      Real.log (Real.exp 1 * (N n : ℝ)) ^ 2 / (N n : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (tendsto_logEN_sq_div N hN).const_mul (gaussianCyclicVarianceConstantAll 1 1 z)
  apply squeeze_zero (fun _ => variance_nonneg _ _) _ hlim
  intro n
  simpa only [matrixRawPotential, ginibreMatrix, ZMod.card, cyclicRawLogDet,
    Complex.ofReal_one, one_smul] using hb n

theorem ginibre_raw_mean_of_probability (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (z : ℂ) {target : ℝ}
    (hBC12 : TendstoInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
      (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1)) target) :
    Tendsto (fun n => ∫ ω, matrixRawPotential (ginibreMatrix (N n) ω - z • 1)
      ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 target) := by
  apply deterministic_center_tendsto_of_tri_anchor_and_close
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian) _ _ target hBC12
  simpa only [matrixRawPotential, ginibreMatrix, ZMod.card, cyclicRawLogDet,
    Complex.ofReal_one, one_smul] using
    (gaussian_cyclic_concentration_all N hN (fun n _ => 1 / (N n : ℝ))
      (c := 1) (r := 1) zero_lt_one zero_lt_one z (fun _ => le_rfl)).2

theorem ginibre_raw_secondMoment_of_probability (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (z : ℂ) {target : ℝ}
    (hBC12 : TendstoInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
      (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1)) target) :
    Tendsto (fun n => ∫ ω, matrixRawPotential (ginibreMatrix (N n) ω - z • 1) ^ 2
      ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 (target ^ 2)) := by
  simpa only [zero_add] using secondMoment_tendsto_of_mean_variance
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian) _ (fun n => ginibre_raw_memLp (N n) z)
    (ginibre_raw_mean_of_probability N hN z hBC12) (ginibre_raw_variance_tendsto N hN z)

end CircularLawSection6
