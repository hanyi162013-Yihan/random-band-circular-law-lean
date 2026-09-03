import CircularLawSection6.UniformCyclicSourceBridge

/-! # Local source inputs on an arbitrary positive dimension window

The common exceptional set is still indexed only by countably many
finite dimensions, not by the uncountable set of length sequences.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem cyclicBlock_all_interval_lengths_of_source_inputs_ae
    (H lo hi : ℕ → ℕ) (hlo : ∀ n, 0 < lo n) (hfit : ∀ n, 2 * H n + 1 ≤ lo n)
    (b : ∀ n, Fin (2 * H n + 1) → ℂ) (hb : ∀ n, ∑ s, ‖b n s‖ ^ 2 = 1) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ σ : Measure ℝ, IsProbabilityMeasure σ →
      (∀ᵐ s ∂σ, 0 ≤ s) → Integrable (fun s : ℝ => s ^ 2) σ →
      (∀ M : ℕ → ℕ+, (∀ n, lo n ≤ (M n : ℕ) ∧ (M n : ℕ) ≤ hi n) →
        CyclicGinibreCdfInput M H b z ∧ GinibreSquaredTestInput M z σ) →
      ∀ a : ℝ, 0 < a → ∀ m : ℕ → ℕ,
        (∀ n, lo n ≤ m n ∧ m n ≤ hi n) →
        Tendsto (fun n => cyclicBlockExpectedCutoff (m n) (H n) (b n) circularComplexGaussian z a)
          atTop (𝓝 (∫ s, Real.log (max s a) ∂σ)) := by
  have hdA : ∀ᵐ z ∂(volume : Measure ℂ), ∀ n (m : ℕ+),
      ∀ᵐ ω ∂Measure.pi (fun _ : Fin (m : ℕ) × Fin (2 * H n + 1) => circularComplexGaussian),
        (routedBandMatrix (cyclicFinSlot (N := (m : ℕ)) (H n)) (b n) ω - z • 1).det ≠ 0 :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (fun m => ae_shifted_matrix_det_ne_zero _
      (routedBandMatrix (cyclicFinSlot (N := (m : ℕ)) (H n)) (b n)) (routedBandMatrix_measurable _ _)))
  have hdB : ∀ᵐ z ∂(volume : Measure ℂ), ∀ m : ℕ+,
      ∀ᵐ ω ∂cyclicAtomLaw (m : ℕ) circularComplexGaussian, (ginibreMatrix (m : ℕ) ω - z • 1).det ≠ 0 :=
    ae_all_iff.2 (fun m => ae_shifted_matrix_det_ne_zero _ (ginibreMatrix (m : ℕ)) (ginibreMatrix_measurable _))
  filter_upwards [hdA, hdB] with z hzA hzB
  intro σ hσ hσpos hσ2 hsource a ha m hm
  let : IsProbabilityMeasure σ := hσ
  let M (n : ℕ) : ℕ+ := ⟨m n, (hlo n).trans_le (hm n).1⟩
  let μ (n : ℕ) := Measure.pi (fun _ : Fin (M n : ℕ) × Fin (2 * H n + 1) => circularComplexGaussian)
  let ν (n : ℕ) := cyclicAtomLaw (M n) circularComplexGaussian
  let A (n : ℕ) := routedBandMatrix (cyclicFinSlot (N := (M n : ℕ)) (H n)) (b n)
  have hA (n : ℕ) := routedBandMatrix_measurable (cyclicFinSlot (N := (M n : ℕ)) (H n)) (b n)
  have henergy (n : ℕ) := routedBand_expected_energy (cyclicFinSlot (N := (M n : ℕ)) (H n))
    (cyclicFinSlot_injective ((hfit n).trans (hm n).1)) (b n) (hb n)
    circularComplexGaussian circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment
  have heA (n : ℕ) := expected_shifted_scaled_energy_le (μ n) (A n) (hA n)
    (henergy n).1 (henergy n).2 (1 : ℂ) z
  simp only [one_smul, norm_one, one_pow, mul_one] at heA
  obtain ⟨hcdf, hweak⟩ := hsource M hm
  have hcmp := matrixCutoff_expectation_difference_of_coupled_cdf μ ν (fun n => (μ n).prod (ν n))
    (fun _ => Prod.fst) (fun _ => Prod.snd) (fun _ => measurePreserving_fst) (fun _ => measurePreserving_snd)
    (fun n ω => A n ω - z • 1) (fun n ω => ginibreMatrix (M n) ω - z • 1)
    (fun n => (hA n).sub measurable_const) (fun n => (ginibreMatrix_measurable (M n)).sub measurable_const)
    (fun n => hzA n (M n)) (fun n => hzB (M n))
    (fun n => (heA n).1) (fun n => (ginibre_shifted_expected_energy (M n) z).1)
    (2 + 2 * ‖z‖ ^ 2) (2 + 2 * ‖z‖ ^ 2) (fun n => (heA n).2)
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (M n) z).2) hcdf ha
  have hg := matrixCutoff_expectation_of_squared_singular_probability ν
    (fun n ω => ginibreMatrix (M n) ω - z • 1)
    (fun n => (ginibreMatrix_measurable (M n)).sub measurable_const) (fun n => hzB (M n))
    (fun n => (ginibre_shifted_expected_energy (M n) z).1) (2 + 2 * ‖z‖ ^ 2)
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (M n) z).2)
    σ hσpos hσ2 hweak ha
  have hlim := hcmp.add hg
  simp only [sub_add_cancel, zero_add] at hlim
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  let : NeZero (m n) := ⟨((hlo n).trans_le (hm n).1).ne'⟩
  exact (cyclicBlockExpectedCutoff_eq (m n) (H n) (b n) circularComplexGaussian z a).symm

end CircularLawSection6
