import BernoulliSection10Complex.Section3Inputs
import BernoulliSection10Complex.MeasureTransport
import ShortRingAnchor.SecondMoment

/-! # Exact moments of the permitted input model -/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace BernoulliSection10Complex.SourceInputs

open ShortRingAnchor

set_option backward.isDefEq.respectTransparency false

theorem inputAtom_measurePreserving (μ : Measure ℂ) [IsProbabilityMeasure μ] (k : ℕ) :
    MeasurePreserving (fun ω : InputSpace => ω.1 k) (inputLaw μ) μ :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) k).comp
    (measurePreserving_fst (μ := Measure.infinitePi fun _ : ℕ => μ)
      (ν := Measure.infinitePi fun _ : ℕ => circularGaussianPairLaw))

theorem measurable_profileMatrix_entry {N : ℕ}
    (σ : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    Measurable (fun ω => profileMatrix σ ω i j) := by
  unfold profileMatrix
  fun_prop

theorem integrable_profileMatrix_entry
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {N : ℕ} (σ : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    Integrable (fun ω => profileMatrix σ ω i j) (inputLaw μ) := by
  letI := hμ.toIsProbabilityMeasure
  have hi := (inputAtom_measurePreserving μ (squareAtomIndex i j)).integrable_comp_of_integrable
    hμ.integrable_id
  exact hi.const_mul (σ i j : ℂ)

theorem profileMatrix_norm_sq {N : ℕ}
    (σ : Matrix (Fin N) (Fin N) ℝ) (ω : InputSpace) (i j : Fin N) :
    ‖profileMatrix σ ω i j‖ ^ 2 = σ i j ^ 2 * ‖ω.1 (squareAtomIndex i j)‖ ^ 2 := by
  simp only [profileMatrix, norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]

theorem integrable_profileMatrix_norm_sq
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {N : ℕ} (σ : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    Integrable (fun ω => ‖profileMatrix σ ω i j‖ ^ 2) (inputLaw μ) := by
  letI := hμ.toIsProbabilityMeasure
  simp only [profileMatrix_norm_sq]
  exact ((inputAtom_measurePreserving μ (squareAtomIndex i j)).integrable_comp_of_integrable
    hμ.integrable_sq).const_mul _

theorem integral_profileMatrix_entry
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {N : ℕ} (σ : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    (∫ ω, profileMatrix σ ω i j ∂inputLaw μ) = 0 := by
  letI := hμ.toIsProbabilityMeasure
  have he := (integral_comp_measurePreserving
    (inputAtom_measurePreserving μ (squareAtomIndex i j)) measurable_id.stronglyMeasurable).trans hμ.centered
  change (∫ ω : InputSpace, ω.1 (squareAtomIndex i j) ∂inputLaw μ) = 0 at he
  simp only [profileMatrix, integral_const_mul, he, mul_zero]

theorem integral_profileMatrix_norm_sq
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {N : ℕ} (σ : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    (∫ ω, ‖profileMatrix σ ω i j‖ ^ 2 ∂inputLaw μ) = σ i j ^ 2 := by
  letI := hμ.toIsProbabilityMeasure
  have he := (integral_comp_measurePreserving
    (inputAtom_measurePreserving μ (squareAtomIndex i j))
    (by fun_prop : StronglyMeasurable (fun x : ℂ => ‖x‖ ^ 2))).trans hμ.variance_one
  simp only [profileMatrix_norm_sq, integral_const_mul, he, mul_one]

theorem profileMatrix_row_moments
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {N : ℕ → ℕ} (σ : ∀ n, Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (hσ : ∀ n, DoublyStochasticProfile (σ n)) :
    CenteredMatrixRowSecondMomentInputs (inputLaw μ) (fun n ω => profileMatrix (σ n) ω) 1 := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · intro n i j
    exact integrable_profileMatrix_entry hμ (σ n) i j
  · intro n i j
    exact integrable_profileMatrix_norm_sq hμ (σ n) i j
  · intro n i j
    exact integral_profileMatrix_entry hμ (σ n) i j
  · intro n i
    simp only [integral_profileMatrix_norm_sq hμ]
    exact (hσ n).row i

theorem profileMatrix_energy_integrable
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {N : ℕ} (σ : Matrix (Fin N) (Fin N) ℝ) :
    Integrable (fun ω => squaredEntryMass (profileMatrix σ ω)) (inputLaw μ) := by
  exact integrable_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => integrable_profileMatrix_norm_sq hμ σ i j))

theorem integral_profileMatrix_energy
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {N : ℕ} (σ : Matrix (Fin N) (Fin N) ℝ) (hσ : DoublyStochasticProfile σ) :
    (∫ ω, squaredEntryMass (profileMatrix σ ω) ∂inputLaw μ) = N := by
  unfold squaredEntryMass
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => integrable_profileMatrix_norm_sq hμ σ i j))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_profileMatrix_norm_sq hμ σ _ j),
    integral_profileMatrix_norm_sq hμ, hσ.row]
  simp

end BernoulliSection10Complex.SourceInputs
