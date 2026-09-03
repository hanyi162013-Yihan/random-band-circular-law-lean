import CircularLawSection6.FiniteCdfCutoffComparison
import Mathlib.MeasureTheory.Measure.Prod

/-! # CDF comparison on a coupling, expectations on the original laws

The finite-matrix comparison source may use a larger joint sample space.
Measure-preserving marginal maps transport the actual cutoff expectations
and energies, without replacing either original model by a surrogate law.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem integral_comp_of_measurePreserving_aes
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} {T : Ω → Ξ}
    (hT : MeasurePreserving T μ ν) (f : Ξ → ℝ) (hf : AEStronglyMeasurable f ν) :
    (∫ ω, f (T ω) ∂μ) = ∫ η, f η ∂ν := by
  have hm : AEStronglyMeasurable f (μ.map T) := by rwa [hT.map_eq]
  rw [← integral_map hT.measurable.aemeasurable hm, hT.map_eq]

theorem matrixCutoff_expectation_difference_of_coupled_cdf
    {Ω Ξ Λ ι κ : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)] [∀ n, MeasurableSpace (Λ n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Nonempty (ι n)]
    [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)] [∀ n, Nonempty (κ n)]
    (μ : ∀ n, Measure (Ω n)) (ν : ∀ n, Measure (Ξ n)) (ρ : ∀ n, Measure (Λ n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    [∀ n, IsProbabilityMeasure (ρ n)]
    (T : ∀ n, Λ n → Ω n) (S : ∀ n, Λ n → Ξ n)
    (hT : ∀ n, MeasurePreserving (T n) (ρ n) (μ n))
    (hS : ∀ n, MeasurePreserving (S n) (ρ n) (ν n))
    (A : ∀ n, Ω n → Matrix (ι n) (ι n) ℂ) (B : ∀ n, Ξ n → Matrix (κ n) (κ n) ℂ)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (hAdet : ∀ n, ∀ᵐ ω ∂μ n, (A n ω).det ≠ 0)
    (hBdet : ∀ n, ∀ᵐ ω ∂ν n, (B n ω).det ≠ 0)
    (hAE : ∀ n, Integrable (fun ω => hilbertSchmidtSq (A n ω)) (μ n))
    (hBE : ∀ n, Integrable (fun ω => hilbertSchmidtSq (B n ω)) (ν n))
    (CA CB : ℝ)
    (hAbound : ∀ n, (∫ ω, hilbertSchmidtSq (A n ω) ∂μ n) / (Fintype.card (ι n) : ℝ) ≤ CA)
    (hBbound : ∀ n, (∫ ω, hilbertSchmidtSq (B n ω) ∂ν n) / (Fintype.card (κ n) : ℝ) ≤ CB)
    (hcdf : ∀ R : ℝ, 1 ≤ R → TendstoInProbabilityTri ρ
      (fun n ω => matrixSquaredSingularCdfDistanceOn (A n (T n ω)) (B n (S n ω)) R) 0)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (∫ ω, matrixCutoffPotential (A n ω) a ∂μ n) -
      ∫ ω, matrixCutoffPotential (B n ω) a ∂ν n) atTop (𝓝 0) := by
  have hEA (n : ℕ) := integral_comp_of_measurePreserving_aes (hT n)
    (fun ω => hilbertSchmidtSq (A n ω)) (hAE n).aestronglyMeasurable
  have hEB (n : ℕ) := integral_comp_of_measurePreserving_aes (hS n)
    (fun ω => hilbertSchmidtSq (B n ω)) (hBE n).aestronglyMeasurable
  have hlim := matrixCutoff_expectation_difference_of_cdf_probability ρ
    (fun n ω => A n (T n ω)) (fun n ω => B n (S n ω))
    (fun n => (hA n).comp (hT n).measurable) (fun n => (hB n).comp (hS n).measurable)
    (fun n => (hT n).quasiMeasurePreserving.ae (hAdet n))
    (fun n => (hS n).quasiMeasurePreserving.ae (hBdet n))
    (fun n => (hT n).integrable_comp_of_integrable (hAE n))
    (fun n => (hS n).integrable_comp_of_integrable (hBE n)) CA CB
    (fun n => by rw [hEA]; exact hAbound n) (fun n => by rw [hEB]; exact hBbound n) hcdf ha
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [integral_comp_of_measurePreserving_aes (hT n) _
    (aestronglyMeasurable_matrixCutoffPotential (μ n) (A n) (hA n) (hAdet n) ha),
    integral_comp_of_measurePreserving_aes (hS n) _
    (aestronglyMeasurable_matrixCutoffPotential (ν n) (B n) (hB n) (hBdet n) ha)]

end CircularLawSection6
