import CircularLawSection6.CutoffIntegrability
import CircularLawSections56.Section6.LiteralIndicatorModel

/-! # A common-atom coupling for rerouted band rows

The same independent row/slot atoms may be sent to the original cyclic
columns or to the columns of periodic blocks. Each injective routing has
the same row energy. If the routings agree outside a set of boundary rows,
their expected squared HS difference is at most four times the boundary
row count, for normalized weights and atoms. No independence between the
two coupled matrices is assumed. The contiguous-block routing and its
boundary count are separate finite combinatorial obligations.
-/

open MeasureTheory
open TaoVuReplacement
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def routedBandMatrix (route : ι → κ → ι) (b : κ → ℂ) (ω : ι × κ → ℂ) : Matrix ι ι ℂ :=
  fun i j => ∑ s, if j = route i s then b s * ω (i, s) else 0

theorem routedBandMatrix_measurable (route : ι → κ → ι) (b : κ → ℂ) :
    Measurable (routedBandMatrix route b) := by
  classical
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  unfold routedBandMatrix
  apply Finset.measurable_sum
  intro s _
  by_cases h : j = route i s
  · simpa only [if_pos h] using measurable_const.mul (measurable_pi_apply (i, s))
  · simpa only [if_neg h] using (measurable_const : Measurable (fun _ : ι × κ → ℂ => (0 : ℂ)))

theorem routedBand_row_energy (route : ι → κ → ι)
    (hr : ∀ i, Function.Injective (route i)) (b : κ → ℂ) (ω : ι × κ → ℂ) (i : ι) :
    (∑ j, ‖routedBandMatrix route b ω i j‖ ^ 2) = ∑ s, ‖b s * ω (i, s)‖ ^ 2 :=
  CircularLawSections56.Section6.sparse_row_norm_square_sum (route i) (hr i) _

def maskMatrixRows (S : Finset ι) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => if i ∈ S then A i j else 0

theorem maskMatrixRows_hilbertSchmidtSq (S : Finset ι) (A : Matrix ι ι ℂ) :
    hilbertSchmidtSq (maskMatrixRows S A) = ∑ i ∈ S, ∑ j, ‖A i j‖ ^ 2 := by
  unfold hilbertSchmidtSq
  calc
    _ = ∑ i ∈ S, ∑ j, ‖maskMatrixRows S A i j‖ ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      simp [maskMatrixRows, hi]
    _ = _ := Finset.sum_congr rfl (fun i hi => by simp only [maskMatrixRows, if_pos hi])

theorem routedBand_difference_energy_le
    (route₁ route₂ : ι → κ → ι)
    (h₁ : ∀ i, Function.Injective (route₁ i)) (h₂ : ∀ i, Function.Injective (route₂ i))
    (S : Finset ι) (hgood : ∀ i ∉ S, ∀ s, route₁ i s = route₂ i s)
    (b : κ → ℂ) (ω : ι × κ → ℂ) :
    hilbertSchmidtSq (routedBandMatrix route₁ b ω - routedBandMatrix route₂ b ω) ≤
      4 * ∑ i ∈ S, ∑ s, ‖b s * ω (i, s)‖ ^ 2 := by
  have heq : routedBandMatrix route₁ b ω - routedBandMatrix route₂ b ω =
      maskMatrixRows S (routedBandMatrix route₁ b ω) -
        maskMatrixRows S (routedBandMatrix route₂ b ω) := by
    ext i j
    by_cases hi : i ∈ S
    · simp [maskMatrixRows, hi]
    · simp [maskMatrixRows, hi, routedBandMatrix, hgood i hi]
  rw [heq]
  have h := hilbertSchmidtSq_sub_le
    (maskMatrixRows S (routedBandMatrix route₁ b ω))
    (maskMatrixRows S (routedBandMatrix route₂ b ω))
  simp_rw [maskMatrixRows_hilbertSchmidtSq, routedBand_row_energy route₁ h₁,
    routedBand_row_energy route₂ h₂] at h
  convert h using 1 <;> ring

omit [DecidableEq ι] in
theorem routedAtoms_expected_boundary_energy (S : Finset ι) (b : κ → ℂ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν) :
    Integrable (fun ω : ι × κ → ℂ => ∑ i ∈ S, ∑ s, ‖b s * ω (i, s)‖ ^ 2)
      (Measure.pi (fun _ : ι × κ => ν)) ∧
      (∫ ω : ι × κ → ℂ, (∑ i ∈ S, ∑ s, ‖b s * ω (i, s)‖ ^ 2)
        ∂Measure.pi (fun _ : ι × κ => ν)) =
        (S.card : ℝ) * (∑ s, ‖b s‖ ^ 2) * ∫ u : ℂ, ‖u‖ ^ 2 ∂ν := by
  let μ := Measure.pi (fun _ : ι × κ => ν)
  have hMP (i : ι) (s : κ) : MeasurePreserving
      (fun ω : ι × κ → ℂ => ω (i, s)) μ ν := measurePreserving_eval _ (i, s)
  have ht (i : ι) (s : κ) : Integrable (fun ω => ‖b s‖ ^ 2 * ‖ω (i, s)‖ ^ 2) μ :=
    ((hMP i s).integrable_comp_of_integrable hInt).const_mul _
  have hc (i : ι) (s : κ) : (∫ ω, ‖ω (i, s)‖ ^ 2 ∂μ) = ∫ u : ℂ, ‖u‖ ^ 2 ∂ν := by
    have hf : AEStronglyMeasurable (fun u : ℂ => ‖u‖ ^ 2)
        (Measure.map (fun ω : ι × κ → ℂ => ω (i, s)) μ) := by
      rw [(hMP i s).map_eq]
      exact hInt.aestronglyMeasurable
    calc
      _ = ∫ u : ℂ, ‖u‖ ^ 2 ∂Measure.map (fun ω : ι × κ → ℂ => ω (i, s)) μ :=
        (integral_map (hMP i s).measurable.aemeasurable hf).symm
      _ = _ := by rw [(hMP i s).map_eq]
  have hi := integrable_finsetSum S (fun i _ =>
    integrable_finsetSum Finset.univ (fun s _ => ht i s))
  simp_rw [norm_mul, mul_pow]
  refine ⟨hi, ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun s _ => ht i s))]
  simp_rw [integral_finsetSum _ (fun s _ => ht _ s), integral_const_mul, hc]
  simp only [← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
  ring

theorem routedBand_expected_difference_energy_le
    (route₁ route₂ : ι → κ → ι)
    (h₁ : ∀ i, Function.Injective (route₁ i)) (h₂ : ∀ i, Function.Injective (route₂ i))
    (S : Finset ι) (hgood : ∀ i ∉ S, ∀ s, route₁ i s = route₂ i s)
    (b : κ → ℂ) (hb : ∑ s, ‖b s‖ ^ 2 = 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hMoment : (∫ u : ℂ, ‖u‖ ^ 2 ∂ν) = 1) :
    Integrable (fun ω => hilbertSchmidtSq
      (routedBandMatrix route₁ b ω - routedBandMatrix route₂ b ω))
      (Measure.pi (fun _ : ι × κ => ν)) ∧
      (∫ ω, hilbertSchmidtSq (routedBandMatrix route₁ b ω - routedBandMatrix route₂ b ω)
        ∂Measure.pi (fun _ : ι × κ => ν)) ≤ 4 * (S.card : ℝ) := by
  have henergy := routedAtoms_expected_boundary_energy S b ν hInt
  have hbound := henergy.1.const_mul 4
  have hi : Integrable (fun ω => hilbertSchmidtSq
      (routedBandMatrix route₁ b ω - routedBandMatrix route₂ b ω))
      (Measure.pi (fun _ : ι × κ => ν)) := by
    apply hbound.mono'
    · exact (continuous_hilbertSchmidtSq.measurable.comp
        ((routedBandMatrix_measurable route₁ b).sub
          (routedBandMatrix_measurable route₂ b))).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hilbertSchmidtSq_nonneg _)]
      exact routedBand_difference_energy_le route₁ route₂ h₁ h₂ S hgood b ω
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, 4 * ∑ i ∈ S, ∑ s, ‖b s * ω (i, s)‖ ^ 2
        ∂Measure.pi (fun _ : ι × κ => ν) :=
      integral_mono hi hbound (fun ω => routedBand_difference_energy_le route₁ route₂ h₁ h₂ S hgood b ω)
    _ = _ := by rw [integral_const_mul, henergy.2, hb, hMoment]; ring

end CircularLawSection6
