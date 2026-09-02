import BernoulliSection10.DensityEnergyLimit
import Mathlib.Probability.Moments.SubGaussian

/-!
# The symmetric Bernoulli atom and exact physical energy

The measure here is literally `(δ₁ + δ₋₁) / 2`. The cyclic matrix is the
existing physical three-neighbour block matrix, with every displayed atom
normalized by `1 / sqrt (3W)`. Its normalized Hilbert--Schmidt energy is
almost surely exactly one at each finite size. No density assumption or
invertibility assertion is used.

The existing physical-coordinate API writes the number of sites as `s + 3`.
The Section 8 range `m ≥ 4` is obtained by taking `s ≥ 1`; the energy identity
itself also holds at three sites.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace BernoulliSection8

open BernoulliSection10 BernoulliSection10.ProbabilityLimits ProbabilityTheory

/-- The genuine symmetric Bernoulli/Rademacher distribution on the real line. -/
def rademacherLaw : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac 1 + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (-1)

instance rademacherLaw_isProbabilityMeasure : IsProbabilityMeasure rademacherLaw where
  measure_univ := by simp [rademacherLaw, ENNReal.inv_two_add_inv_two]

@[simp] theorem rademacherLaw_singleton_one : rademacherLaw {1} = (2 : ℝ≥0∞)⁻¹ := by
  norm_num [rademacherLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']

@[simp] theorem rademacherLaw_singleton_neg_one :
    rademacherLaw {-1} = (2 : ℝ≥0∞)⁻¹ := by
  norm_num [rademacherLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']

/-- Every real-valued function is integrable against this two-point law. -/
theorem integrable_rademacherLaw (f : ℝ → ℝ) : Integrable f rademacherLaw := by
  unfold rademacherLaw
  apply Integrable.add_measure
  all_goals exact (integrable_dirac (by simp)).smul_measure (by norm_num)

theorem integral_rademacherLaw (f : ℝ → ℝ) :
    (∫ x, f x ∂rademacherLaw) = (f 1 + f (-1)) / 2 := by
  unfold rademacherLaw
  rw [integral_add_measure
    ((integrable_dirac (by simp)).smul_measure (by norm_num))
    ((integrable_dirac (by simp)).smul_measure (by norm_num))]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, smul_eq_mul]
  ring

@[simp] theorem rademacherLaw_mean_zero : (∫ x : ℝ, x ∂rademacherLaw) = 0 := by
  norm_num [integral_rademacherLaw]

@[simp] theorem rademacherLaw_second_moment :
    (∫ x : ℝ, x ^ 2 ∂rademacherLaw) = 1 := by
  norm_num [integral_rademacherLaw]

@[simp] theorem rademacherLaw_variance : variance (fun x : ℝ => x) rademacherLaw = 1 := by
  change variance id rademacherLaw = 1
  rw [variance_of_integral_eq_zero measurable_id.aemeasurable rademacherLaw_mean_zero]
  exact rademacherLaw_second_moment

/-- Its positive atom mass rules out every bounded-density certificate. -/
theorem rademacherLaw_not_boundedDensity (L : ℝ) :
    ¬IsBoundedDensityAtom rademacherLaw L := by
  intro h
  have hzero := h.measure_singleton 1
  rw [rademacherLaw_singleton_one] at hzero
  norm_num at hzero

theorem rademacherLaw_ae_sign : ∀ᵐ x ∂rademacherLaw, x = 1 ∨ x = -1 := by
  unfold rademacherLaw
  rw [ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure (by simp) _
  · exact Measure.ae_smul_measure (by simp) _

theorem rademacherLaw_ae_sq : ∀ᵐ x ∂rademacherLaw, x ^ 2 = 1 := by
  filter_upwards [rademacherLaw_ae_sign] with x hx
  rcases hx with rfl | rfl <;> norm_num

/-- The atom meets the real sub-Gaussian MGF convention used in Section 9,
with the explicit parameter one. -/
theorem rademacherLaw_subgaussian : HasSubgaussianMGF (fun x : ℝ => x) 1 rademacherLaw := by
  have hb : ∀ᵐ x ∂rademacherLaw, x ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [rademacherLaw_ae_sign] with x hx
    rcases hx with rfl | rfl <;> norm_num
  convert hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (measurable_id.aemeasurable : AEMeasurable (fun x : ℝ => x) rademacherLaw)
    hb rademacherLaw_mean_zero using 1 <;> first | rfl | norm_num

/-- All physical coordinates are signs simultaneously almost surely. -/
theorem rademacherRows_ae_sign (W s : ℕ) :
    ∀ᵐ x ∂intervalRowsLaw W s rademacherLaw, ∀ i a, x i a = 1 ∨ x i a = -1 := by
  apply ae_all_iff.2
  intro i
  apply ae_all_iff.2
  intro a
  exact (intervalAtom_measurePreserving rademacherLaw W s i a).quasiMeasurePreserving.ae
    rademacherLaw_ae_sign

/-- A deterministic sign configuration has exactly unit average squared atom. -/
theorem intervalMeanAtomSquare_eq_one_of_sign
    (W s : ℕ) (hW : 0 < W) (hs : 0 < s) (x : IntervalRows W s)
    (hx : ∀ i a, x i a = 1 ∨ x i a = -1) :
    intervalMeanAtomSquare W s x = 1 := by
  have hsq (i) (a) : x i a ^ 2 = 1 := by
    rcases hx i a with h | h <;> rw [h] <;> norm_num
  unfold intervalMeanAtomSquare
  simp only [hsq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Nat.cast_mul]
  have hW0 : (W : ℝ) ≠ 0 := by positivity
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  field_simp

/-- Exact finite-dimensional energy of the actual cyclic full-block matrix.
This is a pointwise identity on sign configurations, even when the matrix
or one of its block factors is singular. -/
theorem rademacherCyclicMatrix_energy_eq_one_of_sign
    (W s : ℕ) (hW : 0 < W) (x : IntervalRows W (s + 3))
    (hx : ∀ i a, x i a = 1 ∨ x i a = -1) :
    (∑ i, ∑ j, ‖densityCyclicMatrix W s x i j‖ ^ 2) /
      (((s + 3) * W : ℕ) : ℝ) = 1 := by
  rw [densityCyclicMatrix_normalized_energy W s hW]
  exact intervalMeanAtomSquare_eq_one_of_sign W (s + 3) hW (by omega) x hx

theorem rademacherCyclicMatrix_energy_ae_one (W s : ℕ) (hW : 0 < W) :
    ∀ᵐ x ∂intervalRowsLaw W (s + 3) rademacherLaw,
      (∑ i, ∑ j, ‖densityCyclicMatrix W s x i j‖ ^ 2) /
        (((s + 3) * W : ℕ) : ℝ) = 1 := by
  filter_upwards [rademacherRows_ae_sign W (s + 3)] with x hx
  exact rademacherCyclicMatrix_energy_eq_one_of_sign W s hW x hx

/-- The expected energy needed by Tao--Vu is one, at every finite size. -/
theorem rademacherCyclicMatrix_energy_integrable_and_integral (W s : ℕ) (hW : 0 < W) :
    Integrable (fun x => (∑ i, ∑ j, ‖densityCyclicMatrix W s x i j‖ ^ 2) /
      (((s + 3) * W : ℕ) : ℝ)) (intervalRowsLaw W (s + 3) rademacherLaw) ∧
    (∫ x, (∑ i, ∑ j, ‖densityCyclicMatrix W s x i j‖ ^ 2) /
      (((s + 3) * W : ℕ) : ℝ) ∂intervalRowsLaw W (s + 3) rademacherLaw) = 1 := by
  have h := rademacherCyclicMatrix_energy_ae_one W s hW
  refine ⟨(integrable_const 1).congr (Filter.EventuallyEq.symm h), ?_⟩
  rw [integral_congr_ae h]
  simp

/-- The energy limit is automatic for the Bernoulli model. The dimension,
bandwidth and number of sites can vary arbitrarily, provided `W > 0`.
This exact energy statement does not strengthen the hypotheses of the
Section 8 log-determinant or circular-law conclusions. -/
theorem rademacher_ring_energy_limit
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) rademacherLaw)
      (fun n x => (∑ i, ∑ j, ‖densityCyclicMatrix (W n) (s n) x i j‖ ^ 2) /
        (((s n + 3) * W n : ℕ) : ℝ)) 1 := by
  intro ε hε
  have hz (n : ℕ) :
      (intervalRowsLaw (W n) (s n + 3) rademacherLaw).real
        {x | ε ≤ |(∑ i, ∑ j, ‖densityCyclicMatrix (W n) (s n) x i j‖ ^ 2) /
          (((s n + 3) * W n : ℕ) : ℝ) - 1|} = 0 := by
    have hae := rademacherCyclicMatrix_energy_ae_one (W n) (s n) (hW n)
    have hempty : {x | ε ≤ |(∑ i, ∑ j,
        ‖densityCyclicMatrix (W n) (s n) x i j‖ ^ 2) /
        (((s n + 3) * W n : ℕ) : ℝ) - 1|} =ᵐ[
          intervalRowsLaw (W n) (s n + 3) rademacherLaw] (∅ : Set _) := by
      filter_upwards [hae] with x hx
      apply propext
      change (ε ≤ |(∑ i, ∑ j,
        ‖densityCyclicMatrix (W n) (s n) x i j‖ ^ 2) /
        (((s n + 3) * W n : ℕ) : ℝ) - 1|) ↔ False
      rw [hx]
      simp [not_le.mpr hε]
    rw [measureReal_congr hempty, measureReal_empty]
  simp_rw [hz]
  exact tendsto_const_nhds

end BernoulliSection8
