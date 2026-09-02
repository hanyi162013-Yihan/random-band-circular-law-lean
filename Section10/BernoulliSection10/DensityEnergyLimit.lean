import BernoulliSection10.PhysicalMatrixEntries
import BernoulliSection10.PhysicalProbabilityInstances
import BernoulliSection10.ProbabilityLimits

/-! # Equation (10.57) for the literal cyclic matrix -/

open Filter MeasureTheory Topology
open scoped BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace BernoulliSection10

open ProbabilityLimits

theorem intervalMeanAtomSquare_tendsto_of_second_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h2 : Integrable (fun x : ℝ => x ^ 2) μ) (hmean : (∫ x : ℝ, x ^ 2 ∂μ) = 1)
    (W s : ℕ → ℕ) (hd : Tendsto (fun n => s n * W n * (3 * W n)) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (intervalRowsLaw (W n) (s n) μ).real
      {x | ε ≤ |intervalMeanAtomSquare (W n) (s n) x - 1|}) atTop (𝓝 0) := by
  have h := finiteIID_average_tendsto_in_probability μ (fun x : ℝ => x ^ 2)
    (by fun_prop) h2 _ hd hε
  rw [hmean] at h
  have he (n : ℕ) : (intervalRowsLaw (W n) (s n) μ).real
      {x | ε ≤ |intervalMeanAtomSquare (W n) (s n) x - 1|} =
      (Measure.pi fun _ : Fin (s n * W n * (3 * W n)) => μ).real
        {x | ε ≤ |(∑ i, x i ^ 2) / ((s n * W n * (3 * W n) : ℕ) : ℝ) - 1|} := by
    have hp := flattenIntervalAtoms_measurePreserving μ (W n) (s n)
    have hm : Measurable (fun x : Fin (s n * W n * (3 * W n)) → ℝ =>
        (∑ i, x i ^ 2) / ((s n * W n * (3 * W n) : ℕ) : ℝ)) := by fun_prop
    have hs : MeasurableSet {x : Fin (s n * W n * (3 * W n)) → ℝ |
        ε ≤ |(∑ i, x i ^ 2) / ((s n * W n * (3 * W n) : ℕ) : ℝ) - 1|} :=
      measurableSet_le measurable_const (hm.sub_const 1).norm
    simp only [measureReal_def]
    rw [← hp.map_eq, Measure.map_apply hp.measurable hs]
    apply congrArg ENNReal.toReal
    apply congrArg (intervalRowsLaw (W n) (s n) μ)
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, intervalMeanAtomSquare_eq_flat]
  simp_rw [he]
  exact h

/-- Equation (10.57) needs only a probability law with second moment one:
no density, centering, third moment, or fourth moment enters this theorem. -/
theorem density_ring_energy_limit_of_second_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h2 : Integrable (fun x : ℝ => x ^ 2) μ) (hmean : (∫ x : ℝ, x ^ 2 ∂μ) = 1)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) μ)
      (fun n x => (∑ i, ∑ j, ‖densityCyclicMatrix (W n) (s n) x i j‖ ^ 2) /
        (((s n + 3) * W n : ℕ) : ℝ)) 1 := by
  have hd : Tendsto (fun n => (s n + 3) * W n * (3 * W n)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hWtop
    apply Eventually.of_forall
    intro n
    exact (Nat.le_mul_of_pos_left (W n) (by omega : 0 < s n + 3)).trans
      (Nat.le_mul_of_pos_right _ (Nat.mul_pos (by decide) (hW n)))
  intro ε hε
  simp_rw [densityCyclicMatrix_normalized_energy (W _) (s _) (hW _)]
  exact intervalMeanAtomSquare_tendsto_of_second_moment μ h2 hmean W
    (fun n => s n + 3) hd hε

theorem density_ring_energy_limit
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop) :
    letI := hμ.toIsProbabilityMeasure
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) μ)
      (fun n x => (∑ i, ∑ j, ‖densityCyclicMatrix (W n) (s n) x i j‖ ^ 2) /
        (((s n + 3) * W n : ℕ) : ℝ)) 1 := by
  letI := hμ.toIsProbabilityMeasure
  exact density_ring_energy_limit_of_second_moment μ hμ.integrable_sq hμ.variance_one
    W s hW hWtop

end BernoulliSection10
