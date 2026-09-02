import SubgaussianSection8.Atom
import BernoulliSection10.DensityEnergyLimit

/-! The actual energy limit and expected energy use second moments, not pointwise signs. -/
open MeasureTheory Filter Topology
open scoped BigOperators
noncomputable section
namespace SubgaussianSection8
open BernoulliSection10

set_option backward.isDefEq.respectTransparency false

theorem intervalMeanAtomSquare_integrable (A : Atom) (W s : ℕ) :
    Integrable (intervalMeanAtomSquare W s) (intervalRowsLaw W s A.law) := by
  apply Integrable.div_const
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro a _
  exact (intervalAtom_measurePreserving A.law W s i a).integrable_comp_of_integrable A.integrable_sq

theorem intervalMeanAtomSquare_integral
    (A : Atom) (W s : ℕ) (hW : 0 < W) (hs : 0 < s) :
    (∫ x, intervalMeanAtomSquare W s x ∂intervalRowsLaw W s A.law) = 1 := by
  have hi (i : Fin (s * W)) (a : Fin (3 * W)) :
      Integrable (fun x : IntervalRows W s => x i a ^ 2) (intervalRowsLaw W s A.law) :=
    (intervalAtom_measurePreserving A.law W s i a).integrable_comp_of_integrable A.integrable_sq
  have he (i : Fin (s * W)) (a : Fin (3 * W)) :
      (∫ x : IntervalRows W s, x i a ^ 2 ∂intervalRowsLaw W s A.law) = 1 := by
    exact (real_integral_comp_measurePreserving (intervalAtom_measurePreserving A.law W s i a)
      (by fun_prop : Measurable (fun x : ℝ => x ^ 2))).trans A.second_moment
  unfold BernoulliSection10.intervalMeanAtomSquare
  rw [integral_div, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun a _ => hi i a))]
  simp_rw [integral_finsetSum _ (fun a _ => hi _ a), he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, Nat.cast_mul]
  have hw : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp [hw, hs']

theorem cyclicMatrix_energy_integrable_and_integral
    (A : Atom) (W s : ℕ) (hW : 0 < W) :
    Integrable (fun x => (∑ i, ∑ j, ‖densityCyclicMatrix W s x i j‖ ^ 2) /
      (((s + 3) * W : ℕ) : ℝ)) (intervalRowsLaw W (s + 3) A.law) ∧
    (∫ x, (∑ i, ∑ j, ‖densityCyclicMatrix W s x i j‖ ^ 2) /
      (((s + 3) * W : ℕ) : ℝ) ∂intervalRowsLaw W (s + 3) A.law) = 1 := by
  simp_rw [densityCyclicMatrix_normalized_energy W s hW]
  exact ⟨intervalMeanAtomSquare_integrable A W (s + 3),
    intervalMeanAtomSquare_integral A W (s + 3) hW (by omega)⟩

theorem ring_energy_limit
    (A : Atom) (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n)
    (hWtop : Tendsto W atTop atTop) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) A.law)
      (fun n x => (∑ i, ∑ j, ‖densityCyclicMatrix (W n) (s n) x i j‖ ^ 2) /
        (((s n + 3) * W n : ℕ) : ℝ)) 1 :=
  density_ring_energy_limit_of_second_moment A.law A.integrable_sq A.second_moment W s hW hWtop

end SubgaussianSection8
