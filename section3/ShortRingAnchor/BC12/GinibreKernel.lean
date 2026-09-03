import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary estimates for the explicit complex Ginibre one-point function

BC12, Section 3, Theorems 3.3--3.4 give the finite-dimensional correlation
formula.  Its derivation from Gaussian matrix entries is an external formula
in this development.  This file proves the estimates on that explicit formula;
it does not assume a circular law, logarithmic integrability, or tightness.

For variance-normalized matrices the mean empirical eigenvalue density is
`pi⁻¹ exp(-n |w|²) sum_{k<n} (n |w|²)^k/k!`.
-/

open scoped BigOperators

noncomputable section

namespace ShortRingAnchor.BC12

/-- The Poisson partial sum in BC12's one-point correlation formula. -/
def expPartialSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, x ^ k / (Nat.factorial k : ℝ)

/-- The exponential factor times the partial sum; no probabilistic
interpretation is assumed in this definition. -/
def poissonCutoff (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) * expPartialSum n x

/-- BC12 Theorem 3.4's density after scaling eigenvalues by `sqrt n`. -/
def ginibreOnePointDensity (n : ℕ) (w : ℂ) : ℝ :=
  poissonCutoff n ((n : ℝ) * ‖w‖ ^ 2) / Real.pi

/-- Positivity of the finite sum in the one-point formula. -/
theorem expPartialSum_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ expPartialSum n x := by
  exact Finset.sum_nonneg fun k _ => div_nonneg (pow_nonneg hx k) (by positivity)

/-- The partial exponential series is bounded by the whole exponential. -/
theorem expPartialSum_le_exp (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    expPartialSum n x ≤ Real.exp x :=
  Real.sum_le_exp_of_nonneg hx n

/-- The normalized one-point formula is nonnegative. -/
theorem poissonCutoff_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ poissonCutoff n x :=
  mul_nonneg (Real.exp_pos _).le (expPartialSum_nonneg n hx)

/-- The uniform density bound needed near the logarithmic singularity. -/
theorem poissonCutoff_le_one (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    poissonCutoff n x ≤ 1 := by
  calc
    poissonCutoff n x ≤ Real.exp (-x) * Real.exp x :=
      mul_le_mul_of_nonneg_left (expPartialSum_le_exp n hx) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- A finite-series exponential tilt, avoiding any Poisson tail theorem. -/
theorem expPartialSum_le_tilt (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    expPartialSum n x ≤ (2 : ℝ) ^ n * Real.exp (x / 2) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range n) :
      x ^ k / (Nat.factorial k : ℝ) ≤
        (2 : ℝ) ^ n * ((x / 2) ^ k / (Nat.factorial k : ℝ)) := by
    have hid : x ^ k = (2 : ℝ) ^ k * (x / 2) ^ k := by
      rw [← mul_pow]
      congr 1
      ring
    rw [hid, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (Finset.mem_range.mp hk).le) (by positivity)
  calc
    expPartialSum n x ≤
        ∑ k ∈ Finset.range n, (2 : ℝ) ^ n *
          ((x / 2) ^ k / (Nat.factorial k : ℝ)) := Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ n * expPartialSum n (x / 2) := by
      simp only [expPartialSum, Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ n * Real.exp (x / 2) :=
      mul_le_mul_of_nonneg_left (expPartialSum_le_exp n (by positivity)) (by positivity)

/-- The elementary exponential tail estimate behind the Gaussian envelope. -/
theorem poissonCutoff_le_exp_tilt (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    poissonCutoff n x ≤ Real.exp ((n : ℝ) - x / 2) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    poissonCutoff n x ≤
        Real.exp (-x) * ((2 : ℝ) ^ n * Real.exp (x / 2)) :=
      mul_le_mul_of_nonneg_left (expPartialSum_le_tilt n hx) (Real.exp_pos _).le
    _ ≤ Real.exp (-x) * ((Real.exp 1) ^ n * Real.exp (x / 2)) := by
      gcongr
    _ = Real.exp ((n : ℝ) - x / 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-- For every positive dimension the diagonal density has one Gaussian
envelope, uniformly in dimension.  This is an elementary consequence of
the finite correlation formula, not a random-matrix input. -/
theorem poissonCutoff_scaled_le_gaussian
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u) :
    poissonCutoff n ((n : ℝ) * u) ≤ Real.exp (1 - u / 4) := by
  by_cases hsmall : u ≤ 4
  · exact (poissonCutoff_le_one n (by positivity)).trans
      (by simpa using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 - u / 4 by linarith))
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hu4 : 4 ≤ u := (lt_of_not_ge hsmall).le
    refine (poissonCutoff_le_exp_tilt n (by positivity : 0 ≤ (n : ℝ) * u)).trans ?_
    apply Real.exp_le_exp.mpr
    have hmul := mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr hn1) (show 1 - u / 2 ≤ 0 by linarith)
    nlinarith

/-- BC12's normalized one-point density is nonnegative. -/
theorem ginibreOnePointDensity_nonneg (n : ℕ) (w : ℂ) :
    0 ≤ ginibreOnePointDensity n w :=
  div_nonneg (poissonCutoff_nonneg n (by positivity)) Real.pi_pos.le

/-- The bound `rho_n ≤ 1/pi` is proved from the explicit finite formula. -/
theorem ginibreOnePointDensity_le_inv_pi (n : ℕ) (w : ℂ) :
    ginibreOnePointDensity n w ≤ 1 / Real.pi :=
  div_le_div_of_nonneg_right (poissonCutoff_le_one n (by positivity)) Real.pi_pos.le

/-- A common integrable-tail candidate for the logarithmic observables;
the bound itself holds globally, not just on bounded sets. -/
theorem ginibreOnePointDensity_le_gaussian {n : ℕ} (hn : 0 < n) (w : ℂ) :
    ginibreOnePointDensity n w ≤ Real.exp (1 - ‖w‖ ^ 2 / 4) / Real.pi :=
  div_le_div_of_nonneg_right
    (poissonCutoff_scaled_le_gaussian hn (sq_nonneg _)) Real.pi_pos.le

end ShortRingAnchor.BC12
