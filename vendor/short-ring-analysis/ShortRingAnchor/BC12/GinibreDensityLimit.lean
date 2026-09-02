import ShortRingAnchor.BC12.GinibreKernel
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Pointwise circular limit of the explicit Ginibre one-point function

This is the analytic calculation following BC12 Theorem 3.4.  We prove
exponential errors away from the unit circle, without taking a circular law
or Poisson large-deviation theorem as input.  No claim of uniform convergence
across the discontinuous unit-circle boundary is made.
-/

open Filter
open scoped BigOperators Topology

noncomputable section

namespace ShortRingAnchor.BC12

/-- The full exponential-series identity used in BC12's one-point calculation. -/
theorem hasSum_exp_series (x : ℝ) :
    HasSum (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ)) (Real.exp x) := by
  simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

/-- The positive rate function is `u - 1 - log u`; its strict positivity
off `u = 1` follows from the elementary strict logarithm inequality. -/
theorem ginibre_rate_neg {u : ℝ} (hu : 0 < u) (hu1 : u ≠ 1) :
    Real.log u + 1 - u < 0 := by
  linarith [Real.log_lt_sub_one_of_pos hu hu1]

/-- Combining the powers and exponentials in the finite-series estimates. -/
theorem ginibre_rate_identity (n : ℕ) {u : ℝ} (hu : 0 < u) :
    Real.exp (-((n : ℝ) * u)) * (u ^ n * Real.exp (n : ℝ)) =
      Real.exp ((n : ℝ) * (Real.log u + 1 - u)) := by
  rw [show u ^ n = Real.exp ((n : ℝ) * Real.log u) by
    rw [Real.exp_nat_mul, Real.exp_log hu]]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Outside the disk, the one-point density decays exponentially in dimension. -/
theorem poissonCutoff_scaled_le_rate (n : ℕ) {u : ℝ} (hu : 1 < u) :
    poissonCutoff n ((n : ℝ) * u) ≤
      Real.exp ((n : ℝ) * (Real.log u + 1 - u)) := by
  have hsum : expPartialSum n ((n : ℝ) * u) ≤ u ^ n * Real.exp (n : ℝ) := by
    calc
      expPartialSum n ((n : ℝ) * u) ≤
          ∑ k ∈ Finset.range n, u ^ n * ((n : ℝ) ^ k / (Nat.factorial k : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [mul_pow]
        have hpow := pow_le_pow_right₀ hu.le (Finset.mem_range.mp hk).le
        have hmul := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (n : ℝ) ^ k by positivity)
        exact (div_le_div_of_nonneg_right hmul (by positivity)).trans_eq (by ring)
      _ = u ^ n * expPartialSum n (n : ℝ) := by
        simp only [expPartialSum, Finset.mul_sum]
      _ ≤ u ^ n * Real.exp (n : ℝ) :=
        mul_le_mul_of_nonneg_left (expPartialSum_le_exp n (Nat.cast_nonneg n))
          (pow_nonneg (by linarith) n)
  exact (mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le).trans_eq
    (ginibre_rate_identity n (by linarith))

/-- A bound on the exponential-series tail, with all summability justified. -/
theorem exp_series_tail_scaled_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑' k : ℕ, ((n : ℝ) * u) ^ (k + n) / (Nat.factorial (k + n) : ℝ)) ≤
      u ^ n * Real.exp (n : ℝ) := by
  have hsn := (hasSum_exp_series (n : ℝ)).summable
  have hsnu := (hasSum_exp_series ((n : ℝ) * u)).summable
  have htailn := (summable_nat_add_iff n).2 hsn
  have htailnu := (summable_nat_add_iff n).2 hsnu
  have htail_le :
      (∑' k : ℕ, ((n : ℝ) * u) ^ (k + n) / (Nat.factorial (k + n) : ℝ)) ≤
        ∑' k : ℕ, u ^ n * ((n : ℝ) ^ (k + n) / (Nat.factorial (k + n) : ℝ)) := by
    apply htailnu.tsum_le_tsum _ (htailn.mul_left (u ^ n))
    intro k
    rw [mul_pow]
    have hpow : u ^ (k + n) ≤ u ^ n := pow_le_pow_of_le_one hu hu1 (by omega)
    have hmul := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ (n : ℝ) ^ (k + n) by positivity)
    exact (div_le_div_of_nonneg_right hmul (by positivity)).trans_eq (by ring)
  have htailn_le :
      (∑' k : ℕ, (n : ℝ) ^ (k + n) / (Nat.factorial (k + n) : ℝ)) ≤
        Real.exp (n : ℝ) := by
    have hsplit := hsn.sum_add_tsum_nat_add n
    rw [(hasSum_exp_series (n : ℝ)).tsum_eq] at hsplit
    have hfirst := expPartialSum_nonneg n (Nat.cast_nonneg n)
    change 0 ≤ ∑ k ∈ Finset.range n, (n : ℝ) ^ k / (Nat.factorial k : ℝ) at hfirst
    linarith
  calc
    _ ≤ _ := htail_le
    _ = u ^ n * ∑' k : ℕ, (n : ℝ) ^ (k + n) / (Nat.factorial (k + n) : ℝ) :=
      tsum_mul_left
    _ ≤ u ^ n * Real.exp (n : ℝ) :=
      mul_le_mul_of_nonneg_left htailn_le (pow_nonneg hu n)

/-- Inside the disk the deficit from one decays exponentially in dimension. -/
theorem one_sub_poissonCutoff_scaled_le_rate
    (n : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    1 - poissonCutoff n ((n : ℝ) * u) ≤
      Real.exp ((n : ℝ) * (Real.log u + 1 - u)) := by
  let x : ℝ := (n : ℝ) * u
  have hsplit := (hasSum_exp_series x).summable.sum_add_tsum_nat_add n
  rw [(hasSum_exp_series x).tsum_eq] at hsplit
  have htail : Real.exp x - expPartialSum n x =
      ∑' k : ℕ, x ^ (k + n) / (Nat.factorial (k + n) : ℝ) := by
    change expPartialSum n x + _ = Real.exp x at hsplit
    linarith
  have hexp : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  calc
    1 - poissonCutoff n ((n : ℝ) * u) =
        Real.exp (-x) * (Real.exp x - expPartialSum n x) := by
      unfold poissonCutoff
      dsimp [x] at hexp ⊢
      nlinarith [hexp]
    _ = Real.exp (-x) *
        (∑' k : ℕ, x ^ (k + n) / (Nat.factorial (k + n) : ℝ)) := by rw [htail]
    _ ≤ Real.exp (-x) * (u ^ n * Real.exp (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (exp_series_tail_scaled_le n hu.le hu1.le)
        (Real.exp_pos _).le
    _ = Real.exp ((n : ℝ) * (Real.log u + 1 - u)) := ginibre_rate_identity n hu

/-- The explicit exponential error converges to zero off the unit circle. -/
theorem ginibre_rate_tendsto_zero {u : ℝ} (hu : 0 < u) (hu1 : u ≠ 1) :
    Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (Real.log u + 1 - u)))
      atTop (nhds 0) := by
  have hexp : |Real.exp (Real.log u + 1 - u)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (ginibre_rate_neg hu hu1)
  simpa only [Real.exp_nat_mul] using tendsto_pow_atTop_nhds_zero_of_norm_lt_one hexp

/-- BC12 Theorem 3.4's one-point limit outside the unit disk. -/
theorem poissonCutoff_scaled_tendsto_zero {u : ℝ} (hu : 1 < u) :
    Tendsto (fun n : ℕ => poissonCutoff n ((n : ℝ) * u)) atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ginibre_rate_tendsto_zero (by linarith) (ne_of_gt hu))
    (fun n => poissonCutoff_nonneg n (by positivity))
    (fun n => poissonCutoff_scaled_le_rate n hu)

/-- BC12 Theorem 3.4's one-point limit inside the disk, away from its centre. -/
theorem poissonCutoff_scaled_tendsto_one {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun n : ℕ => poissonCutoff n ((n : ℝ) * u)) atTop (nhds 1) := by
  have hdeficit : Tendsto (fun n : ℕ => 1 - poissonCutoff n ((n : ℝ) * u))
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ginibre_rate_tendsto_zero hu (ne_of_lt hu1))
      (fun n => sub_nonneg.mpr (poissonCutoff_le_one n (by positivity)))
      (fun n => one_sub_poissonCutoff_scaled_le_rate n hu hu1)
  simpa using (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)
    from tendsto_const_nhds).sub hdeficit

/-- The centre of the disk is handled exactly, including the harmless
exclusion of the zero-dimensional initial term. -/
theorem poissonCutoff_zero_of_pos {n : ℕ} (hn : 0 < n) :
    poissonCutoff n 0 = 1 := by
  simp only [poissonCutoff, expPartialSum, neg_zero, Real.exp_zero, one_mul]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _hk hk0
    simp [zero_pow hk0]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hn))

/-- The complete scalar one-point limit, excluding only the discontinuity
at the unit-circle parameter. -/
theorem poissonCutoff_scaled_tendsto {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≠ 1) :
    Tendsto (fun n : ℕ => poissonCutoff n ((n : ℝ) * u)) atTop
      (nhds (if u < 1 then 1 else 0)) := by
  by_cases hu0 : u = 0
  · subst u
    simp only [mul_zero, zero_lt_one, if_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (poissonCutoff_zero_of_pos hn).symm
  · by_cases hlt : u < 1
    · simp only [if_pos hlt]
      exact poissonCutoff_scaled_tendsto_one (lt_of_le_of_ne hu (Ne.symm hu0)) hlt
    · simp only [if_neg hlt]
      exact poissonCutoff_scaled_tendsto_zero (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hu1))

/-- BC12 Theorem 3.4, at the level of the explicit normalized density:
pointwise convergence at every point off the unit circle. -/
theorem ginibreOnePointDensity_tendsto (w : ℂ) (hw : ‖w‖ ≠ 1) :
    Tendsto (fun n : ℕ => ginibreOnePointDensity n w) atTop
      (nhds (if ‖w‖ < 1 then 1 / Real.pi else 0)) := by
  have hsquare : ‖w‖ ^ 2 ≠ 1 := by
    intro h
    apply hw
    nlinarith [norm_nonneg w]
  have hlt : ‖w‖ ^ 2 < 1 ↔ ‖w‖ < 1 := by
    constructor <;> intro h <;> nlinarith [norm_nonneg w]
  have h := (poissonCutoff_scaled_tendsto (sq_nonneg ‖w‖) hsquare).div_const Real.pi
  simpa only [ginibreOnePointDensity, hlt, ite_div, zero_div] using h

end ShortRingAnchor.BC12
