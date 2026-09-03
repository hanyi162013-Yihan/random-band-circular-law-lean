/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/VarianceProfile.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Doubly stochastic variance profiles

This file formalizes the elementary variance-profile bookkeeping used in the proof of
arXiv:2410.16457v3, Proposition 3.4.  In particular, the last theorem is the computation
immediately below v3 formula (3.12); it is not delegated to the external universality input.
-/

namespace Arxiv2410V3

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Definition 1.2 / the hypothesis preceding v3 Proposition 3.4:
`bᵢⱼ ≥ 0`, and both the row and column sums of `bᵢⱼ²` are one. -/
structure DoublyStochasticVarianceProfile (ι : Type*) [Fintype ι] where
  coefficient : ι → ι → ℝ
  coefficient_nonneg : ∀ i j, 0 ≤ coefficient i j
  row_sq_sum : ∀ i, ∑ j, coefficient i j ^ 2 = 1
  col_sq_sum : ∀ j, ∑ i, coefficient i j ^ 2 = 1

/-- The finite-dimensional unpacking of
`B⁻¹ = sup_(i,j) bᵢⱼ²` from v3 Proposition 3.4.

The maximum-attainment field makes the definition exact rather than merely an upper bound.
-/
structure IsBandwidth (P : DoublyStochasticVarianceProfile ι) (B : ℝ) : Prop where
  pos : 0 < B
  sq_le_inv : ∀ i j, P.coefficient i j ^ 2 ≤ B⁻¹
  attained : ∃ i j, P.coefficient i j ^ 2 = B⁻¹

/-- The entrywise form `bᵢⱼ ≤ 1 / √B` of the bandwidth bound. -/
theorem coefficient_le_inv_sqrt (P : DoublyStochasticVarianceProfile ι) {B : ℝ}
    (hB : IsBandwidth P B) (i j : ι) :
    P.coefficient i j ≤ 1 / Real.sqrt B := by
  have hsqrt : 0 < Real.sqrt B := Real.sqrt_pos.2 hB.pos
  have hsqrt_sq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB.pos.le
  have hinv_sq : (1 / Real.sqrt B) ^ 2 = B⁻¹ := by
    rw [div_pow]
    simp only [one_pow]
    rw [hsqrt_sq]
    simp [one_div]
  have hb0 := P.coefficient_nonneg i j
  have hinv0 : 0 ≤ 1 / Real.sqrt B := by positivity
  have hsq := hB.sq_le_inv i j
  rw [← hinv_sq] at hsq
  nlinarith [sq_nonneg (P.coefficient i j + 1 / Real.sqrt B)]

/-- The exact bandwidth in v3 Proposition 3.4 also satisfies `1 ≤ B`: every squared
coefficient is at most its row sum `1`, including the coefficient attaining `B⁻¹`.
-/
theorem one_le_bandwidth [Nonempty ι]
    (P : DoublyStochasticVarianceProfile ι) {B : ℝ} (hB : IsBandwidth P B) :
    1 ≤ B := by
  rcases hB.attained with ⟨i, j, hij⟩
  have hcoeff : P.coefficient i j ^ 2 ≤ 1 := by
    calc
      P.coefficient i j ^ 2 ≤ ∑ k, P.coefficient i k ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (P.coefficient i k))
          (Finset.mem_univ j)
      _ = 1 := P.row_sq_sum i
  rw [hij] at hcoeff
  have hmul := mul_le_mul_of_nonneg_right hcoeff hB.pos.le
  calc
    1 = B⁻¹ * B := (inv_mul_cancel₀ hB.pos.ne').symm
    _ ≤ 1 * B := hmul
    _ = B := one_mul B

/-- Each row forces the v3 bandwidth to be at most the matrix dimension: `B ≤ n`.
This is one of the elementary inequalities used when reading polynomial rates from (3.11). -/
theorem bandwidth_le_card [Nonempty ι] (P : DoublyStochasticVarianceProfile ι) {B : ℝ}
    (hB : IsBandwidth P B) : B ≤ Fintype.card ι := by
  let i : ι := Classical.choice inferInstance
  have hsum : ∑ j, P.coefficient i j ^ 2 ≤ ∑ _j : ι, B⁻¹ :=
    Finset.sum_le_sum fun j _ => hB.sq_le_inv i j
  rw [P.row_sq_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hB0 : 0 < B := hB.pos
  rw [inv_eq_one_div] at hsum
  have hquot : 1 ≤ (Fintype.card ι : ℝ) / B := by
    simpa [div_eq_mul_inv] using hsum
  have := (le_div_iff₀ hB0).mp hquot
  simpa using this

/-- The normalized third-moment ledger below v3 formula (3.12):

`(1/n) * ∑ᵢⱼ bᵢⱼ³ ≤ 1 / √B`.

Only row stochasticity is used; column stochasticity remains part of the faithful model.
-/
theorem normalized_sum_cube_le [Nonempty ι]
    (P : DoublyStochasticVarianceProfile ι) {B : ℝ} (hB : IsBandwidth P B) :
    (∑ i, ∑ j, P.coefficient i j ^ 3) / (Fintype.card ι : ℝ) ≤
      1 / Real.sqrt B := by
  have hpoint (i j : ι) :
      P.coefficient i j ^ 3 ≤
        (1 / Real.sqrt B) * P.coefficient i j ^ 2 := by
    calc
      P.coefficient i j ^ 3 =
          P.coefficient i j ^ 2 * P.coefficient i j := by ring
      _ ≤ P.coefficient i j ^ 2 * (1 / Real.sqrt B) :=
        mul_le_mul_of_nonneg_left (coefficient_le_inv_sqrt P hB i j) (sq_nonneg _)
      _ = (1 / Real.sqrt B) * P.coefficient i j ^ 2 := by ring
  have hsum :
      (∑ i, ∑ j, P.coefficient i j ^ 3) ≤
        ∑ i, ∑ j, (1 / Real.sqrt B) * P.coefficient i j ^ 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
  have hcard : 0 < (Fintype.card ι : ℝ) := by positivity
  apply (div_le_iff₀ hcard).2
  calc
    ∑ i, ∑ j, P.coefficient i j ^ 3
        ≤ ∑ i, ∑ j, (1 / Real.sqrt B) * P.coefficient i j ^ 2 := hsum
    _ = (Fintype.card ι : ℝ) * (1 / Real.sqrt B) := by
      simp_rw [← Finset.mul_sum, P.row_sq_sum]
      simp [mul_comm]
    _ = (1 / Real.sqrt B) * (Fintype.card ι : ℝ) := by ring

/-- The third-moment contribution in the line below v3 formula (3.12): if
`M₃ = 𝔼|ξ|³`, then
`M₃ ((1/n) ∑ᵢⱼ bᵢⱼ³) ≤ M₃ / √B`.

This is a deterministic consequence of `normalized_sum_cube_le`; no probabilistic
universality input is used here. -/
theorem third_moment_mul_normalized_sum_cube_le [Nonempty ι]
    (P : DoublyStochasticVarianceProfile ι) {B M3 : ℝ}
    (hB : IsBandwidth P B) (hM3 : 0 ≤ M3) :
    M3 * ((∑ i, ∑ j, P.coefficient i j ^ 3) / (Fintype.card ι : ℝ)) ≤
      M3 / Real.sqrt B := by
  calc
    M3 * ((∑ i, ∑ j, P.coefficient i j ^ 3) / (Fintype.card ι : ℝ))
        ≤ M3 * (1 / Real.sqrt B) :=
      mul_le_mul_of_nonneg_left (normalized_sum_cube_le P hB) hM3
    _ = M3 / Real.sqrt B := by ring

end Arxiv2410V3

