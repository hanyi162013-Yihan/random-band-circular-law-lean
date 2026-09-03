import ShortRingAnchor.ExplicitStieltjesRate
import ShortRingAnchor.HorizontalPolynomialNet
import ShortRingAnchor.ParameterArithmetic

/-!
# Lemma 3.5: explicit polynomial scales for the matrix-level reconstruction

If `B >= N^epsilon`, put `e = min epsilon 1` and choose height
`v = N^(-e/16)`. Then `B v^8 >= N^(e/2)`, the common v3 comparison
rate is `N^(-e/64)`, and `sqrt(v)` is smaller than that rate.
This is a valid reconstruction of the source argument, not a change to
the manuscript. It avoids dimension-dependent existential exponents.
-/

open Filter
open scoped Topology

noncomputable section
namespace ShortRingAnchor
open Arxiv2410V3

/-- Lemma 3.5: a positive bandwidth exponent bounded by one. -/
def localBulkEffectiveExponent (epsilon : ℝ) : ℝ := min epsilon 1

/-- Lemma 3.5: the fixed explicit exponent of the final polynomial rate. -/
def localBulkRateExponent (epsilon : ℝ) : ℝ := localBulkEffectiveExponent epsilon / 64

/-- Lemma 3.5: the comparison height for the shorter matrix-level proof. -/
def localBulkHeight (epsilon N : ℝ) : ℝ :=
  N ^ (-(localBulkEffectiveExponent epsilon / 16))

/-- Lemma 3.5: the displayed rate exponent is genuinely positive. -/
theorem localBulkRateExponent_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < localBulkRateExponent epsilon := by
  unfold localBulkRateExponent localBulkEffectiveExponent
  positivity

/-- Lemma 3.5: the chosen height stays above `N^(-1/8)`, so the proved
horizontal interpolation bound applies. -/
theorem localBulkHeight_lower {epsilon N : ℝ} (hN : 1 ≤ N) :
    N ^ (-(1 / 8 : ℝ)) ≤ localBulkHeight epsilon N := by
  apply Real.rpow_le_rpow_of_exponent_le hN
  have he : localBulkEffectiveExponent epsilon ≤ 1 := min_le_right _ _
  change -(1 / 8 : ℝ) ≤ -(localBulkEffectiveExponent epsilon / 16)
  linarith

/-- Lemma 3.5: verify exactly the scale premise in v3 (3.11). -/
theorem localBulkHeight_scale {epsilon N B : ℝ}
    (hN : 1 ≤ N) (hB : N ^ epsilon ≤ B) :
    N ^ (localBulkEffectiveExponent epsilon / 2) ≤
      B * localBulkHeight epsilon N ^ 8 := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hBe : N ^ localBulkEffectiveExponent epsilon ≤ B :=
    (Real.rpow_le_rpow_of_exponent_le hN (min_le_left _ _)).trans hB
  have hp : localBulkHeight epsilon N ^ 8 =
      N ^ (-(localBulkEffectiveExponent epsilon / 2)) := by
    unfold localBulkHeight
    rw [← Real.rpow_mul_natCast hN0.le]
    congr 1
    ring
  rw [hp]
  calc
    N ^ (localBulkEffectiveExponent epsilon / 2) =
        N ^ localBulkEffectiveExponent epsilon *
          N ^ (-(localBulkEffectiveExponent epsilon / 2)) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hBe (Real.rpow_nonneg hN0.le _)

/-- Lemma 3.5: the Poisson smoothing error is below the common comparison rate. -/
theorem sqrt_localBulkHeight_le_rate {epsilon N : ℝ}
    (hepsilon : 0 < epsilon) (hN : 1 ≤ N) :
    Real.sqrt (localBulkHeight epsilon N) ≤ N ^ (-localBulkRateExponent epsilon) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have he : 0 < localBulkEffectiveExponent epsilon := by
    unfold localBulkEffectiveExponent
    positivity
  unfold localBulkHeight localBulkRateExponent
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
  apply Real.rpow_le_rpow_of_exponent_le hN
  linarith

/-- Lemma 3.5: uniformly in the exact bandwidth, the actual v3 error at
the chosen height has the explicit common exponent `min(epsilon,1)/64`. -/
theorem eventually_formula311Error_localBulkHeight {C epsilon : ℝ}
    (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ B : ℝ,
      1 ≤ B → B ≤ (n : ℝ) → (n : ℝ) ^ epsilon ≤ B →
        formula311Error (n : ℝ) B (localBulkHeight epsilon n) C 32 ≤
          (n : ℝ) ^ (-localBulkRateExponent epsilon) := by
  have he : 0 < localBulkEffectiveExponent epsilon := by
    unfold localBulkEffectiveExponent
    positivity
  have hr := eventually_formula311Error_le_explicit_nat_allEta hC
    (show (0 : ℝ) ≤ 32 by norm_num) (show 0 < localBulkEffectiveExponent epsilon / 2 by positivity)
  filter_upwards [hr, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro B hB1 hBn hB
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hv : 0 < localBulkHeight epsilon n :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hnR) _
  have h := hn B (localBulkHeight epsilon n) hB1 hBn hv
    (localBulkHeight_scale hnR hB)
  convert h using 1
  congr 1
  unfold localBulkRateExponent
  ring

/-- Lemma 3.5: the comparison rate tends to zero along any growing dimensions. -/
theorem localBulk_rate_tendsto_zero {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {M : ℕ → ℕ} (hM : Tendsto M atTop atTop) :
    Tendsto (fun n => (M n : ℝ) ^ (-localBulkRateExponent epsilon)) atTop (nhds 0) :=
  (tendsto_rpow_atTop_zero_of_neg (neg_lt_zero.mpr (localBulkRateExponent_pos hepsilon))).comp
    (tendsto_natCast_atTop_atTop.comp hM)

end ShortRingAnchor
