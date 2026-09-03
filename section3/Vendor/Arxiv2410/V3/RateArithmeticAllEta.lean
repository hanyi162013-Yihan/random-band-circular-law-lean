/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/RateArithmeticAllEta.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.RateArithmetic

/-!
# Rate bookkeeping for every positive imaginary part

The first, fixed-`eta` conclusion (3.9) of arXiv:2410.16457v3, Proposition 3.4 does not
impose the bounded-domain condition `Im eta ≤ 5` that is used later for the uniform
conclusion (3.10).  This file removes that condition from the finite-`n` rate construction.

The key observation is that the scale assumption and the variance-profile inequalities
`1 ≤ B ≤ n` control the denominators directly.  In particular, no upper bound on `v` and
no bandwidth-growth hypothesis are used below.
-/

namespace Arxiv2410V3

/-! ## Denominator consequences of the scale assumption -/

/-- The square-root denominator in the first term of v3 (3.11) is at least one.
This is the auxiliary estimate that also compares the second term with the first. -/
theorem one_le_sqrt_bandwidth_mul_pow_four_of_scale
    {n B v c : ℝ} (hn : 1 ≤ n) (hv : 0 < v) (hc : 0 ≤ c)
    (hscale : Real.rpow n c ≤ B * v ^ 8) :
    1 ≤ Real.sqrt B * v ^ 4 := by
  calc
    1 ≤ Real.rpow n (c / 2) := Real.one_le_rpow hn (by positivity)
    _ ≤ Real.sqrt B * v ^ 4 :=
      rpow_half_le_sqrt_mul_pow_four (zero_lt_one.trans_le hn) hv hscale

/-- Under `1 ≤ B` and the v3 scale assumption, the denominator `B v⁵` of the
second term in (3.11) dominates the denominator `sqrt(B) v⁴` of the first term. -/
theorem sqrt_bandwidth_mul_pow_four_le_bandwidth_mul_pow_five
    {n B v c : ℝ} (hn : 1 ≤ n) (hB : 1 ≤ B) (hv : 0 < v) (hc : 0 ≤ c)
    (hscale : Real.rpow n c ≤ B * v ^ 8) :
    Real.sqrt B * v ^ 4 ≤ B * v ^ 5 := by
  have hsqrtB : 1 ≤ Real.sqrt B := (Real.one_le_sqrt).2 hB
  have hunit := one_le_sqrt_bandwidth_mul_pow_four_of_scale hn hv hc hscale
  have hsqrtBv : 1 ≤ Real.sqrt B * v := by
    by_cases hvone : v ≤ 1
    · have hvpow : v ^ 4 ≤ v := by
        calc
          v ^ 4 = Real.rpow v (4 : ℝ) := (Real.rpow_natCast v 4).symm
          _ ≤ v :=
            Real.rpow_le_self_of_le_one hv.le hvone
              (by norm_num : (1 : ℝ) ≤ 4)
      exact hunit.trans
        (mul_le_mul_of_nonneg_left hvpow (Real.sqrt_nonneg B))
    · have hvone' : 1 ≤ v := le_of_not_ge hvone
      calc
        1 = 1 * 1 := by ring
        _ ≤ Real.sqrt B * v :=
          mul_le_mul hsqrtB hvone' zero_le_one (Real.sqrt_nonneg B)
  have hnonneg : 0 ≤ Real.sqrt B * v ^ 4 :=
    mul_nonneg (Real.sqrt_nonneg B) (pow_nonneg hv.le 4)
  calc
    Real.sqrt B * v ^ 4 = (Real.sqrt B * v ^ 4) * 1 := by ring
    _ ≤ (Real.sqrt B * v ^ 4) * (Real.sqrt B * v) :=
      mul_le_mul_of_nonneg_left hsqrtBv hnonneg
    _ = B * v ^ 5 := by
      calc
        (Real.sqrt B * v ^ 4) * (Real.sqrt B * v) =
            (Real.sqrt B) ^ 2 * v ^ 5 := by ring
        _ = B * v ^ 5 := by rw [Real.sq_sqrt (zero_le_one.trans hB)]

/-- The third denominator in v3 (3.11) satisfies
`n^(c/8) ≤ sqrt(n) v` for every `v > 0`; no upper bound on `v` is needed. -/
theorem rpow_eighth_le_sqrt_n_mul_v
    {n B v c : ℝ} (hn : 1 ≤ n) (hv : 0 < v) (hBn : B ≤ n)
    (hscale : Real.rpow n c ≤ B * v ^ 8) :
    Real.rpow n (c / 8) ≤ Real.sqrt n * v := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hhalf := rpow_half_le_sqrt_n_mul_pow_four hn0 hv hBn hscale
  have hsqrt_le_nsq : Real.sqrt n ≤ n ^ 2 := by
    calc
      Real.sqrt n ≤ n := (Real.sqrt_le_self_iff).2 (Or.inr hn)
      _ ≤ n ^ 2 := by nlinarith [sq_nonneg (n - 1)]
  have hpow :
      (Real.rpow n (c / 8)) ^ 4 ≤ (Real.sqrt n * v) ^ 4 := by
    calc
      (Real.rpow n (c / 8)) ^ 4 = Real.rpow n (c / 2) := by
        calc
          (Real.rpow n (c / 8)) ^ 4 =
              Real.rpow n ((c / 8) * (4 : ℝ)) :=
            (Real.rpow_mul_natCast hn0.le (c / 8) 4).symm
          _ = Real.rpow n (c / 2) := by congr 1; ring
      _ ≤ Real.sqrt n * v ^ 4 := hhalf
      _ ≤ n ^ 2 * v ^ 4 :=
        mul_le_mul_of_nonneg_right hsqrt_le_nsq (pow_nonneg hv.le 4)
      _ = (Real.sqrt n * v) ^ 4 := by
        rw [mul_pow]
        rw [show (Real.sqrt n) ^ 4 = n ^ 2 by
          rw [show (Real.sqrt n) ^ 4 = ((Real.sqrt n) ^ 2) ^ 2 by ring,
            Real.sq_sqrt hn0.le]]
  exact (pow_le_pow_iff_left₀
    (Real.rpow_nonneg hn0.le _) (mul_nonneg (Real.sqrt_nonneg n) hv.le)
      (by norm_num : (4 : ℕ) ≠ 0)).1 hpow

/-- The fourth denominator in v3 (3.11) satisfies
`n^(c/4) ≤ sqrt(B) v²` for every `v > 0`, using `1 ≤ B`. -/
theorem rpow_quarter_le_sqrt_bandwidth_mul_v_sq
    {n B v c : ℝ} (hn : 1 ≤ n) (hB : 1 ≤ B) (hv : 0 < v)
    (hscale : Real.rpow n c ≤ B * v ^ 8) :
    Real.rpow n (c / 4) ≤ Real.sqrt B * v ^ 2 := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hhalf := rpow_half_le_sqrt_mul_pow_four hn0 hv hscale
  have hsqrt_le_B : Real.sqrt B ≤ B :=
    (Real.sqrt_le_self_iff).2 (Or.inr hB)
  have hpow :
      (Real.rpow n (c / 4)) ^ 2 ≤ (Real.sqrt B * v ^ 2) ^ 2 := by
    calc
      (Real.rpow n (c / 4)) ^ 2 = Real.rpow n (c / 2) := by
        calc
          (Real.rpow n (c / 4)) ^ 2 =
              Real.rpow n ((c / 4) * (2 : ℝ)) :=
            (Real.rpow_mul_natCast hn0.le (c / 4) 2).symm
          _ = Real.rpow n (c / 2) := by congr 1; ring
      _ ≤ Real.sqrt B * v ^ 4 := hhalf
      _ ≤ B * v ^ 4 :=
        mul_le_mul_of_nonneg_right hsqrt_le_B (pow_nonneg hv.le 4)
      _ = (Real.sqrt B * v ^ 2) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (zero_le_one.trans hB)]
        ring
  exact (pow_le_pow_iff_left₀
    (Real.rpow_nonneg hn0.le _)
      (mul_nonneg (Real.sqrt_nonneg B) (pow_nonneg hv.le 2))
      (by norm_num : (2 : ℕ) ≠ 0)).1 hpow

/-! ## All-`v` estimates for the four terms in (3.11) -/

/-- For every positive `v`, the second term in v3 (3.11) is bounded by the same
`C n^(-c/2)` expression as the first term. -/
theorem formula311_second_term_le_rpow_allEta
    {n B v C c : ℝ} (hn : 1 ≤ n) (hB : 1 ≤ B) (hv : 0 < v)
    (hC : 0 ≤ C) (hc : 0 < c)
    (hscale : Real.rpow n c ≤ B * v ^ 8) :
    C / (B * v ^ 5) ≤ C * Real.rpow n (-(c / 2)) := by
  have hdenomPos : 0 < Real.sqrt B * v ^ 4 := by positivity
  calc
    C / (B * v ^ 5) ≤ C / (Real.sqrt B * v ^ 4) :=
      div_le_div_of_nonneg_left hC hdenomPos
        (sqrt_bandwidth_mul_pow_four_le_bandwidth_mul_pow_five
          hn hB hv hc.le hscale)
    _ ≤ C * Real.rpow n (-(c / 2)) :=
      formula311_first_term_le_rpow (zero_lt_one.trans_le hn) hv hC hc hscale

/-- Log-free part of the third term in v3 (3.11), valid for every positive `v`. -/
theorem formula311_third_algebraic_factor_le_rpow_allEta
    {n B v CD c : ℝ} (hn : 1 ≤ n) (hv : 0 < v) (hCD : 0 ≤ CD)
    (hBn : B ≤ n) (hscale : Real.rpow n c ≤ B * v ^ 8) :
    CD / (Real.sqrt n * v) ≤ CD * Real.rpow n (-(c / 8)) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hpow : 0 < Real.rpow n (c / 8) := Real.rpow_pos_of_pos hn0 _
  calc
    CD / (Real.sqrt n * v) ≤ CD / Real.rpow n (c / 8) :=
      div_le_div_of_nonneg_left hCD hpow
        (rpow_eighth_le_sqrt_n_mul_v hn hv hBn hscale)
    _ = CD * Real.rpow n (-(c / 8)) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_neg hn0.le]
      simp only [div_eq_mul_inv]

/-- With `sqrt(log n) ≤ n^(c/16)`, the complete third term in v3 (3.11) is
at most `CD n^(-c/16)` for every positive `v`. -/
theorem formula311_third_term_le_sixteenth_rpow_allEta
    {n B v CD c : ℝ} (hn : 1 ≤ n) (hv : 0 < v) (hCD : 0 ≤ CD)
    (hBn : B ≤ n) (hscale : Real.rpow n c ≤ B * v ^ 8)
    (hlog : Real.sqrt (Real.log n) ≤ Real.rpow n (c / 16)) :
    CD * Real.sqrt (Real.log n) / (Real.sqrt n * v) ≤
      CD * Real.rpow n (-(c / 16)) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hbase := formula311_third_algebraic_factor_le_rpow_allEta
    (CD := CD * Real.sqrt (Real.log n)) hn hv
      (mul_nonneg hCD (Real.sqrt_nonneg (Real.log n))) hBn hscale
  have hrpow0 : 0 ≤ Real.rpow n (-(c / 8)) := Real.rpow_nonneg hn0.le _
  have habsorb :
      Real.rpow n (c / 16) * Real.rpow n (-(c / 8)) =
        Real.rpow n (-(c / 16)) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  calc
    CD * Real.sqrt (Real.log n) / (Real.sqrt n * v) ≤
        (CD * Real.sqrt (Real.log n)) * Real.rpow n (-(c / 8)) := hbase
    _ ≤ (CD * Real.rpow n (c / 16)) * Real.rpow n (-(c / 8)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog hCD) hrpow0
    _ = CD * Real.rpow n (-(c / 16)) := by
      calc
        (CD * Real.rpow n (c / 16)) * Real.rpow n (-(c / 8)) =
            CD * (Real.rpow n (c / 16) * Real.rpow n (-(c / 8))) := by ring
        _ = CD * Real.rpow n (-(c / 16)) := by rw [habsorb]

/-- Log-free part of the fourth term in v3 (3.11), valid for every positive `v`. -/
theorem formula311_fourth_algebraic_factor_le_rpow_allEta
    {n B v C c : ℝ} (hn : 1 ≤ n) (hB : 1 ≤ B) (hv : 0 < v)
    (hC : 0 ≤ C) (hscale : Real.rpow n c ≤ B * v ^ 8) :
    C / (Real.sqrt B * v ^ 2) ≤ C * Real.rpow n (-(c / 4)) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hpow : 0 < Real.rpow n (c / 4) := Real.rpow_pos_of_pos hn0 _
  calc
    C / (Real.sqrt B * v ^ 2) ≤ C / Real.rpow n (c / 4) :=
      div_le_div_of_nonneg_left hC hpow
        (rpow_quarter_le_sqrt_bandwidth_mul_v_sq hn hB hv hscale)
    _ = C * Real.rpow n (-(c / 4)) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_neg hn0.le]
      simp only [div_eq_mul_inv]

/-- With `sqrt(log n) ≤ n^(c/8)`, the complete fourth term in v3 (3.11) is
at most `C n^(-c/8)` for every positive `v`. -/
theorem formula311_fourth_term_le_eighth_rpow_allEta
    {n B v C c : ℝ} (hn : 1 ≤ n) (hB : 1 ≤ B) (hv : 0 < v)
    (hC : 0 ≤ C) (hscale : Real.rpow n c ≤ B * v ^ 8)
    (hlog : Real.sqrt (Real.log n) ≤ Real.rpow n (c / 8)) :
    C * Real.sqrt (Real.log n) / (Real.sqrt B * v ^ 2) ≤
      C * Real.rpow n (-(c / 8)) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hbase := formula311_fourth_algebraic_factor_le_rpow_allEta
    (C := C * Real.sqrt (Real.log n)) hn hB hv
      (mul_nonneg hC (Real.sqrt_nonneg (Real.log n))) hscale
  have hrpow0 : 0 ≤ Real.rpow n (-(c / 4)) := Real.rpow_nonneg hn0.le _
  have habsorb :
      Real.rpow n (c / 8) * Real.rpow n (-(c / 4)) =
        Real.rpow n (-(c / 8)) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  calc
    C * Real.sqrt (Real.log n) / (Real.sqrt B * v ^ 2) ≤
        (C * Real.sqrt (Real.log n)) * Real.rpow n (-(c / 4)) := hbase
    _ ≤ (C * Real.rpow n (c / 8)) * Real.rpow n (-(c / 4)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog hC) hrpow0
    _ = C * Real.rpow n (-(c / 8)) := by
      calc
        (C * Real.rpow n (c / 8)) * Real.rpow n (-(c / 4)) =
            C * (Real.rpow n (c / 8) * Real.rpow n (-(c / 4))) := by ring
        _ = C * Real.rpow n (-(c / 8)) := by rw [habsorb]

/-! ## Uniform all-`v` rate certificate -/

/-- All-positive-`v` asymptotic closure of v3 `(3.11) ⇒ (3.9)` on real dimensions.
The resulting checked exponent is `c/32`. -/
theorem eventually_formula311_polynomialRateCertificate_allEta
    {C CD c : ℝ} (hC : 0 ≤ C) (hCD : 0 ≤ CD) (hc : 0 < c) :
    ∀ᶠ n : ℝ in Filter.atTop, ∀ B v : ℝ,
      1 ≤ B → B ≤ n → 0 < v → Real.rpow n c ≤ B * v ^ 8 →
        Nonempty (PolynomialRateCertificate n (formula311Error n B v C CD)) := by
  have hlogThird := eventually_sqrt_log_le_rpow (show 0 < c / 16 by linarith)
  have hlogFourth := eventually_sqrt_log_le_rpow (show 0 < c / 8 by linarith)
  have hfirst := eventually_const_mul_rpow_neg_le_quarter
    hC (show 0 < c / 32 by linarith) (show c / 32 < c / 2 by linarith)
  have hthird := eventually_const_mul_rpow_neg_le_quarter
    hCD (show 0 < c / 32 by linarith) (show c / 32 < c / 16 by linarith)
  have hfourth := eventually_const_mul_rpow_neg_le_quarter
    hC (show 0 < c / 32 by linarith) (show c / 32 < c / 8 by linarith)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), hlogThird, hlogFourth,
      hfirst, hthird, hfourth] with n hn hnlogThird hnlogFourth
        hnfirst hnthird hnfourth
  intro B v hB hBn hv hscale
  refine ⟨polynomialRateCertificate_of_termwise
    (exponent := c / 32) (show 0 < c / 32 by linarith) ?_ ?_ ?_ ?_⟩
  · exact (formula311_first_term_le_rpow
      (zero_lt_one.trans_le hn) hv hC hc hscale).trans hnfirst
  · exact (formula311_second_term_le_rpow_allEta
      hn hB hv hC hc hscale).trans hnfirst
  · exact (formula311_third_term_le_sixteenth_rpow_allEta
      hn hv hCD hBn hscale hnlogThird).trans hnthird
  · exact (formula311_fourth_term_le_eighth_rpow_allEta
      hn hB hv hC hscale hnlogFourth).trans hnfourth

/-- Natural-dimension form of the all-positive-`v` rate construction. -/
theorem eventually_formula311_polynomialRateCertificate_nat_allEta
    {C CD c : ℝ} (hC : 0 ≤ C) (hCD : 0 ≤ CD) (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ B v : ℝ,
      1 ≤ B → B ≤ (n : ℝ) → 0 < v →
        Real.rpow (n : ℝ) c ≤ B * v ^ 8 →
          Nonempty (PolynomialRateCertificate (n : ℝ)
            (formula311Error (n : ℝ) B v C CD)) := by
  exact tendsto_natCast_atTop_atTop.eventually
    (eventually_formula311_polynomialRateCertificate_allEta hC hCD hc)

/-- Explicit natural threshold for the all-positive-`v` rate construction in v3 (3.9).
The threshold depends only on the fixed constants `C`, `CD`, and `c`. -/
theorem exists_threshold_formula311_polynomialRateCertificate_nat_allEta
    {C CD c : ℝ} (hC : 0 ≤ C) (hCD : 0 ≤ CD) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ B v : ℝ,
      1 ≤ B → B ≤ (n : ℝ) → 0 < v →
        Real.rpow (n : ℝ) c ≤ B * v ^ 8 →
          Nonempty (PolynomialRateCertificate (n : ℝ)
            (formula311Error (n : ℝ) B v C CD)) := by
  exact Filter.eventually_atTop.1
    (eventually_formula311_polynomialRateCertificate_nat_allEta hC hCD hc)

end Arxiv2410V3

