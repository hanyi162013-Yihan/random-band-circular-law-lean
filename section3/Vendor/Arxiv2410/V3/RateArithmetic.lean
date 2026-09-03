/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/RateArithmetic.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.TraceComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Finite-`n` rate bookkeeping for v3 Proposition 3.4

The paper compresses the passage from (3.11) to (3.9) into “each term is smaller than a
negative power.”  This file verifies both the finite-`n` algebra and the missing asymptotic
bookkeeping.  In particular, it proves `sqrt(log n) ≤ n^δ` eventually for every `δ > 0`,
absorbs all fixed coefficients, and constructs the rate certificate required by (3.9).
-/

namespace Arxiv2410V3

/-- Positivity of the mesoscopic scale in v3 Corollary 3.5:
`B^(-1/8) n^c > 0` whenever `B,n > 0`. -/
theorem corollary35_scale_pos
    {n B c : ℝ} (hB : 0 < B) (hn : 0 < n) :
    0 < Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c := by
  exact mul_pos (Real.rpow_pos_of_pos hB _) (Real.rpow_pos_of_pos hn _)

/-- The scale condition in v3 Proposition 3.4 forces the bandwidth parameter to be positive.
This is useful because the paper subsequently divides by `B` and `sqrt B`. -/
theorem bandwidth_pos_of_scale
    {n B v c : ℝ} (hn : 0 < n) (hv : 0 < v)
    (hscale : Real.rpow n c ≤ B * v ^ 8) :
    0 < B := by
  have hprod : 0 < B * v ^ 8 :=
    (Real.rpow_pos_of_pos hn c).trans_le hscale
  exact pos_of_mul_pos_left hprod (pow_nonneg hv.le 8)

/-- Square-root form of the v3 scale assumption `n^c ≤ B v⁸`:
`n^(c/2) ≤ sqrt(B) v⁴`.

This is the common deterministic denominator estimate for the first and fourth terms of
v3 formula (3.11). -/
theorem rpow_half_le_sqrt_mul_pow_four
    {n B v c : ℝ} (hn : 0 < n) (hv : 0 < v)
    (hscale : Real.rpow n c ≤ B * v ^ 8) :
    Real.rpow n (c / 2) ≤ Real.sqrt B * v ^ 4 := by
  have hB : 0 < B := bandwidth_pos_of_scale hn hv hscale
  have hsqrt_scale := Real.sqrt_le_sqrt hscale
  calc
    Real.rpow n (c / 2) = Real.sqrt (Real.rpow n c) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
      congr 1
      ring
    _ ≤ Real.sqrt (B * v ^ 8) := hsqrt_scale
    _ = Real.sqrt B * Real.sqrt (v ^ 8) := Real.sqrt_mul hB.le _
    _ = Real.sqrt B * v ^ 4 := by
      rw [show v ^ 8 = (v ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]

/-- The first, log-free term of v3 formula (3.11), as an explicit finite-`n` negative-power
bound.  Under `n^c ≤ B v⁸` and `c > 0`,
`C / (sqrt(B) v⁴) ≤ C n^(-c/2)`.

No probability input is used. -/
theorem formula311_first_term_le_rpow
    {n B v C c : ℝ} (hn : 0 < n) (hv : 0 < v) (hC : 0 ≤ C) (_hc : 0 < c)
    (hscale : Real.rpow n c ≤ B * v ^ 8) :
    C / (Real.sqrt B * v ^ 4) ≤ C * Real.rpow n (-(c / 2)) := by
  have hpow : 0 < Real.rpow n (c / 2) := Real.rpow_pos_of_pos hn _
  calc
    C / (Real.sqrt B * v ^ 4) ≤ C / Real.rpow n (c / 2) :=
      div_le_div_of_nonneg_left hC hpow
        (rpow_half_le_sqrt_mul_pow_four hn hv hscale)
    _ = C * Real.rpow n (-(c / 2)) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_neg hn.le]
      simp only [div_eq_mul_inv]

/-- Before using the bounded range `v ≤ 5`, the second term of v3 (3.11) satisfies the
sharper algebraic estimate `C/(Bv⁵) ≤ C v³ n^(-c)`. -/
theorem formula311_second_term_le_rpow_mul_v_cube
    {n B v C c : ℝ} (hn : 0 < n) (hv : 0 < v) (hC : 0 ≤ C)
    (hscale : Real.rpow n c ≤ B * v ^ 8) :
    C / (B * v ^ 5) ≤ C * v ^ 3 * Real.rpow n (-c) := by
  have hB : 0 < B := bandwidth_pos_of_scale hn hv hscale
  have hpow : 0 < Real.rpow n c := Real.rpow_pos_of_pos hn _
  calc
    C / (B * v ^ 5) = (C * v ^ 3) / (B * v ^ 8) := by
      field_simp [hB.ne', hv.ne']
    _ ≤ (C * v ^ 3) / Real.rpow n c :=
      div_le_div_of_nonneg_left (mul_nonneg hC (pow_nonneg hv.le 3)) hpow hscale
    _ = C * v ^ 3 * Real.rpow n (-c) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_neg hn.le]
      simp only [div_eq_mul_inv]

/-- The second term of v3 (3.11), uniformly on the paper's finite range `0 < v ≤ 5`:
`C/(Bv⁵) ≤ 125 C n^(-c)`.

This is a strict finite-`n` inequality, not asymptotic notation. -/
theorem formula311_second_term_le_125_mul_rpow
    {n B v C c : ℝ} (hn : 0 < n) (hv : 0 < v) (hv5 : v ≤ 5)
    (hC : 0 ≤ C) (_hc : 0 < c)
    (hscale : Real.rpow n c ≤ B * v ^ 8) :
    C / (B * v ^ 5) ≤ 125 * C * Real.rpow n (-c) := by
  have hv3 : v ^ 3 ≤ (125 : ℝ) := by
    calc
      v ^ 3 ≤ (5 : ℝ) ^ 3 := pow_le_pow_left₀ hv.le hv5 3
      _ = 125 := by norm_num
  have hrpow0 : 0 ≤ Real.rpow n (-c) :=
    (Real.rpow_pos_of_pos hn _).le
  calc
    C / (B * v ^ 5) ≤ C * v ^ 3 * Real.rpow n (-c) :=
      formula311_second_term_le_rpow_mul_v_cube hn hv hC hscale
    _ ≤ C * 125 * Real.rpow n (-c) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hv3 hC) hrpow0
    _ = 125 * C * Real.rpow n (-c) := by ring

/-- If the bandwidth obeys the elementary stochastic-profile bound `B ≤ n`, then the
square-root scale denominator also satisfies `n^(c/2) ≤ sqrt(n) v⁴`.  This is the
deterministic bridge needed for the third term of v3 formula (3.11). -/
theorem rpow_half_le_sqrt_n_mul_pow_four
    {n B v c : ℝ} (hn : 0 < n) (hv : 0 < v) (hBn : B ≤ n)
    (hscale : Real.rpow n c ≤ B * v ^ 8) :
    Real.rpow n (c / 2) ≤ Real.sqrt n * v ^ 4 := by
  calc
    Real.rpow n (c / 2) ≤ Real.sqrt B * v ^ 4 :=
      rpow_half_le_sqrt_mul_pow_four hn hv hscale
    _ ≤ Real.sqrt n * v ^ 4 :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hBn) (pow_nonneg hv.le 4)

/-- Before using `v ≤ 5`, the log-free algebraic factor in the third term of v3 (3.11)
satisfies `CD/(sqrt(n)v) ≤ CD v³ n^(-c/2)`. -/
theorem formula311_third_algebraic_factor_le_rpow_mul_v_cube
    {n B v CD c : ℝ} (hn : 0 < n) (hv : 0 < v) (hCD : 0 ≤ CD)
    (hBn : B ≤ n) (hscale : Real.rpow n c ≤ B * v ^ 8) :
    CD / (Real.sqrt n * v) ≤
      CD * v ^ 3 * Real.rpow n (-(c / 2)) := by
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hpow : 0 < Real.rpow n (c / 2) := Real.rpow_pos_of_pos hn _
  calc
    CD / (Real.sqrt n * v) =
        (CD * v ^ 3) / (Real.sqrt n * v ^ 4) := by
      field_simp [hsqrtn.ne', hv.ne']
    _ ≤ (CD * v ^ 3) / Real.rpow n (c / 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hCD (pow_nonneg hv.le 3)) hpow
        (rpow_half_le_sqrt_n_mul_pow_four hn hv hBn hscale)
    _ = CD * v ^ 3 * Real.rpow n (-(c / 2)) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_neg hn.le]
      simp only [div_eq_mul_inv]

/-- Uniform finite-range denominator bound for the third term of v3 (3.11): if
`0 < v ≤ 5`, then `CD/(sqrt(n)v) ≤ 125 CD n^(-c/2)`. -/
theorem formula311_third_algebraic_factor_le_125_mul_rpow
    {n B v CD c : ℝ} (hn : 0 < n) (hv : 0 < v) (hv5 : v ≤ 5)
    (hCD : 0 ≤ CD) (_hc : 0 < c) (hBn : B ≤ n)
    (hscale : Real.rpow n c ≤ B * v ^ 8) :
    CD / (Real.sqrt n * v) ≤
      125 * CD * Real.rpow n (-(c / 2)) := by
  have hv3 : v ^ 3 ≤ (125 : ℝ) := by
    calc
      v ^ 3 ≤ (5 : ℝ) ^ 3 := pow_le_pow_left₀ hv.le hv5 3
      _ = 125 := by norm_num
  have hrpow0 : 0 ≤ Real.rpow n (-(c / 2)) :=
    (Real.rpow_pos_of_pos hn _).le
  calc
    CD / (Real.sqrt n * v) ≤
        CD * v ^ 3 * Real.rpow n (-(c / 2)) :=
      formula311_third_algebraic_factor_le_rpow_mul_v_cube hn hv hCD hBn hscale
    _ ≤ CD * 125 * Real.rpow n (-(c / 2)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hv3 hCD) hrpow0
    _ = 125 * CD * Real.rpow n (-(c / 2)) := by ring

/-- After removing its `sqrt(log n)` multiplier, the fourth term of v3 (3.11) has the
sharper algebraic factor bound
`C/(sqrt(B)v²) ≤ C v² n^(-c/2)`. -/
theorem formula311_fourth_algebraic_factor_le_rpow_mul_v_sq
    {n B v C c : ℝ} (hn : 0 < n) (hv : 0 < v) (hC : 0 ≤ C)
    (hscale : Real.rpow n c ≤ B * v ^ 8) :
    C / (Real.sqrt B * v ^ 2) ≤
      C * v ^ 2 * Real.rpow n (-(c / 2)) := by
  have hB : 0 < B := bandwidth_pos_of_scale hn hv hscale
  have hsqrtB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hpow : 0 < Real.rpow n (c / 2) := Real.rpow_pos_of_pos hn _
  calc
    C / (Real.sqrt B * v ^ 2) =
        (C * v ^ 2) / (Real.sqrt B * v ^ 4) := by
      field_simp [hsqrtB.ne', hv.ne']
    _ ≤ (C * v ^ 2) / Real.rpow n (c / 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hC (pow_nonneg hv.le 2)) hpow
        (rpow_half_le_sqrt_mul_pow_four hn hv hscale)
    _ = C * v ^ 2 * Real.rpow n (-(c / 2)) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_neg hn.le]
      simp only [div_eq_mul_inv]

/-- Uniform finite-range version of the algebraic factor in the fourth term of v3 (3.11):
for `0 < v ≤ 5`, `C/(sqrt(B)v²) ≤ 25 C n^(-c/2)`. -/
theorem formula311_fourth_algebraic_factor_le_25_mul_rpow
    {n B v C c : ℝ} (hn : 0 < n) (hv : 0 < v) (hv5 : v ≤ 5)
    (hC : 0 ≤ C) (_hc : 0 < c)
    (hscale : Real.rpow n c ≤ B * v ^ 8) :
    C / (Real.sqrt B * v ^ 2) ≤
      25 * C * Real.rpow n (-(c / 2)) := by
  have hv2 : v ^ 2 ≤ (25 : ℝ) := by
    calc
      v ^ 2 ≤ (5 : ℝ) ^ 2 := pow_le_pow_left₀ hv.le hv5 2
      _ = 25 := by norm_num
  have hrpow0 : 0 ≤ Real.rpow n (-(c / 2)) :=
    (Real.rpow_pos_of_pos hn _).le
  calc
    C / (Real.sqrt B * v ^ 2) ≤
        C * v ^ 2 * Real.rpow n (-(c / 2)) :=
      formula311_fourth_algebraic_factor_le_rpow_mul_v_sq hn hv hC hscale
    _ ≤ C * 25 * Real.rpow n (-(c / 2)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hv2 hC) hrpow0
    _ = 25 * C * Real.rpow n (-(c / 2)) := by ring

/-- With the explicit logarithm-absorption hypothesis `sqrt(log n) ≤ n^δ`, the complete
third term of v3 (3.11) is at most `125 CD n^(δ-c/2)` on `0 < v ≤ 5`.

The separate condition `δ < c/2` makes the displayed exponent strictly negative; proving
that the logarithm hypothesis eventually holds is intentionally left outside this finite-`n`
arithmetic lemma. -/
theorem formula311_third_term_le_rpow_sub
    {n B v CD c delta : ℝ}
    (hn : 0 < n) (hv : 0 < v) (hv5 : v ≤ 5) (hCD : 0 ≤ CD)
    (hc : 0 < c) (_hdelta : delta < c / 2) (hBn : B ≤ n)
    (hscale : Real.rpow n c ≤ B * v ^ 8)
    (hlog : Real.sqrt (Real.log n) ≤ Real.rpow n delta) :
    CD * Real.sqrt (Real.log n) / (Real.sqrt n * v) ≤
      125 * CD * Real.rpow n (delta - c / 2) := by
  have hbase :
      (CD * Real.sqrt (Real.log n)) / (Real.sqrt n * v) ≤
        125 * (CD * Real.sqrt (Real.log n)) *
          Real.rpow n (-(c / 2)) :=
    formula311_third_algebraic_factor_le_125_mul_rpow
      hn hv hv5 (mul_nonneg hCD (Real.sqrt_nonneg (Real.log n))) hc hBn hscale
  have hrpow0 : 0 ≤ Real.rpow n (-(c / 2)) :=
    (Real.rpow_pos_of_pos hn _).le
  have habsorb :
      Real.rpow n delta * Real.rpow n (-(c / 2)) =
        Real.rpow n (delta - c / 2) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hn]
    congr 1
  calc
    CD * Real.sqrt (Real.log n) / (Real.sqrt n * v) ≤
        125 * (CD * Real.sqrt (Real.log n)) *
          Real.rpow n (-(c / 2)) := hbase
    _ ≤ 125 * (CD * Real.rpow n delta) *
          Real.rpow n (-(c / 2)) := by
      have hinner :
          (CD * Real.sqrt (Real.log n)) * Real.rpow n (-(c / 2)) ≤
            (CD * Real.rpow n delta) * Real.rpow n (-(c / 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog hCD) hrpow0
      calc
        125 * (CD * Real.sqrt (Real.log n)) * Real.rpow n (-(c / 2)) =
            125 * ((CD * Real.sqrt (Real.log n)) *
              Real.rpow n (-(c / 2))) := by ring
        _ ≤ 125 * ((CD * Real.rpow n delta) *
              Real.rpow n (-(c / 2))) :=
          mul_le_mul_of_nonneg_left hinner (by norm_num)
        _ = 125 * (CD * Real.rpow n delta) *
              Real.rpow n (-(c / 2)) := by ring
    _ = 125 * CD * Real.rpow n (delta - c / 2) := by
      calc
        125 * (CD * Real.rpow n delta) * Real.rpow n (-(c / 2)) =
            125 * CD *
              (Real.rpow n delta * Real.rpow n (-(c / 2))) := by ring
        _ = 125 * CD * Real.rpow n (delta - c / 2) := by rw [habsorb]

/-- Convenient `δ=c/4` specialization of `formula311_third_term_le_rpow_sub`:
the complete third term is bounded by `125 CD n^(-c/4)`. -/
theorem formula311_third_term_le_quarter_rpow
    {n B v CD c : ℝ}
    (hn : 0 < n) (hv : 0 < v) (hv5 : v ≤ 5) (hCD : 0 ≤ CD)
    (hc : 0 < c) (hBn : B ≤ n)
    (hscale : Real.rpow n c ≤ B * v ^ 8)
    (hlog : Real.sqrt (Real.log n) ≤ Real.rpow n (c / 4)) :
    CD * Real.sqrt (Real.log n) / (Real.sqrt n * v) ≤
      125 * CD * Real.rpow n (-(c / 4)) := by
  have h := formula311_third_term_le_rpow_sub hn hv hv5 hCD hc
    (show c / 4 < c / 2 by linarith) hBn hscale hlog
  have hexponent : c / 4 - c / 2 = -(c / 4) := by ring
  simpa only [hexponent] using h

/-- Under the same explicit logarithm-absorption hypothesis, the complete fourth term of
v3 (3.11) is at most `25 C n^(δ-c/2)` on `0 < v ≤ 5`. -/
theorem formula311_fourth_term_le_rpow_sub
    {n B v C c delta : ℝ}
    (hn : 0 < n) (hv : 0 < v) (hv5 : v ≤ 5) (hC : 0 ≤ C)
    (hc : 0 < c) (_hdelta : delta < c / 2)
    (hscale : Real.rpow n c ≤ B * v ^ 8)
    (hlog : Real.sqrt (Real.log n) ≤ Real.rpow n delta) :
    C * Real.sqrt (Real.log n) / (Real.sqrt B * v ^ 2) ≤
      25 * C * Real.rpow n (delta - c / 2) := by
  have hbase :
      (C * Real.sqrt (Real.log n)) / (Real.sqrt B * v ^ 2) ≤
        25 * (C * Real.sqrt (Real.log n)) *
          Real.rpow n (-(c / 2)) :=
    formula311_fourth_algebraic_factor_le_25_mul_rpow
      hn hv hv5 (mul_nonneg hC (Real.sqrt_nonneg (Real.log n))) hc hscale
  have hrpow0 : 0 ≤ Real.rpow n (-(c / 2)) :=
    (Real.rpow_pos_of_pos hn _).le
  have habsorb :
      Real.rpow n delta * Real.rpow n (-(c / 2)) =
        Real.rpow n (delta - c / 2) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hn]
    congr 1
  calc
    C * Real.sqrt (Real.log n) / (Real.sqrt B * v ^ 2) ≤
        25 * (C * Real.sqrt (Real.log n)) *
          Real.rpow n (-(c / 2)) := hbase
    _ ≤ 25 * (C * Real.rpow n delta) *
          Real.rpow n (-(c / 2)) := by
      have hinner :
          (C * Real.sqrt (Real.log n)) * Real.rpow n (-(c / 2)) ≤
            (C * Real.rpow n delta) * Real.rpow n (-(c / 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog hC) hrpow0
      calc
        25 * (C * Real.sqrt (Real.log n)) * Real.rpow n (-(c / 2)) =
            25 * ((C * Real.sqrt (Real.log n)) *
              Real.rpow n (-(c / 2))) := by ring
        _ ≤ 25 * ((C * Real.rpow n delta) *
              Real.rpow n (-(c / 2))) :=
          mul_le_mul_of_nonneg_left hinner (by norm_num)
        _ = 25 * (C * Real.rpow n delta) *
              Real.rpow n (-(c / 2)) := by ring
    _ = 25 * C * Real.rpow n (delta - c / 2) := by
      calc
        25 * (C * Real.rpow n delta) * Real.rpow n (-(c / 2)) =
            25 * C *
              (Real.rpow n delta * Real.rpow n (-(c / 2))) := by ring
        _ = 25 * C * Real.rpow n (delta - c / 2) := by rw [habsorb]

/-- Convenient `δ=c/4` specialization for the complete fourth term of v3 (3.11):
it is bounded by `25 C n^(-c/4)`. -/
theorem formula311_fourth_term_le_quarter_rpow
    {n B v C c : ℝ}
    (hn : 0 < n) (hv : 0 < v) (hv5 : v ≤ 5) (hC : 0 ≤ C)
    (hc : 0 < c) (hscale : Real.rpow n c ≤ B * v ^ 8)
    (hlog : Real.sqrt (Real.log n) ≤ Real.rpow n (c / 4)) :
    C * Real.sqrt (Real.log n) / (Real.sqrt B * v ^ 2) ≤
      25 * C * Real.rpow n (-(c / 4)) := by
  have h := formula311_fourth_term_le_rpow_sub hn hv hv5 hC hc
    (show c / 4 < c / 2 by linarith) hscale hlog
  have hexponent : c / 4 - c / 2 = -(c / 4) := by ring
  simpa only [hexponent] using h

/-- The logarithmic factor suppressed in the passage from v3 (3.11) to (3.9) is smaller
than every positive real power: for every `δ > 0`, eventually
`sqrt(log n) ≤ n^δ` as a statement on the real `atTop` filter.

This is proved from mathlib's `isLittleO_log_rpow_rpow_atTop`; it is not an analytic input
interface. -/
theorem eventually_sqrt_log_le_rpow {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℝ in Filter.atTop,
      Real.sqrt (Real.log n) ≤ Real.rpow n delta := by
  have hasymptotic :=
    (isLittleO_log_rpow_rpow_atTop (1 / 2 : ℝ) hdelta).eventuallyLE
  filter_upwards [hasymptotic, Filter.eventually_ge_atTop (1 : ℝ)] with n hn hn1
  have hn0 : 0 ≤ n := zero_le_one.trans hn1
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog0 _),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn0 _)] at hn
  simpa only [Real.sqrt_eq_rpow, Real.rpow_eq_pow] using hn

/-- Natural-number version of `eventually_sqrt_log_le_rpow`, matching the matrix dimension
`n` in v3 Proposition 3.4. -/
theorem eventually_sqrt_log_natCast_le_rpow {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt (Real.log (n : ℝ)) ≤ Real.rpow (n : ℝ) delta := by
  exact tendsto_natCast_atTop_atTop.eventually
    (eventually_sqrt_log_le_rpow hdelta)

/-- A fixed nonnegative coefficient can be absorbed into a strictly smaller negative
power.  This is the coefficient bookkeeping used four times after v3 formula (3.11):
if `0 < b < a`, then eventually `K n⁻ᵃ ≤ n⁻ᵇ / 4`.

The factor `1/4` is chosen so that the four terms add to one copy of the target power. -/
theorem eventually_const_mul_rpow_neg_le_quarter
    {K a b : ℝ} (_hK : 0 ≤ K) (_hb : 0 < b) (hba : b < a) :
    ∀ᶠ n : ℝ in Filter.atTop,
      K * Real.rpow n (-a) ≤ Real.rpow n (-b) / 4 := by
  have hpower :
      ∀ᶠ n : ℝ in Filter.atTop, 4 * K ≤ Real.rpow n (a - b) :=
    (tendsto_rpow_atTop (sub_pos.mpr hba)).eventually
      (Filter.eventually_ge_atTop (4 * K))
  filter_upwards [hpower, Filter.eventually_gt_atTop (0 : ℝ)] with n hnPower hn
  have hcoeff : K ≤ Real.rpow n (a - b) / 4 := by linarith
  have hneg : 0 ≤ Real.rpow n (-a) := (Real.rpow_pos_of_pos hn _).le
  have hfactor :
      Real.rpow n (-b) = Real.rpow n (a - b) * Real.rpow n (-a) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hn]
    congr 1
    ring
  calc
    K * Real.rpow n (-a) ≤
        (Real.rpow n (a - b) / 4) * Real.rpow n (-a) :=
      mul_le_mul_of_nonneg_right hcoeff hneg
    _ = Real.rpow n (-b) / 4 := by rw [hfactor]; ring

/-- Natural-number version of fixed-coefficient absorption. -/
theorem eventually_const_mul_rpow_natCast_neg_le_quarter
    {K a b : ℝ} (hK : 0 ≤ K) (hb : 0 < b) (hba : b < a) :
    ∀ᶠ n : ℕ in Filter.atTop,
      K * Real.rpow (n : ℝ) (-a) ≤ Real.rpow (n : ℝ) (-b) / 4 := by
  exact tendsto_natCast_atTop_atTop.eventually
    (eventually_const_mul_rpow_neg_le_quarter hK hb hba)

/-- Four quarter-sized estimates give the desired polynomial error. -/
theorem formula311Error_le_of_termwise
    {n B v C CD target : ℝ}
    (h1 : C / (Real.sqrt B * v ^ 4) ≤ target / 4)
    (h2 : C / (B * v ^ 5) ≤ target / 4)
    (h3 : CD * Real.sqrt (Real.log n) / (Real.sqrt n * v) ≤ target / 4)
    (h4 : C * Real.sqrt (Real.log n) / (Real.sqrt B * v ^ 2) ≤ target / 4) :
    formula311Error n B v C CD ≤ target := by
  unfold formula311Error
  linarith

/-- A checked constructor for the rate certificate used in v3 formula (3.9). -/
def polynomialRateCertificate_of_termwise
    {n B v C CD exponent : ℝ}
    (hexponent : 0 < exponent)
    (h1 : C / (Real.sqrt B * v ^ 4) ≤ Real.rpow n (-exponent) / 4)
    (h2 : C / (B * v ^ 5) ≤ Real.rpow n (-exponent) / 4)
    (h3 : CD * Real.sqrt (Real.log n) / (Real.sqrt n * v) ≤
      Real.rpow n (-exponent) / 4)
    (h4 : C * Real.sqrt (Real.log n) / (Real.sqrt B * v ^ 2) ≤
      Real.rpow n (-exponent) / 4) :
    PolynomialRateCertificate n (formula311Error n B v C CD) where
  exponent := exponent
  exponent_pos := hexponent
  error_le := formula311Error_le_of_termwise h1 h2 h3 h4

/-- Fully checked asymptotic closure of v3 `(3.11) => (3.9)` on real dimensions.

For fixed nonnegative constants `C, CD` and `c > 0`, all sufficiently large `n` have the
following uniform property: every `B,v` satisfying exactly the deterministic hypotheses
used in the paper,

* `0 < v ≤ 5`,
* `B ≤ n`, and
* `n^c ≤ B v⁸`,

admits a concrete `PolynomialRateCertificate` with exponent `c/8`.  Thus no additional
probability or free-probability input is hidden in the passage from (3.11) to (3.9). -/
theorem eventually_formula311_polynomialRateCertificate
    {C CD c : ℝ} (hC : 0 ≤ C) (hCD : 0 ≤ CD) (hc : 0 < c) :
    ∀ᶠ n : ℝ in Filter.atTop, ∀ B v : ℝ,
      0 < v → v ≤ 5 → B ≤ n → Real.rpow n c ≤ B * v ^ 8 →
        Nonempty (PolynomialRateCertificate n (formula311Error n B v C CD)) := by
  have hlog := eventually_sqrt_log_le_rpow (show 0 < c / 4 by linarith)
  have hfirst := eventually_const_mul_rpow_neg_le_quarter
    hC (show 0 < c / 8 by linarith) (show c / 8 < c / 2 by linarith)
  have hsecond := eventually_const_mul_rpow_neg_le_quarter
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 125) hC)
    (show 0 < c / 8 by linarith) (show c / 8 < c by linarith)
  have hthird := eventually_const_mul_rpow_neg_le_quarter
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 125) hCD)
    (show 0 < c / 8 by linarith) (show c / 8 < c / 4 by linarith)
  have hfourth := eventually_const_mul_rpow_neg_le_quarter
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 25) hC)
    (show 0 < c / 8 by linarith) (show c / 8 < c / 4 by linarith)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), hlog, hfirst,
      hsecond, hthird, hfourth] with n hn hnlog hnfirst hnsecond hnthird hnfourth
  intro B v hv hv5 hBn hscale
  refine ⟨polynomialRateCertificate_of_termwise
    (exponent := c / 8) (show 0 < c / 8 by linarith) ?_ ?_ ?_ ?_⟩
  · exact (formula311_first_term_le_rpow hn hv hC hc hscale).trans hnfirst
  · exact (formula311_second_term_le_125_mul_rpow
      hn hv hv5 hC hc hscale).trans hnsecond
  · exact (formula311_third_term_le_quarter_rpow
      hn hv hv5 hCD hc hBn hscale hnlog).trans hnthird
  · exact (formula311_fourth_term_le_quarter_rpow
      hn hv hv5 hC hc hscale hnlog).trans hnfourth

/-- Natural-dimension version of the complete `(3.11) => (3.9)` rate construction, matching
the type of the matrix dimension in the formalized v3 random-matrix model. -/
theorem eventually_formula311_polynomialRateCertificate_nat
    {C CD c : ℝ} (hC : 0 ≤ C) (hCD : 0 ≤ CD) (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ B v : ℝ,
      0 < v → v ≤ 5 → B ≤ (n : ℝ) →
        Real.rpow (n : ℝ) c ≤ B * v ^ 8 →
          Nonempty (PolynomialRateCertificate (n : ℝ)
            (formula311Error (n : ℝ) B v C CD)) := by
  exact tendsto_natCast_atTop_atTop.eventually
    (eventually_formula311_polynomialRateCertificate hC hCD hc)

/-- Explicit “sufficiently large `n`” form of the preceding result.  This exposes an actual
natural threshold (depending only on `C`, `CD`, and `c`) rather than leaving the conclusion
in filter notation.  It is the rate certificate required by v3 formula (3.9). -/
theorem exists_threshold_formula311_polynomialRateCertificate_nat
    {C CD c : ℝ} (hC : 0 ≤ C) (hCD : 0 ≤ CD) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ B v : ℝ,
      0 < v → v ≤ 5 → B ≤ (n : ℝ) →
        Real.rpow (n : ℝ) c ≤ B * v ^ 8 →
          Nonempty (PolynomialRateCertificate (n : ℝ)
            (formula311Error (n : ℝ) B v C CD)) := by
  exact Filter.eventually_atTop.1
    (eventually_formula311_polynomialRateCertificate_nat hC hCD hc)

end Arxiv2410V3

