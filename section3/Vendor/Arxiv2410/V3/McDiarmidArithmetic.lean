/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/McDiarmidArithmetic.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.ComplexMcDiarmid

/-!
# Explicit arithmetic for the v3 McDiarmid threshold

This file discharges the elementary exponent comparison left explicit in
`probabilityAtLeast_complexConcentrationGood_of_boundedDoobDifferences_v3`.

With `n` row coordinates and coordinate sensitivity at most `2 / (n v)`, the sum of the
Hoeffding proxies is at most `1 / (n v²)`.  Because the complex concentration proof uses four
real one-sided tails at threshold `bound / 2`, the simple choice `C_D = 16` makes the four-tail
bound at most `n⁻¹⁰` for every `n ≥ 2`.
-/

namespace Arxiv2410V3

open Real
open scoped BigOperators NNReal

/-- The proxy-sum estimate corresponding to the row sensitivity
`cᵢ ≤ 2 / (n v)` in v3 Proposition 3.4, proof step (3). -/
theorem mcdiarmid_proxy_sum_le_of_row_sensitivity
    {n : ℕ} {v : ℝ} (hn : 0 < n) (hv : 0 < v) {c : ℕ → ℝ≥0}
    (hc : ∀ i < n, (c i : ℝ) ≤ 2 / ((n : ℝ) * v)) :
    (((∑ i ∈ Finset.range n, (c i / 2) ^ 2 : ℝ≥0)) : ℝ) ≤
      1 / ((n : ℝ) * v ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) * v := mul_pos hnR hv
  calc
    (((∑ i ∈ Finset.range n, (c i / 2) ^ 2 : ℝ≥0)) : ℝ) =
        ∑ i ∈ Finset.range n, (((c i : ℝ) / 2) ^ 2) := by
          simp
    _ ≤ ∑ _i ∈ Finset.range n, (1 / ((n : ℝ) * v)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hic : i < n := Finset.mem_range.mp hi
      have hcdiv : (c i : ℝ) / 2 ≤ 1 / ((n : ℝ) * v) := by
        calc
          (c i : ℝ) / 2 ≤ (2 / ((n : ℝ) * v)) / 2 := by
            exact div_le_div_of_nonneg_right (hc i hic) (by norm_num)
          _ = 1 / ((n : ℝ) * v) := by ring
      exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (c i : ℝ) / 2) hcdiv 2
    _ = (n : ℝ) * (1 / ((n : ℝ) * v)) ^ 2 := by simp
    _ = 1 / ((n : ℝ) * v ^ 2) := by
      field_simp [hnR.ne', hv.ne']

/-- A positive coordinate bound makes the proxy sum strictly positive.  This is needed because
Lean's totalized real division assigns `x / 0 = 0`; the displayed exponential formula itself
cannot yield a small tail when its denominator is literally zero. -/
theorem mcdiarmid_proxy_sum_pos_of_one_pos
    {n : ℕ} {c : ℕ → ℝ≥0}
    (hpos : ∃ i < n, 0 < c i) :
    0 < (((∑ i ∈ Finset.range n, (c i / 2) ^ 2 : ℝ≥0)) : ℝ) := by
  obtain ⟨i, hi, hci⟩ := hpos
  have hmem : i ∈ Finset.range n := Finset.mem_range.mpr hi
  have hterm : 0 < (c i / 2) ^ 2 := by positivity
  have hterm_le : (c i / 2) ^ 2 ≤ ∑ j ∈ Finset.range n, (c j / 2) ^ 2 :=
    Finset.single_le_sum (f := fun j ↦ (c j / 2) ^ 2) (fun _ _ ↦ bot_le) hmem
  exact_mod_cast hterm.trans_le hterm_le

/-- Explicit v3 four-tail arithmetic with `C_D = 16`.

The extra positivity premise is only an artefact of the totalized denominator in the displayed
McDiarmid bound; it follows, for example, from `mcdiarmid_proxy_sum_pos_of_one_pos` when one row
sensitivity is positive. -/
theorem four_exp_mcdiarmid_threshold_sixteen_le
    {n : ℕ} (hn : 2 ≤ n) {v : ℝ} (hv : 0 < v) {c : ℕ → ℝ≥0}
    (hc : ∀ i < n, (c i : ℝ) ≤ 2 / ((n : ℝ) * v))
    (hproxypos :
      0 < (((∑ i ∈ Finset.range n, (c i / 2) ^ 2 : ℝ≥0)) : ℝ)) :
    4 * exp
      (-((16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)) / 2) ^ 2 /
        (2 * (((∑ i ∈ Finset.range n, (c i / 2) ^ 2 : ℝ≥0)) : ℝ))) ≤
      (n : ℝ) ^ (-10 : ℤ) := by
  have hnNat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnNat.ne')
  have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ log (n : ℝ) := log_nonneg hnOne
  have hsqrtn : 0 < sqrt (n : ℝ) := sqrt_pos.2 hnR
  have hnv2 : 0 < (n : ℝ) * v ^ 2 := mul_pos hnR (sq_pos_of_pos hv)
  have hproxyLe :
      (((∑ i ∈ Finset.range n, (c i / 2) ^ 2 : ℝ≥0)) : ℝ) ≤
        1 / ((n : ℝ) * v ^ 2) :=
    mcdiarmid_proxy_sum_le_of_row_sensitivity hnNat hv hc
  let S : ℝ := (((∑ i ∈ Finset.range n, (c i / 2) ^ 2 : ℝ≥0)) : ℝ)
  have hSpos : 0 < S := hproxypos
  have hSle : S ≤ 1 / ((n : ℝ) * v ^ 2) := hproxyLe
  have hnumerator :
      ((16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)) / 2) ^ 2 =
        64 * log (n : ℝ) / ((n : ℝ) * v ^ 2) := by
    field_simp [hsqrtn.ne', hv.ne', hnR.ne']
    nlinarith [sq_sqrt hlog, sq_sqrt hnR.le]
  have hnum_nonneg : 0 ≤ 64 * log (n : ℝ) / ((n : ℝ) * v ^ 2) := by positivity
  have hquotient :
      32 * log (n : ℝ) ≤
        ((16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)) / 2) ^ 2 /
          (2 * S) := by
    rw [hnumerator]
    calc
      32 * log (n : ℝ) =
          (64 * log (n : ℝ) / ((n : ℝ) * v ^ 2)) /
            (2 / ((n : ℝ) * v ^ 2)) := by
        field_simp [hnv2.ne']
        ring
      _ ≤ (64 * log (n : ℝ) / ((n : ℝ) * v ^ 2)) / (2 * S) := by
        apply div_le_div_of_nonneg_left hnum_nonneg (by positivity)
        calc
          2 * S ≤ 2 * (1 / ((n : ℝ) * v ^ 2)) :=
            mul_le_mul_of_nonneg_left hSle (by norm_num)
          _ = 2 / ((n : ℝ) * v ^ 2) := by ring
  have hexp :
      exp
          (-((16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)) / 2) ^ 2 /
            (2 * S)) ≤
        exp (-(32 * log (n : ℝ))) := by
    exact exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hquotient)
  have hexpPower : exp (-(32 * log (n : ℝ))) = (n : ℝ) ^ (-32 : ℤ) := by
    rw [show -(32 * log (n : ℝ)) = log ((n : ℝ) ^ (-32 : ℤ)) by
      rw [log_zpow]
      norm_num]
    exact exp_log (zpow_pos hnR _)
  have hfourPower : 4 * ((n : ℝ) ^ (-32 : ℤ)) ≤ (n : ℝ) ^ (-10 : ℤ) := by
    rw [show (-32 : ℤ) = -(32 : ℤ) by norm_num,
      show (-10 : ℤ) = -(10 : ℤ) by norm_num,
      zpow_neg, zpow_neg]
    have hdiv : 4 / (n : ℝ) ^ 32 ≤ 1 / (n : ℝ) ^ 10 := by
      rw [div_le_div_iff₀ (pow_pos hnR 32) (pow_pos hnR 10)]
      have hfour : (4 : ℝ) ≤ (n : ℝ) ^ 22 := by
        exact (by norm_num : (4 : ℝ) ≤ 2 ^ 22).trans
          (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnTwo 22)
      calc
        4 * (n : ℝ) ^ 10 ≤ (n : ℝ) ^ 22 * (n : ℝ) ^ 10 :=
          mul_le_mul_of_nonneg_right hfour (pow_nonneg hnR.le 10)
        _ = 1 * (n : ℝ) ^ 32 := by
          rw [one_mul, ← pow_add]
    calc
      4 * ((n : ℝ) ^ 32)⁻¹ = 4 / (n : ℝ) ^ 32 := by
        rw [div_eq_mul_inv]
      _ ≤ 1 / (n : ℝ) ^ 10 := hdiv
      _ = ((n : ℝ) ^ 10)⁻¹ := by rw [one_div]
  change 4 * exp
      (-((16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)) / 2) ^ 2 /
        (2 * S)) ≤ (n : ℝ) ^ (-10 : ℤ)
  calc
    4 * exp
        (-((16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)) / 2) ^ 2 /
          (2 * S)) ≤ 4 * exp (-(32 * log (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = 4 * ((n : ℝ) ^ (-32 : ℤ)) := by rw [hexpPower]
    _ ≤ (n : ℝ) ^ (-10 : ℤ) := hfourPower

/-- Convenient form of `four_exp_mcdiarmid_threshold_sixteen_le` in which positivity of the
proxy sum is discharged by exhibiting one positive row sensitivity. -/
theorem four_exp_mcdiarmid_threshold_sixteen_le_of_one_pos
    {n : ℕ} (hn : 2 ≤ n) {v : ℝ} (hv : 0 < v) {c : ℕ → ℝ≥0}
    (hc : ∀ i < n, (c i : ℝ) ≤ 2 / ((n : ℝ) * v))
    (hpos : ∃ i < n, 0 < c i) :
    4 * exp
      (-((16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)) / 2) ^ 2 /
        (2 * (((∑ i ∈ Finset.range n, (c i / 2) ^ 2 : ℝ≥0)) : ℝ))) ≤
      (n : ℝ) ^ (-10 : ℤ) :=
  four_exp_mcdiarmid_threshold_sixteen_le hn hv hc
    (mcdiarmid_proxy_sum_pos_of_one_pos hpos)

end Arxiv2410V3

