import Vendor.Arxiv2410.V3.RateArithmeticAllEta

/-!
# Lemma 3.5: expose a common polynomial exponent before taking a growing net

The old fixed-eta endpoint existentially packages its exponent.  That endpoint
alone does not imply a common exponent over a dimension-dependent grid.
Here the already proved v3 (3.11) arithmetic is reassembled with the explicit
exponent `c/32`, uniformly for all admissible `B,v`.  In particular there is
no radius-five assumption and no new random-matrix comparison hypothesis.
-/

open Filter
open scoped Topology

namespace ShortRingAnchor
open Arxiv2410V3

/-- Lemma 3.5, quantitative use of v3 (3.11): one exponent works for every
positive imaginary part obeying the scale condition. -/
theorem eventually_formula311Error_le_explicit_allEta
    {C CD c : ℝ} (hC : 0 ≤ C) (hCD : 0 ≤ CD) (hc : 0 < c) :
    ∀ᶠ n : ℝ in atTop, ∀ B v : ℝ,
      1 ≤ B → B ≤ n → 0 < v → n ^ c ≤ B * v ^ 8 →
        formula311Error n B v C CD ≤ n ^ (-(c / 32)) := by
  have hlogThird := eventually_sqrt_log_le_rpow (show 0 < c / 16 by linarith)
  have hlogFourth := eventually_sqrt_log_le_rpow (show 0 < c / 8 by linarith)
  have hfirst := eventually_const_mul_rpow_neg_le_quarter
    hC (show 0 < c / 32 by linarith) (show c / 32 < c / 2 by linarith)
  have hthird := eventually_const_mul_rpow_neg_le_quarter
    hCD (show 0 < c / 32 by linarith) (show c / 32 < c / 16 by linarith)
  have hfourth := eventually_const_mul_rpow_neg_le_quarter
    hC (show 0 < c / 32 by linarith) (show c / 32 < c / 8 by linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlogThird, hlogFourth,
    hfirst, hthird, hfourth] with n hn hnlogThird hnlogFourth hnfirst hnthird hnfourth
  intro B v hB hBn hv hscale
  exact formula311Error_le_of_termwise
    ((formula311_first_term_le_rpow (zero_lt_one.trans_le hn) hv hC hc hscale).trans hnfirst)
    ((formula311_second_term_le_rpow_allEta hn hB hv hC hc hscale).trans hnfirst)
    ((formula311_third_term_le_sixteenth_rpow_allEta
      hn hv hCD hBn hscale hnlogThird).trans hnthird)
    ((formula311_fourth_term_le_eighth_rpow_allEta
      hn hB hv hC hscale hnlogFourth).trans hnfourth)

/-- Lemma 3.5, the common-rate statement on natural matrix dimensions. -/
theorem eventually_formula311Error_le_explicit_nat_allEta
    {C CD c : ℝ} (hC : 0 ≤ C) (hCD : 0 ≤ CD) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ B v : ℝ,
      1 ≤ B → B ≤ (n : ℝ) → 0 < v → (n : ℝ) ^ c ≤ B * v ^ 8 →
        formula311Error (n : ℝ) B v C CD ≤ (n : ℝ) ^ (-(c / 32)) :=
  tendsto_natCast_atTop_atTop.eventually
    (eventually_formula311Error_le_explicit_allEta hC hCD hc)

end ShortRingAnchor
