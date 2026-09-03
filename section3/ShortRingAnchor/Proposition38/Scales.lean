import ShortRingAnchor.SourceScales

/-!
# Proposition 3.8: reusing the verified hard-edge scales

Equations (3.20)--(3.23). We choose slightly stronger strict exponent
inequalities than the source needs, so that the logarithmic JJLO loss can
be absorbed into the already verified `sourceHardEdgeScale`. This costs no
bandwidth range: `exists_hardEdgeAdmissible_of_omega` applies to every
positive omega. These are deterministic theorems, not external interfaces.
-/

open Filter
open scoped Topology
noncomputable section
namespace ShortRingAnchor.Proposition38

/-- Proposition 3.8, immediately after (3.20): the high-band condition
implies `m ≤ W`, the size hypothesis needed in Proposition 3.2. -/
theorem block_count_le_width {N m W : ℕ} {beta : ℝ}
    (hN : 1 ≤ N) (hW : 0 < W) (hdim : N = m * W)
    (hbeta : (1 / 2 : ℝ) < beta) (hband : (N : ℝ) ^ beta ≤ W) : m ≤ W := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hw : (0 : ℝ) < W := by exact_mod_cast hW
  have hsq := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg N) beta) hband 2
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)] at hsq
  have hpower : (N : ℝ) ≤ (N : ℝ) ^ (beta * (2 : ℕ)) := by
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (by norm_num; linarith)
  have hdimR : (N : ℝ) = (m : ℝ) * (W : ℝ) := by exact_mod_cast hdim
  have hmw : (m : ℝ) ≤ W := by nlinarith [hpower.trans hsq]
  exact_mod_cast hmw

/-- Equation (3.20): the existing constructive parameter choice also
satisfies both strict inequalities of Proposition 3.8. -/
theorem source_parameter_inequalities {beta chi kappa tau : ℝ}
    (h : HardEdgeAdmissible beta chi kappa tau) :
    0 < tau ∧ tau < beta / 8 ∧ tau < 9 * beta / 8 - 1 := by
  rcases h with ⟨_, hk, ht, _, _, htb, hgap⟩
  exact ⟨ht, htb, by linarith⟩

/-- Equations (3.20), (3.23): any v3 bandwidth `B ≥ N^beta`
supplies the cutoff comparison needed for the internal counting theorem.
The cap by one is eventually inactive. -/
theorem counting_cutoff_le_eventually
    {N : ℕ → ℕ} {B : ℕ → ℝ} {beta chi kappa tau : ℝ}
    (hparam : HardEdgeAdmissible beta chi kappa tau)
    (hN : Tendsto N atTop atTop)
    (hband : ∀ᶠ k in atTop, (N k : ℝ) ^ beta ≤ B k) :
    ∀ᶠ k in atTop, B k ^ (-(1 / 8 : ℝ)) * (N k : ℝ) ^ tau ≤
      sourceCutoff N 1 beta tau k := by
  filter_upwards [hN.eventually_ge_atTop 1, hband,
    sourceCutoff_eventually_eq_raw (K := 1) hparam hN] with k hk hb hc
  have hn : (0 : ℝ) < N k := by exact_mod_cast (show 0 < N k by omega)
  rw [hc]
  have hpow := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hn beta) hb (by norm_num : -(1 / 8 : ℝ) ≤ 0)
  calc
    B k ^ (-(1 / 8 : ℝ)) * (N k : ℝ) ^ tau ≤
        ((N k : ℝ) ^ beta) ^ (-(1 / 8 : ℝ)) * (N k : ℝ) ^ tau :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hn.le _)
    _ = sourceRawCutoff N 1 beta tau k := by
      rw [← Real.rpow_mul hn.le, ← Real.rpow_add hn]
      simp only [sourceRawCutoff, one_mul, sourceCutoffExponent]
      congr 1
      ring

/-- Equations (3.21)--(3.22): a positive polynomial absorbs the logarithmic
JJLO exponent uniformly for `1 ≤ W ≤ N`. -/
theorem eventually_log_three_width_le_power
    {N W : ℕ → ℕ} {d : ℝ} (hd : 0 < d)
    (hN : Tendsto N atTop atTop) (hWN : ∀ k, W k ≤ N k) :
    ∀ᶠ k in atTop, 0 < W k →
      25 * Real.log (3 * (W k : ℝ)) ≤ (N k : ℝ) ^ d := by
  have hreal := tendsto_natCast_comp_atTop hN
  have hp := (tendsto_rpow_atTop_zero_of_neg (neg_neg_of_pos hd)).comp hreal
  have hl := (tendsto_rpow_mul_log_atTop_zero_of_neg (neg_neg_of_pos hd)).comp hreal
  have hzero : Tendsto (fun k => 25 *
      ((N k : ℝ) ^ (-d) * Real.log 3 +
        (N k : ℝ) ^ (-d) * Real.log (N k : ℝ))) atTop (nhds 0) := by
    simpa using ((hp.mul_const (Real.log 3)).add hl).const_mul 25
  filter_upwards [hN.eventually_ge_atTop 1,
    hzero.eventually_le_const zero_lt_one] with k hk he hW
  have hn : (0 : ℝ) < N k := by exact_mod_cast (show 0 < N k by omega)
  have hw : (0 : ℝ) < W k := by exact_mod_cast hW
  have hlog : Real.log (3 * (W k : ℝ)) ≤ Real.log 3 + Real.log (N k : ℝ) := by
    rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hn.ne']
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hWN k) (by norm_num)
  have hpow : 0 < (N k : ℝ) ^ d := Real.rpow_pos_of_pos hn _
  simp only [Real.rpow_neg hn.le] at he
  have hquot : (25 * (Real.log 3 + Real.log (N k : ℝ))) /
      (N k : ℝ) ^ d ≤ 1 := by
    calc
      _ = 25 * ((N k : ℝ) ^ d)⁻¹ *
          (Real.log 3 + Real.log (N k : ℝ)) := by ring
      _ ≤ 1 := by nlinarith [he]
  have hb := (div_le_one hpow).mp hquot
  linarith

/-- Equations (3.21)--(3.22): the repaired Proposition 3.2 floor is
eventually stronger than the reusable exponential floor. No assertion
about the probability of either event is made here. -/
theorem jjlo_exponent_le_sourceHardEdgeScale
    {N W m : ℕ → ℕ} {kappa : ℝ} (hkappa : 0 < kappa)
    (hN : Tendsto N atTop atTop) (hW : ∀ k, 0 < W k)
    (hWN : ∀ k, W k ≤ N k) (hdim : ∀ k, N k = m k * W k) :
    ∀ᶠ k in atTop, 25 * (m k : ℝ) * Real.log (3 * (W k : ℝ)) ≤
      sourceHardEdgeScale N W kappa k := by
  filter_upwards [eventually_log_three_width_le_power (by positivity : 0 < 3 * kappa)
      hN hWN, hN.eventually_ge_atTop 1] with k hk hn
  have hw : (0 : ℝ) < W k := by exact_mod_cast hW k
  have hn0 : (0 : ℝ) < N k := by exact_mod_cast (show 0 < N k by omega)
  have hnr : (1 : ℝ) ≤ N k := by exact_mod_cast hn
  have hm : (m k : ℝ) = (N k : ℝ) / (W k : ℝ) := by
    apply (eq_div_iff hw.ne').mpr
    exact_mod_cast (hdim k).symm
  have hbound := mul_le_mul_of_nonneg_left (hk (hW k))
    (Nat.cast_nonneg (m k) : (0 : ℝ) ≤ m k)
  have heq : (m k : ℝ) * (N k : ℝ) ^ (3 * kappa) =
      (N k : ℝ) ^ (1 + 3 * kappa) / (W k : ℝ) := by
    rw [hm, Real.rpow_add hn0, Real.rpow_one]
    ring
  rw [heq] at hbound
  have hlog := Real.log_nonneg hnr
  dsimp [sourceHardEdgeScale]
  nlinarith

/-- Equations (3.21)--(3.22): translate the polynomial JJLO floor into the
exponential floor used by the verified logarithmic truncation argument. -/
theorem exponential_floor_le_jjlo_floor {W m : ℕ} {L : ℝ}
    (hW : 0 < W) (hL : 25 * (m : ℝ) * Real.log (3 * (W : ℝ)) ≤ L) :
    Real.exp (-L) ≤ (3 * (W : ℝ)) ^ (-(25 * (m : ℝ))) := by
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 3 * W)]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Proposition 3.8, (3.22): the reusable exponential floor is below
`N^(-2)`, so the bounded-block Cook floor suffices on the same scale. -/
theorem exponential_floor_le_polynomial
    (N W : ℕ → ℕ) (kappa : ℝ) (k : ℕ) (hN : 0 < N k) :
    Real.exp (-(sourceHardEdgeScale N W kappa k)) ≤ (N k : ℝ) ^ (-(2 : ℝ)) := by
  have hn : (0 : ℝ) < N k := by exact_mod_cast hN
  rw [Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.mpr
  have hp : 0 ≤ (N k : ℝ) ^ (1 + 3 * kappa) / (W k : ℝ) := by positivity
  dsimp [sourceHardEdgeScale]
  nlinarith

end ShortRingAnchor.Proposition38
