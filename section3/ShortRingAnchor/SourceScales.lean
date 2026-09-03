import ShortRingAnchor.ParameterArithmetic

/-!
# Deterministic scales in Proposition 3.6

This file closes the deterministic cutoff bookkeeping in formulas
(3.9)--(3.12) of Proposition 3.6.  It uses no probability or random-matrix
input.

For the bandwidth exponent `beta`, put

`d = tau - beta / 8 < 0`.

The source cutoff `b^(-1/8) M^tau` is, after the deterministic bandwidth
comparison, bounded by a constant multiple of `M^d`.  We therefore use the
slightly larger and everywhere bounded cutoff

`a_M = min 1 (K M^d)`.

The hard-edge scale paired with it is

`L_M = M^(1+3*kappa) / W + 2 log M`.

The last two inequalities in (3.9) imply `C a_M L_M -> 0`.  Finally, every
positive polynomial CDF-comparison rate absorbs the logarithmic size of this
cutoff, exactly as required in (3.12).
-/

open Filter

noncomputable section

namespace ShortRingAnchor

/-- The power in the deterministic cutoff used below.  It is the second
exponent isolated from formula (3.10). -/
def sourceCutoffExponent (beta tau : Real) : Real :=
  tau - beta / 8

/-- A constant multiple of the polynomial cutoff obtained after substituting
`W >= M^beta` into `b^(-1/8) M^tau`. -/
def sourceRawCutoff (M : Nat -> Nat) (K beta tau : Real) (n : Nat) : Real :=
  K * (M n : Real) ^ sourceCutoffExponent beta tau

/-- A bounded positive cutoff convenient for logarithmic truncation.  The
outer `min` does not change its asymptotic behavior. -/
def sourceCutoff (M : Nat -> Nat) (K beta tau : Real) (n : Nat) : Real :=
  min 1 (sourceRawCutoff M K beta tau n)

/-- The deterministic factor called `L_M` immediately before formula (3.10).
-/
def sourceHardEdgeScale
    (M W : Nat -> Nat) (kappa : Real) (n : Nat) : Real :=
  (M n : Real) ^ (1 + 3 * kappa) / (W n : Real) +
    2 * Real.log (M n : Real)

/-- The full deterministic error multiplying the hard-edge probability
input.  The constant `C` may depend on fixed model parameters (and on fixed
`z`), as allowed in Proposition 3.6. -/
def sourceHardEdgeError
    (M W : Nat -> Nat) (K beta tau kappa C : Real) (n : Nat) : Real :=
  C * sourceCutoff M K beta tau n * sourceHardEdgeScale M W kappa n

/-- A pure-power majorant for `sourceHardEdgeError`. -/
def sourceHardEdgeMajorant
    (M : Nat -> Nat) (K beta tau kappa C : Real) (n : Nat) : Real :=
  C * K *
    ((M n : Real) ^ hardEdgeFirstExponent beta tau kappa +
      2 * ((M n : Real) ^ sourceCutoffExponent beta tau *
        Real.log (M n : Real)))

/-- The factor occurring in the CDF-comparison bookkeeping in (3.12). -/
def sourceBulkCutoffBookkeeping
    (M : Nat -> Nat) (K beta tau R zeta : Real) (n : Nat) : Real :=
  (M n : Real) ^ (-zeta) *
    (Real.log R - Real.log (sourceCutoff M K beta tau n))

/-- A diverging natural-valued dimension sequence also diverges after its
cast to the reals. -/
theorem tendsto_natCast_comp_atTop
    {M : Nat -> Nat} (hM : Tendsto M atTop atTop) :
    Tendsto (fun n => (M n : Real)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp hM

/-- Formula (3.9) makes the cutoff exponent strictly negative. -/
theorem sourceCutoffExponent_neg
    {beta chi kappa tau : Real}
    (hparam : HardEdgeAdmissible beta chi kappa tau) :
    sourceCutoffExponent beta tau < 0 := by
  simpa [sourceCutoffExponent, hardEdgeSecondExponent] using
    hardEdgeSecondExponent_neg hparam

/-- The untruncated polynomial cutoff tends to zero. -/
theorem sourceRawCutoff_tendsto_zero
    {M : Nat -> Nat} {K beta chi kappa tau : Real}
    (hparam : HardEdgeAdmissible beta chi kappa tau)
    (hM : Tendsto M atTop atTop) :
    Tendsto (sourceRawCutoff M K beta tau) atTop (nhds 0) := by
  have hpow :
      Tendsto
        (fun n => (M n : Real) ^ sourceCutoffExponent beta tau)
        atTop (nhds 0) :=
    (tendsto_rpow_atTop_zero_of_neg (sourceCutoffExponent_neg hparam)).comp
      (tendsto_natCast_comp_atTop hM)
  change Tendsto
    (fun n => K * (M n : Real) ^ sourceCutoffExponent beta tau)
    atTop (nhds 0)
  simpa only [mul_zero] using hpow.const_mul K

/-- The bounded cutoff tends to zero as well. -/
theorem sourceCutoff_tendsto_zero
    {M : Nat -> Nat} {K beta chi kappa tau : Real}
    (hparam : HardEdgeAdmissible beta chi kappa tau)
    (hM : Tendsto M atTop atTop) :
    Tendsto (sourceCutoff M K beta tau) atTop (nhds 0) := by
  have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hraw := sourceRawCutoff_tendsto_zero (K := K) hparam hM
  have h := hone.min hraw
  change Tendsto (fun n => min 1 (sourceRawCutoff M K beta tau n))
    atTop (nhds 0)
  simpa only [min_eq_right zero_le_one] using h

/-- Eventually the harmless cap by one is inactive. -/
theorem sourceCutoff_eventually_eq_raw
    {M : Nat -> Nat} {K beta chi kappa tau : Real}
    (hparam : HardEdgeAdmissible beta chi kappa tau)
    (hM : Tendsto M atTop atTop) :
    sourceCutoff M K beta tau =ᶠ[atTop] sourceRawCutoff M K beta tau := by
  have hle : ∀ᶠ n in atTop, sourceRawCutoff M K beta tau n <= 1 :=
    (sourceRawCutoff_tendsto_zero hparam hM).eventually_le_const zero_lt_one
  filter_upwards [hle] with n hn
  exact min_eq_right hn

/-- The raw cutoff is positive at every positive dimension. -/
theorem sourceRawCutoff_pos
    {M : Nat -> Nat} {K beta tau : Real} {n : Nat}
    (hK : 0 < K) (hMn : 0 < M n) :
    0 < sourceRawCutoff M K beta tau n := by
  exact mul_pos hK
    (Real.rpow_pos_of_pos (by exact_mod_cast hMn) (sourceCutoffExponent beta tau))

/-- The bounded cutoff is positive at every positive dimension. -/
theorem sourceCutoff_pos
    {M : Nat -> Nat} {K beta tau : Real} {n : Nat}
    (hK : 0 < K) (hMn : 0 < M n) :
    0 < sourceCutoff M K beta tau n := by
  exact lt_min zero_lt_one (sourceRawCutoff_pos hK hMn)

/-- Along a diverging dimension sequence the cutoff is eventually strictly
positive, even if finitely many initial dimensions were allowed to be zero.
-/
theorem sourceCutoff_eventually_pos
    {M : Nat -> Nat} {K beta tau : Real}
    (hM : Tendsto M atTop atTop) (hK : 0 < K) :
    ∀ᶠ n in atTop, 0 < sourceCutoff M K beta tau n := by
  filter_upwards [hM.eventually_ge_atTop 1] with n hn
  exact sourceCutoff_pos hK (zero_lt_one.trans_le hn)

/-- The cutoff is bounded by one, without an asymptotic qualification. -/
theorem sourceCutoff_le_one
    {M : Nat -> Nat} {K beta tau : Real} {n : Nat} :
    sourceCutoff M K beta tau n <= 1 := by
  exact min_le_left _ _

/-- The hard-edge scale `L_M` is nonnegative when `M,W >= 1`. -/
theorem sourceHardEdgeScale_nonneg
    {M W : Nat -> Nat} {kappa : Real} {n : Nat}
    (hMn : 1 <= M n) (hWn : 1 <= W n) :
    0 <= sourceHardEdgeScale M W kappa n := by
  have hMreal : (1 : Real) <= M n := by exact_mod_cast hMn
  have hWreal : (0 : Real) < W n := by exact_mod_cast (zero_lt_one.trans_le hWn)
  exact add_nonneg
    (div_nonneg (Real.rpow_nonneg (by positivity) _) hWreal.le)
    (mul_nonneg (by norm_num) (Real.log_nonneg hMreal))

/-- Pointwise bandwidth substitution for the first part of `a_M L_M`.
This is the exponent computation behind the first summand in (3.10). -/
theorem sourceCutoffPower_mul_bandTerm_le
    {m w beta tau kappa : Real}
    (hm : 1 <= m) (hband : m ^ beta <= w) :
    m ^ sourceCutoffExponent beta tau *
        (m ^ (1 + 3 * kappa) / w) <=
      m ^ hardEdgeFirstExponent beta tau kappa := by
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  have hden : 0 < m ^ beta := Real.rpow_pos_of_pos hmpos beta
  calc
    m ^ sourceCutoffExponent beta tau *
          (m ^ (1 + 3 * kappa) / w) =
        m ^ (sourceCutoffExponent beta tau + (1 + 3 * kappa)) / w := by
          simp only [div_eq_mul_inv, <- mul_assoc, <- Real.rpow_add hmpos]
    _ <= m ^ (sourceCutoffExponent beta tau + (1 + 3 * kappa)) /
          (m ^ beta) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hmpos.le _) hden hband
    _ = m ^
          (sourceCutoffExponent beta tau + (1 + 3 * kappa) - beta) := by
      rw [Real.rpow_sub hmpos]
    _ = m ^ hardEdgeFirstExponent beta tau kappa := by
      congr 1
      simp only [sourceCutoffExponent, hardEdgeFirstExponent]
      ring

/-- Pointwise majorization of the full hard-edge deterministic error. -/
theorem sourceHardEdgeError_le_majorant
    {M W : Nat -> Nat} {K beta tau kappa C : Real} {n : Nat}
    (hK : 0 <= K) (hC : 0 <= C)
    (hMn : 1 <= M n)
    (hband : (M n : Real) ^ beta <= (W n : Real)) :
    sourceHardEdgeError M W K beta tau kappa C n <=
      sourceHardEdgeMajorant M K beta tau kappa C n := by
  have hm : (1 : Real) <= M n := by exact_mod_cast hMn
  have hmpos : (0 : Real) < M n := zero_lt_one.trans_le hm
  have hwpos : (0 : Real) < W n :=
    (Real.rpow_pos_of_pos hmpos beta).trans_le hband
  have hWn : 1 <= W n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
      intro hzero
      simp [hzero] at hwpos))
  have hL : 0 <= sourceHardEdgeScale M W kappa n :=
    sourceHardEdgeScale_nonneg hMn hWn
  have ha : sourceCutoff M K beta tau n <=
      sourceRawCutoff M K beta tau n := min_le_right _ _
  have hfirst := sourceCutoffPower_mul_bandTerm_le
    (beta := beta) (tau := tau) (kappa := kappa) hm hband
  have hcore :
      (M n : Real) ^ sourceCutoffExponent beta tau *
          sourceHardEdgeScale M W kappa n <=
        (M n : Real) ^ hardEdgeFirstExponent beta tau kappa +
          2 * ((M n : Real) ^ sourceCutoffExponent beta tau *
            Real.log (M n : Real)) := by
    calc
      (M n : Real) ^ sourceCutoffExponent beta tau *
          sourceHardEdgeScale M W kappa n =
        (M n : Real) ^ sourceCutoffExponent beta tau *
            ((M n : Real) ^ (1 + 3 * kappa) / (W n : Real)) +
          2 * ((M n : Real) ^ sourceCutoffExponent beta tau *
            Real.log (M n : Real)) := by
          simp only [sourceHardEdgeScale]
          ring
      _ <= (M n : Real) ^ hardEdgeFirstExponent beta tau kappa +
          2 * ((M n : Real) ^ sourceCutoffExponent beta tau *
            Real.log (M n : Real)) := add_le_add hfirst (le_refl _)
  calc
    sourceHardEdgeError M W K beta tau kappa C n <=
        C * sourceRawCutoff M K beta tau n *
          sourceHardEdgeScale M W kappa n := by
      simp only [sourceHardEdgeError]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha hC) hL
    _ = C * K *
        ((M n : Real) ^ sourceCutoffExponent beta tau *
          sourceHardEdgeScale M W kappa n) := by
      simp only [sourceRawCutoff]
      ring
    _ <= C * K *
        ((M n : Real) ^ hardEdgeFirstExponent beta tau kappa +
          2 * ((M n : Real) ^ sourceCutoffExponent beta tau *
            Real.log (M n : Real))) :=
      mul_le_mul_of_nonneg_left hcore (mul_nonneg hC hK)
    _ = sourceHardEdgeMajorant M K beta tau kappa C n := rfl

/-- The pure-power majorant tends to zero by the last two inequalities in
(3.9). -/
theorem sourceHardEdgeMajorant_tendsto_zero
    {M : Nat -> Nat} {K beta chi kappa tau C : Real}
    (hparam : HardEdgeAdmissible beta chi kappa tau)
    (hM : Tendsto M atTop atTop) :
    Tendsto (sourceHardEdgeMajorant M K beta tau kappa C)
      atTop (nhds 0) := by
  have hMreal := tendsto_natCast_comp_atTop hM
  have hfirst :
      Tendsto
        (fun n => (M n : Real) ^ hardEdgeFirstExponent beta tau kappa)
        atTop (nhds 0) :=
    (tendsto_rpow_atTop_zero_of_neg
      (hardEdgeFirstExponent_neg hparam)).comp hMreal
  have hsecond :
      Tendsto
        (fun n => (M n : Real) ^ sourceCutoffExponent beta tau *
          Real.log (M n : Real)) atTop (nhds 0) :=
    (tendsto_rpow_mul_log_atTop_zero_of_neg
      (sourceCutoffExponent_neg hparam)).comp hMreal
  have hsum := hfirst.add (hsecond.const_mul 2)
  have htotal := hsum.const_mul (C * K)
  change Tendsto
    (fun n => C * K *
      ((M n : Real) ^ hardEdgeFirstExponent beta tau kappa +
        2 * ((M n : Real) ^ sourceCutoffExponent beta tau *
          Real.log (M n : Real)))) atTop (nhds 0)
  simpa only [mul_zero, add_zero] using htotal

/-- Formula (3.10), with all deterministic cutoff choices discharged:
under the source bandwidth assumption, `C a_M L_M -> 0` for every fixed
nonnegative constant `C`. -/
theorem sourceHardEdgeError_tendsto_zero
    {M W : Nat -> Nat} {K beta chi kappa tau C : Real}
    (hparam : HardEdgeAdmissible beta chi kappa tau)
    (hM : Tendsto M atTop atTop)
    (hband : ∀ᶠ n in atTop,
      (M n : Real) ^ beta <= (W n : Real))
    (hK : 0 < K) (hC : 0 <= C) :
    Tendsto (sourceHardEdgeError M W K beta tau kappa C)
      atTop (nhds 0) := by
  have hMone : ∀ᶠ n in atTop, 1 <= M n :=
    hM.eventually_ge_atTop 1
  apply squeeze_zero'
  · filter_upwards [hMone, hband] with n hnM hnW
    have hm : (1 : Real) <= M n := by exact_mod_cast hnM
    have hmpos : (0 : Real) < M n := zero_lt_one.trans_le hm
    have hwpos : (0 : Real) < W n :=
      (Real.rpow_pos_of_pos hmpos beta).trans_le hnW
    have hWnat : 1 <= W n := by
      exact Nat.one_le_iff_ne_zero.mpr (by
        intro hzero
        simp [hzero] at hwpos)
    exact mul_nonneg
      (mul_nonneg hC (sourceCutoff_pos hK (zero_lt_one.trans_le hnM)).le)
      (sourceHardEdgeScale_nonneg hnM hWnat)
  · filter_upwards [hMone, hband] with n hnM hnW
    exact sourceHardEdgeError_le_majorant hK.le hC hnM hnW
  · exact sourceHardEdgeMajorant_tendsto_zero hparam hM

/-- Polynomial CDF comparison absorbs the logarithmic cutoff length in
(3.12).  In particular, no separate hypothesis of the form `hBulkScale` is
needed once the cutoff is chosen above. -/
theorem sourceBulkCutoffBookkeeping_tendsto_zero
    {M : Nat -> Nat} {K beta chi kappa tau R zeta : Real}
    (hparam : HardEdgeAdmissible beta chi kappa tau)
    (hM : Tendsto M atTop atTop)
    (hK : 0 < K) (_hR : 0 < R) (hzeta : 0 < zeta) :
    Tendsto (sourceBulkCutoffBookkeeping M K beta tau R zeta)
      atTop (nhds 0) := by
  have hMreal := tendsto_natCast_comp_atTop hM
  have hpow :
      Tendsto (fun n => (M n : Real) ^ (-zeta)) atTop (nhds 0) :=
    (tendsto_rpow_atTop_zero_of_neg (by linarith)).comp hMreal
  have hpowlog :
      Tendsto
        (fun n => (M n : Real) ^ (-zeta) * Real.log (M n : Real))
        atTop (nhds 0) :=
    (tendsto_rpow_mul_log_atTop_zero_of_neg (by linarith)).comp hMreal
  have hexplicit :
      Tendsto
        (fun n =>
          (Real.log R - Real.log K) * (M n : Real) ^ (-zeta) +
            (-sourceCutoffExponent beta tau) *
              ((M n : Real) ^ (-zeta) * Real.log (M n : Real)))
        atTop (nhds 0) := by
    simpa using
      (hpow.const_mul (Real.log R - Real.log K)).add
        (hpowlog.const_mul (-sourceCutoffExponent beta tau))
  have hMone : ∀ᶠ n in atTop, 1 <= M n := hM.eventually_ge_atTop 1
  have hcut := sourceCutoff_eventually_eq_raw (K := K) hparam hM
  apply hexplicit.congr'
  filter_upwards [hMone, hcut] with n hnM hncut
  have hmpos : (0 : Real) < M n := by exact_mod_cast (zero_lt_one.trans_le hnM)
  have hrpowpos :
      0 < (M n : Real) ^ sourceCutoffExponent beta tau :=
    Real.rpow_pos_of_pos hmpos _
  simp only [sourceBulkCutoffBookkeeping, hncut, sourceRawCutoff]
  rw [Real.log_mul hK.ne' hrpowpos.ne', Real.log_rpow hmpos]
  ring

end ShortRingAnchor
