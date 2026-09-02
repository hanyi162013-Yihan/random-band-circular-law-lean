import ShortRingAnchor.ShortRingModel
import ShortRingAnchor.SourceScales

/-!
# Comparing the manuscript and reconstructed hard-edge cutoffs

Immediately before (3.10), the proof of Proposition 3.6 uses the cutoff

`b(H_{M,W})^(-1/8) M^tau`.

The deterministic comparison `b(H_{M,W}) >= W / C0` from (2.2), together
with `W >= M^beta`, bounds this by

`C0^(1/8) M^(tau-beta/8)`.

This file proves that substitution pointwise and along a sequence.  It also
checks that the cap in `sourceCutoff = min 1 sourceRawCutoff` is eventually
inactive, so the manuscript cutoff is eventually bounded by the actual
cutoff used in the formal reconstruction.
-/

open Filter

noncomputable section

namespace ShortRingAnchor

/-- The hard-edge cutoff written immediately before formula (3.10). -/
def manuscriptHardEdgeCutoff
    {W : Nat} {c0 C0 : Real} (weights : AdmissibleWeights W c0 C0)
    (M : Nat) (tau : Real) : Real :=
  weights.bandwidthParameter ^ (-(1 / 8 : Real)) * (M : Real) ^ tau

/-- Pointwise bandwidth substitution in the manuscript cutoff:

`b(H)^(-1/8) M^tau <= C0^(1/8) M^(tau-beta/8)`.

This is the deterministic comparison used when passing from the cutoff
displayed before (3.10) to a pure power of `M`. -/
theorem manuscriptHardEdgeCutoff_le_power
    {M W : Nat} {c0 C0 beta tau : Real}
    (weights : AdmissibleWeights W c0 C0)
    (hM : 1 <= M)
    (hband : (M : Real) ^ beta <= (W : Real)) :
    manuscriptHardEdgeCutoff weights M tau <=
      C0 ^ (1 / 8 : Real) *
        (M : Real) ^ sourceCutoffExponent beta tau := by
  have hMreal : (1 : Real) <= M := by exact_mod_cast hM
  have hMpos : (0 : Real) < M := zero_lt_one.trans_le hMreal
  have hC0 : 0 < C0 := weights.C0_pos
  have hbasepos : 0 < (M : Real) ^ beta / C0 :=
    div_pos (Real.rpow_pos_of_pos hMpos beta) hC0
  have hbase : (M : Real) ^ beta / C0 <= weights.bandwidthParameter := by
    calc
      (M : Real) ^ beta / C0 <= (W : Real) / C0 :=
        div_le_div_of_nonneg_right hband hC0.le
      _ <= weights.bandwidthParameter :=
        weights.bandwidthParameter_linear_lower
  have hnegative : (-(1 / 8 : Real)) <= 0 := by norm_num
  have hrpow :
      weights.bandwidthParameter ^ (-(1 / 8 : Real)) <=
        ((M : Real) ^ beta / C0) ^ (-(1 / 8 : Real)) :=
    Real.rpow_le_rpow_of_nonpos hbasepos hbase hnegative
  calc
    manuscriptHardEdgeCutoff weights M tau <=
        ((M : Real) ^ beta / C0) ^ (-(1 / 8 : Real)) *
          (M : Real) ^ tau := by
      exact mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg hMpos.le tau)
    _ = C0 ^ (1 / 8 : Real) *
        (M : Real) ^ sourceCutoffExponent beta tau := by
      rw [Real.div_rpow (Real.rpow_nonneg hMpos.le beta) hC0.le]
      rw [← Real.rpow_mul hMpos.le beta (-(1 / 8 : Real))]
      rw [Real.rpow_neg hC0.le (1 / 8 : Real)]
      rw [div_inv_eq_mul]
      calc
        ((M : Real) ^ (beta * -(1 / 8 : Real)) *
              C0 ^ (1 / 8 : Real)) * (M : Real) ^ tau =
            C0 ^ (1 / 8 : Real) *
              ((M : Real) ^ (beta * -(1 / 8 : Real)) *
                (M : Real) ^ tau) := by ring
        _ = C0 ^ (1 / 8 : Real) *
              (M : Real) ^ (beta * -(1 / 8 : Real) + tau) := by
            rw [Real.rpow_add hMpos]
        _ = C0 ^ (1 / 8 : Real) *
              (M : Real) ^ sourceCutoffExponent beta tau := by
            congr 2
            simp only [sourceCutoffExponent]
            ring

/-- The same pointwise comparison with any fixed constant
`K >= C0^(1/8)`. -/
theorem manuscriptHardEdgeCutoff_le_raw_of_constant
    {M W : Nat} {c0 C0 beta tau K : Real}
    (weights : AdmissibleWeights W c0 C0)
    (hM : 1 <= M)
    (hband : (M : Real) ^ beta <= (W : Real))
    (hK : C0 ^ (1 / 8 : Real) <= K) :
    manuscriptHardEdgeCutoff weights M tau <=
      K * (M : Real) ^ sourceCutoffExponent beta tau := by
  refine (manuscriptHardEdgeCutoff_le_power weights hM hband).trans ?_
  exact mul_le_mul_of_nonneg_right hK
    (Real.rpow_nonneg (by positivity : (0 : Real) <= M)
      (sourceCutoffExponent beta tau))

/-- Along a bandwidth-admissible sequence, the manuscript cutoff is
eventually bounded by `sourceRawCutoff`. -/
theorem manuscriptHardEdgeCutoff_le_sourceRaw_eventually
    {M W : Nat -> Nat} {c0 C0 beta tau K : Real}
    (weights : forall n, AdmissibleWeights (W n) c0 C0)
    (hM : Tendsto M atTop atTop)
    (hband : ∀ᶠ n in atTop,
      (M n : Real) ^ beta <= (W n : Real))
    (hK : C0 ^ (1 / 8 : Real) <= K) :
    ∀ᶠ n in atTop,
      manuscriptHardEdgeCutoff (weights n) (M n) tau <=
        sourceRawCutoff M K beta tau n := by
  filter_upwards [hM.eventually_ge_atTop 1, hband] with n hMn hWn
  exact manuscriptHardEdgeCutoff_le_raw_of_constant
    (weights n) hMn hWn hK

/-- The cap `min 1` in the reconstructed cutoff does not obstruct the
manuscript cutoff: once the raw cutoff has fallen below one, the cap is
inactive and the pointwise comparison above applies unchanged. -/
theorem manuscriptHardEdgeCutoff_le_sourceCutoff_eventually
    {M W : Nat -> Nat} {c0 C0 beta chi kappa tau K : Real}
    (weights : forall n, AdmissibleWeights (W n) c0 C0)
    (hparam : HardEdgeAdmissible beta chi kappa tau)
    (hM : Tendsto M atTop atTop)
    (hband : ∀ᶠ n in atTop,
      (M n : Real) ^ beta <= (W n : Real))
    (hK : C0 ^ (1 / 8 : Real) <= K) :
    ∀ᶠ n in atTop,
      manuscriptHardEdgeCutoff (weights n) (M n) tau <=
        sourceCutoff M K beta tau n := by
  have hraw := manuscriptHardEdgeCutoff_le_sourceRaw_eventually
    (tau := tau) weights hM hband hK
  have hcap := sourceCutoff_eventually_eq_raw (K := K) hparam hM
  filter_upwards [hraw, hcap] with n hn hcapn
  rw [hcapn]
  exact hn

end ShortRingAnchor
