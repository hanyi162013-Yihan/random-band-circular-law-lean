/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/ModelNumerics.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.PlanarSmallBall

/-! Numerical closure with the dimension loss of the proved planar density bound. -/

noncomputable section
namespace HighBandLSV
open Filter

theorem certificate_raw_log_bound {N J r : Nat} {W kappa R Kz A C1 c Cw : Real}
    (h : NumericalCertificate N J r W kappa R Kz A C1 c Cw) :
    Real.log (rawFixedBound N J r W kappa A C1 (hsCap N R Kz)) ≤
      -(c * W * lambda N W kappa) +
        24 * ((N : Real) * Real.log N + (J : Real) * lambda N W kappa) := by
  have hN : (1 : Real) ≤ N := by exact_mod_cast h.N_pos
  have hJ : (0 : Real) < J := by exact_mod_cast h.J_pos
  have hJN : (J : Real) ≤ N := by exact_mod_cast h.J_le_N
  have hK0 : 0 ≤ R + Kz + 1 := by linarith [h.R_nonneg, h.Kz_nonneg]
  have hK : 0 < hsCap N R Kz + 1 := by unfold hsCap; positivity
  have hrJN : (r : Real) * J ≤ N := by exact_mod_cast h.rows_le
  have hrN : r ≤ N := calc
    r = r * 1 := by omega
    _ ≤ r * J := Nat.mul_le_mul_left r (Nat.succ_le_of_lt h.J_pos)
    _ ≤ N := h.rows_le
  obtain ⟨ha, hb, hc, hd⟩ := hs_cap_log_bounds hN hJ hJN h.entropy.W_pos
    h.C_pos h.C1_pos hK0 (by linarith [h.Cw_ge_one]) h.bandwidth_upper
    h.constant_C h.constant_mesh h.constant_ratio h.constant_variance
  have hrem := remainder_le_24 hN hJ.le hJN (Nat.cast_nonneg r)
    (show (r : Real) ≤ N by exact_mod_cast hrN) hrJN ha hb hc hd
  rw [log_rawFixedBound h.J_pos h.entropy.W_pos h.C_pos h.C1_pos hK]
  exact envelope_le_entropy_gain h.entropy.N_pos h.entropy.W_pos hJ.le
    h.deficit_le h.rows_lower hrem

theorem certificate_dimension_loss_union {N J r : Nat} {W kappa R Kz A C1 c Cw : Real}
    (h : NumericalCertificate N J r W kappa R Kz A C1 c Cw)
    (he : CorrectedSection5NumericalConditions N W kappa J 28 c) :
    (N * J * J : Real) * (N : Real) ^ (r * J) *
      rawFixedBound N J r W kappa A C1 (hsCap N R Kz) ≤
        Real.exp (-(N : Real) ^ (1 + kappa / 4)) := by
  have hK : 0 < hsCap N R Kz + 1 := by
    have hK0 : 0 ≤ R + Kz + 1 := by linarith [h.R_nonneg, h.Kz_nonneg]
    unfold hsCap
    positivity
  have hp : 0 < rawFixedBound N J r W kappa A C1 (hsCap N R Kz) := by
    rw [rawFixedBound_eq_exp h.J_pos h.entropy.W_pos h.C_pos h.C1_pos hK]
    exact Real.exp_pos _
  simpa only [Nat.cast_mul] using dimension_loss_normal_union
    (Nat.succ_le_of_lt h.N_pos) h.J_pos h.J_le_N h.rows_le hp he h.normal_growth
    (certificate_raw_log_bound h)

theorem eventually_seed_size {chi : Real} (hchi : 0 < chi) (W : Nat → Nat)
    (hband : ∀ᶠ n : Nat in atTop, (n : Real) ^ (1 / 2 + chi) ≤ W n) :
    ∀ᶠ n : Nat in atTop, 8 ≤ seedSize n (W n) := by
  have hg := eventually_le_mul_natCast_rpow (A := 64) (B := 1)
    (by norm_num : (0 : Real) < 1) (by linarith : (0 : Real) < 1 / 2 + chi)
  filter_upwards [hband, hg, eventually_ge_atTop 64] with n hn hg hn64
  have hW : 64 ≤ W n := by
    have : (64 : Real) ≤ W n := by nlinarith
    exact_mod_cast this
  unfold seedSize
  omega

theorem eventually_model_numerics {chi kappa R Kz A C1 Cw : Real}
    (hchi : 0 < chi) (hk : 0 < kappa) (hR : 0 ≤ R) (hKz : 0 ≤ Kz)
    (hA : 0 < A) (hC1 : 0 < C1) (hCw : 1 ≤ Cw) (W : Nat → Nat)
    (hWp : ∀ᶠ n : Nat in atTop, 0 < W n)
    (hband : ∀ᶠ n : Nat in atTop, (n : Real) ^ (1 / 2 + chi) ≤ W n)
    (hupper : ∀ᶠ n : Nat in atTop, (W n : Real) ≤ Cw * n) :
    ∀ᶠ n : Nat in atTop,
      8 ≤ seedSize n (W n) ∧
      NumericalCertificate n (blockCount n (W n)) (retainedRows n (W n))
        (W n) kappa R Kz A C1 (1 / (64 * Cw)) Cw ∧
      CorrectedSection5NumericalConditions n (W n) kappa (blockCount n (W n))
        28 (1 / (64 * Cw)) ∧
      Real.log (dimensionLossColumnPrefactor n (W n)) ≤
        Section5Formalization.finalExponentGap n (W n) kappa := by
  have hs := eventually_seed_size hchi W hband
  have hn := eventually_actual_numerics hchi hk hR hKz hA hC1 hCw W hWp hband hupper
  have hcount : ∀ᶠ n : Nat in atTop,
      (blockCount n (W n) : Real) ≤ (32 * Cw) * n / W n := by
    filter_upwards [hs, hupper] with n hs hu
    exact (actual_partition_bounds hs hCw hu).count_scale
  have he := eventually_correctedSection5NumericalConditions hk hchi
    (by norm_num : (0 : Real) ≤ 28) (by linarith : (0 : Real) ≤ 32 * Cw)
    (by positivity : (0 : Real) < 1 / (64 * Cw)) W
    (fun n => blockCount n (W n)) hWp hband hcount
  have h2p : ∀ᶠ n : Nat in atTop, 0 < 2 * W n := by
    filter_upwards [hWp] with n hn
    omega
  have h2u : ∀ᶠ n : Nat in atTop, ((2 * W n : Nat) : Real) ≤ (2 * Cw) * n := by
    filter_upwards [hupper] with n hn
    push_cast
    nlinarith
  have hg := eventually_final_log_dominance hk (by linarith : 1 ≤ 2 * Cw)
    (fun n => 2 * W n) h2p h2u
  filter_upwards [hs, hn, he, hg, hWp, eventually_ge_atTop 1] with n hs hn he hg hw hn1
  refine ⟨hs, hn, he, ?_⟩
  apply dimension_loss_final_gap
    (by exact_mod_cast hn1) (by exact_mod_cast hw)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hg

end HighBandLSV

#print axioms HighBandLSV.eventually_model_numerics
#print axioms HighBandLSV.certificate_dimension_loss_union

