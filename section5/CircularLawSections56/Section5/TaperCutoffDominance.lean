import CircularLawSections56.Section5.TaperEffectiveBandwidth
import ShortRingAnchor.SourceScales

/-! # Section 3's cutoff for the actual taper effective bandwidth

Only the largest variance, not a uniform lower bound on every band weight,
enters this substitution. This is the deterministic adapter needed to rerun
the accepted Section 3 truncation theorem with the inner half-band.
-/

open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace CircularLawSections56.Section5
open ShortRingAnchor

def PolynomialTaperProfile.hardEdgeCutoff
    (p : PolynomialTaperProfile) (M W : ℕ) (τ : ℝ) : ℝ :=
  p.effectiveBandwidth W ^ (-(1 / 8 : ℝ)) * (M : ℝ) ^ τ

theorem PolynomialTaperProfile.hardEdgeCutoff_le_power
    (p : PolynomialTaperProfile) (M W : ℕ) (hM : 0 < M) (hW : 0 < W)
    (β τ : ℝ) (hband : (M : ℝ) ^ β ≤ W) :
    p.hardEdgeCutoff M W τ ≤ p.upperWeightConstant ^ (1 / 8 : ℝ) *
      (M : ℝ) ^ sourceCutoffExponent β τ := by
  have hMr : 0 < (M : ℝ) := Nat.cast_pos.2 hM
  have hC := p.upperWeightConstant_pos
  have hbasepos : 0 < (M : ℝ) ^ β / p.upperWeightConstant :=
    div_pos (Real.rpow_pos_of_pos hMr β) hC
  have hbase : (M : ℝ) ^ β / p.upperWeightConstant ≤ p.effectiveBandwidth W :=
    (div_le_div_of_nonneg_right hband hC.le).trans (p.effectiveBandwidth_comparable W hW).1
  have hrpow := Real.rpow_le_rpow_of_nonpos hbasepos hbase (by norm_num : -(1 / 8 : ℝ) ≤ 0)
  calc
    _ ≤ ((M : ℝ) ^ β / p.upperWeightConstant) ^ (-(1 / 8 : ℝ)) * (M : ℝ) ^ τ :=
      mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg hMr.le τ)
    _ = _ := by
      rw [Real.div_rpow (Real.rpow_nonneg hMr.le β) hC.le,
        ← Real.rpow_mul hMr.le β (-(1 / 8 : ℝ)),
        Real.rpow_neg hC.le (1 / 8 : ℝ), div_inv_eq_mul]
      calc
        _ = p.upperWeightConstant ^ (1 / 8 : ℝ) *
            ((M : ℝ) ^ (β * -(1 / 8 : ℝ)) * (M : ℝ) ^ τ) := by ring
        _ = p.upperWeightConstant ^ (1 / 8 : ℝ) *
            (M : ℝ) ^ (β * -(1 / 8 : ℝ) + τ) := by rw [Real.rpow_add hMr]
        _ = _ := by congr 2; unfold sourceCutoffExponent; ring

theorem PolynomialTaperProfile.hardEdgeCutoff_le_sourceCutoff_eventually
    (p : PolynomialTaperProfile) (M W V : ℕ → ℕ) (β χ κ τ K : ℝ)
    (hparam : HardEdgeAdmissible β χ κ τ)
    (hM : Tendsto M atTop atTop) (hWpos : ∀ n, 0 < W n)
    (hVW : ∀ n, V n ≤ W n)
    (hband : ∀ᶠ n in atTop, (M n : ℝ) ^ β ≤ V n)
    (hK : p.upperWeightConstant ^ (1 / 8 : ℝ) ≤ K) :
    ∀ᶠ n in atTop, p.hardEdgeCutoff (M n) (W n) τ ≤ sourceCutoff M K β τ n := by
  filter_upwards [hM.eventually_ge_atTop 1, hband,
    sourceCutoff_eventually_eq_raw (K := K) hparam hM] with n hMn hbn hcap
  rw [hcap]
  apply (p.hardEdgeCutoff_le_power (M n) (W n) (by omega) (hWpos n) β τ
    (hbn.trans (Nat.cast_le.2 (hVW n)))).trans
  exact mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end CircularLawSections56.Section5
