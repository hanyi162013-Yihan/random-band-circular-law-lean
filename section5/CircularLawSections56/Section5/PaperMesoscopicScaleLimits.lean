import CircularLawSections56.Section5.LiteralPressureAsymptoticClosure
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Concrete mesoscopic-scale limits

This file discharges the three real-asymptotic fields of
`PaperMesoscopicScaleChoice`.  The long-branch inequality supplies exactly the
extra power of `W` needed for the two seam terms; no separate eventual
positivity assumptions on `W` or `N` are required.
-/

open Filter Topology

namespace CircularLawSections56.Section5

/-- `log(e W) / W^a` vanishes for every positive exponent once `W → ∞`. -/
theorem paperLogEW_div_rpow_tendsto_zero
    (W : ℕ → ℕ) (hW : Tendsto W atTop atTop) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => paperLogEW W n / (W n : ℝ) ^ a) atTop (𝓝 0) := by
  have hWr : Tendsto (fun n => (W n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hW
  have hpos : ∀ᶠ n in atTop, 0 < (W n : ℝ) := hWr.eventually_gt_atTop 0
  have hlog :
      Tendsto (fun n => Real.log (W n : ℝ) / (W n : ℝ) ^ a) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero).comp hWr
  have hconst : Tendsto (fun n => (1 : ℝ) / (W n : ℝ) ^ a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop ha).comp hWr)
  have heq :
      (fun n => paperLogEW W n / (W n : ℝ) ^ a) =ᶠ[atTop]
        (fun n => (1 : ℝ) / (W n : ℝ) ^ a +
          Real.log (W n : ℝ) / (W n : ℝ) ^ a) := by
    filter_upwards [hpos] with n hn
    rw [paperLogEW, Real.log_mul (Real.exp_ne_zero 1) hn.ne']
    simp only [Real.log_exp]
    ring
  simpa only [zero_add] using (hconst.add hlog).congr' heq.symm

private theorem eventually_paperLogEW_nonneg
    (W : ℕ → ℕ) (hW : Tendsto W atTop atTop) :
    ∀ᶠ n in atTop, 0 ≤ paperLogEW W n := by
  have hWr : Tendsto (fun n => (W n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hW
  filter_upwards [hWr.eventually_gt_atTop 0] with n hn
  rw [paperLogEW, Real.log_mul (Real.exp_ne_zero 1) hn.ne']
  have hone : (1 : ℝ) ≤ (W n : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hn.ne'))
  simpa only [Real.log_exp] using
    add_nonneg (zero_le_one : (0 : ℝ) ≤ 1) (Real.log_nonneg hone)

/-- The normalized one-cell scale `W log(eW) / ceil(W^(1+δ))` vanishes. -/
theorem paperCellErrorScale_div_mesoscopicLength_tendsto_zero
    (δ : ℝ) (W : ℕ → ℕ) (hδ : 0 < δ) (hW : Tendsto W atTop atTop) :
    Tendsto
      (fun n => paperCellErrorScale W n /
        (paperMesoscopicCellLength δ W n : ℝ)) atTop (𝓝 0) := by
  have hWr : Tendsto (fun n => (W n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hW
  have hupper := paperLogEW_div_rpow_tendsto_zero W hW hδ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [hWr.eventually_gt_atTop 0, eventually_paperLogEW_nonneg W hW]
      with n hn hlog
    exact div_nonneg (mul_nonneg hn.le hlog) (Nat.cast_nonneg _)
  · filter_upwards [hWr.eventually_gt_atTop 0, eventually_paperLogEW_nonneg W hW]
      with n hn hlog
    have hpowpos : 0 < (W n : ℝ) ^ (1 + δ) := Real.rpow_pos_of_pos hn _
    have hceil : (W n : ℝ) ^ (1 + δ) ≤
        (paperMesoscopicCellLength δ W n : ℝ) := Nat.le_ceil _
    calc
      paperCellErrorScale W n / (paperMesoscopicCellLength δ W n : ℝ)
          ≤ paperCellErrorScale W n / (W n : ℝ) ^ (1 + δ) :=
        div_le_div_of_nonneg_left (mul_nonneg hn.le hlog) hpowpos hceil
      _ = paperLogEW W n / (W n : ℝ) ^ δ := by
        rw [paperCellErrorScale, Real.rpow_add hn 1 δ, Real.rpow_one]
        field_simp

/-- The balanced incomplete-cell rate `log(eW) / ceil(W^(1+δ))` vanishes. -/
theorem paperBalancedRemainderRate_tendsto_zero
    (δ : ℝ) (W : ℕ → ℕ) (hδ : 0 < δ) (hW : Tendsto W atTop atTop) :
    Tendsto (paperBalancedRemainderRate δ W) atTop (𝓝 0) := by
  have hWr : Tendsto (fun n => (W n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hW
  have hupper := paperLogEW_div_rpow_tendsto_zero W hW (show 0 < 1 + δ by linarith)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [hWr.eventually_gt_atTop 0, eventually_paperLogEW_nonneg W hW]
      with n hn hlog
    exact div_nonneg hlog (Nat.cast_nonneg _)
  · filter_upwards [hWr.eventually_gt_atTop 0, eventually_paperLogEW_nonneg W hW]
      with n hn hlog
    have hpowpos : 0 < (W n : ℝ) ^ (1 + δ) := Real.rpow_pos_of_pos hn _
    have hceil : (W n : ℝ) ^ (1 + δ) ≤
        (paperMesoscopicCellLength δ W n : ℝ) := Nat.le_ceil _
    exact div_le_div_of_nonneg_left hlog hpowpos hceil

/-- The two long-branch seam terms vanish under `W^(1+γ) < N` eventually. -/
theorem paperFinalSeamRate_tendsto_zero
    (γ : ℝ) (W N : ℕ → ℕ) (hγ : 0 < γ) (hW : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, (W n : ℝ) ^ (1 + γ) < (N n : ℝ)) :
    Tendsto (paperFinalSeamRate W N) atTop (𝓝 0) := by
  have hWr : Tendsto (fun n => (W n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hW
  have hfirst := paperLogEW_div_rpow_tendsto_zero W hW hγ
  have hsecond := paperLogEW_div_rpow_tendsto_zero W hW (half_pos hγ)
  have hupper :
      Tendsto
        (fun n => paperLogEW W n / (W n : ℝ) ^ γ +
          paperLogEW W n / (W n : ℝ) ^ (γ / 2)) atTop (𝓝 0) := by
    simpa only [zero_add] using hfirst.add hsecond
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_paperLogEW_nonneg W hW] with n hlog
    exact add_nonneg
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog) (Nat.cast_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) hlog)
  · filter_upwards [hWr.eventually_gt_atTop 0, eventually_paperLogEW_nonneg W hW,
      hlong] with n hn hlog hnlong
    have hpowpos : 0 < (W n : ℝ) ^ (1 + γ) := Real.rpow_pos_of_pos hn _
    have hfirstBound :
        paperCellErrorScale W n / (N n : ℝ) ≤
          paperLogEW W n / (W n : ℝ) ^ γ := by
      calc
        paperCellErrorScale W n / (N n : ℝ)
            ≤ paperCellErrorScale W n / (W n : ℝ) ^ (1 + γ) :=
          div_le_div_of_nonneg_left (mul_nonneg hn.le hlog) hpowpos hnlong.le
        _ = paperLogEW W n / (W n : ℝ) ^ γ := by
          rw [paperCellErrorScale, Real.rpow_add hn 1 γ, Real.rpow_one]
          field_simp
    have hratio :
        (W n : ℝ) / (N n : ℝ) ≤
          (W n : ℝ) / (W n : ℝ) ^ (1 + γ) :=
      div_le_div_of_nonneg_left hn.le hpowpos hnlong.le
    have hsqrt := Real.sqrt_le_sqrt hratio
    have hsecondBound :
        Real.sqrt ((W n : ℝ) / (N n : ℝ)) * paperLogEW W n ≤
          paperLogEW W n / (W n : ℝ) ^ (γ / 2) := by
      calc
        Real.sqrt ((W n : ℝ) / (N n : ℝ)) * paperLogEW W n
            ≤ Real.sqrt ((W n : ℝ) / (W n : ℝ) ^ (1 + γ)) *
                paperLogEW W n := mul_le_mul_of_nonneg_right hsqrt hlog
        _ = paperLogEW W n / (W n : ℝ) ^ (γ / 2) := by
          have hquot :
              (W n : ℝ) / (W n : ℝ) ^ (1 + γ) = (W n : ℝ) ^ (-γ) := by
            calc
              (W n : ℝ) / (W n : ℝ) ^ (1 + γ)
                  = (W n : ℝ) ^ 1 / (W n : ℝ) ^ (1 + γ) := by
                    rw [Real.rpow_one]
              _ = (W n : ℝ) ^ (1 - (1 + γ)) :=
                (Real.rpow_sub hn 1 (1 + γ)).symm
              _ = (W n : ℝ) ^ (-γ) := by
                congr 1
                ring
          rw [hquot, Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
          have hmul : (-γ) * (1 / 2 : ℝ) = -(γ / 2) := by ring
          rw [hmul, Real.rpow_neg hn.le]
          ring
    exact add_le_add hfirstBound hsecondBound

/-- Construct the manuscript's concrete scale contract from its structural assumptions.

All three limit fields are proved here.  Eventual positivity of the bandwidth follows
from `W → ∞`, while positivity of the dimension on the long branch follows from the
strict comparison with `W^(1+γ)`.
-/
theorem paperMesoscopicScaleChoice_of_tendsto_of_eventually_longBranch
    (δ γ : ℝ) (W N : ℕ → ℕ)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8)
    (hW : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, (W n : ℝ) ^ (1 + γ) < (N n : ℝ)) :
    PaperMesoscopicScaleChoice δ γ W N where
  delta_pos := hδ
  delta_lt_gamma := hδγ
  gamma_lt_one_eighth := hγ
  bandwidth_tendsto := hW
  long_branch := hlong
  cell_error_rate_zero := paperCellErrorScale_div_mesoscopicLength_tendsto_zero δ W hδ hW
  final_seam_rate_zero :=
    paperFinalSeamRate_tendsto_zero γ W N (lt_trans hδ hδγ) hW hlong
  balanced_remainder_rate_zero := paperBalancedRemainderRate_tendsto_zero δ W hδ hW

end CircularLawSections56.Section5
