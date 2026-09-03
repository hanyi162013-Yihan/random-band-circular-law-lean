import CircularLawSection6.PublishedCyclicGinibre
import CircularLawSection6.ClampedCoreProfile
import CircularLawSection6.QuadraticBlockScale
import CircularLawSection6.ProfileCompactSourceBridge

/-! # The actual core weights and automatic polynomial local scales

The core's Section 3 weights are constructed from the positive profile. In the
quadratic block window the quarter-power dimension bound is eventual, so the
published comparison uses the fixed exponent 1/8 after absorbing the profile
constant. Neither bound is an extra asymptotic hypothesis.
-/

open MeasureTheory Filter Topology ShortRingAnchor
open CircularLawSections56.Section5
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem quadraticBlockScale_quarter_power_eventually
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (M : ℕ → ℕ)
    (hM : ∀ n, M n ≤ 2 * quadraticBlockScale (H n)) :
    ∀ᶠ n in atTop, (M n : ℝ) ^ (1 / 4 : ℝ) ≤ H n := by
  filter_upwards [hH.eventually (eventually_ge_atTop 5)] with n hn
  have hH5 : (5 : ℝ) ≤ H n := by exact_mod_cast hn
  have hm : (M n : ℝ) ≤ 8 * (H n : ℝ) ^ 2 + 8 * H n + 2 := by
    exact_mod_cast quadraticBlockScale_window_bound (hM n)
  have hh : (18 : ℝ) ≤ (H n : ℝ) ^ 2 := by nlinarith
  have hm4 : (M n : ℝ) ≤ (H n : ℝ) ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg (H n : ℝ))]
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) < 4)).1
  rw [← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num only [show (1 / 4 : ℝ) * 4 = 1 by norm_num, Real.rpow_one,
    Real.rpow_ofNat]
  exact hm4

theorem cyclic_bandwidth_eighth_power_eventually
    {H M : ℕ → ℕ} {c₀ C₀ : ℝ}
    (weights : ∀ n, AdmissibleWeights (H n) c₀ C₀)
    (hH : Tendsto H atTop atTop)
    (hfit : ∀ n, 2 * H n + 1 ≤ M n)
    (hwindow : ∀ n, M n ≤ 2 * quadraticBlockScale (H n)) :
    ∀ᶠ n in atTop, (M n : ℝ) ^ (1 / 8 : ℝ) ≤ (weights n).bandwidthParameter := by
  have hM : Tendsto M atTop atTop := tendsto_atTop_mono (fun n => by
    have h := hfit n
    omega) hH
  have hpow : Tendsto (fun n => (M n : ℝ) ^ (1 / 8 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      (tendsto_natCast_atTop_atTop.comp hM)
  filter_upwards [hpow.eventually (eventually_ge_atTop C₀),
    quadraticBlockScale_quarter_power_eventually H hH M hwindow] with n hc hquarter
  have hpos : (0 : ℝ) < M n := by exact_mod_cast (show 0 < M n by have h := hfit n; omega)
  calc
    (M n : ℝ) ^ (1 / 8 : ℝ) ≤ (M n : ℝ) ^ (1 / 4 : ℝ) / C₀ := by
      apply (le_div_iff₀ (weights n).C0_pos).2
      calc
        _ ≤ (M n : ℝ) ^ (1 / 8 : ℝ) * (M n : ℝ) ^ (1 / 8 : ℝ) :=
          mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hpos.le _)
        _ = _ := by rw [← Real.rpow_add hpos]; norm_num
    _ ≤ (H n : ℝ) / C₀ := div_le_div_of_nonneg_right hquarter (weights n).C0_pos.le
    _ ≤ _ := (weights n).bandwidthParameter_linear_lower

namespace CoreRadiusBounds

variable {p : NoncompactProfile} {R : ℝ}

def localSection3Weights (B : CoreRadiusBounds p R) (N H : ℕ) [NeZero N]
    (hH : 0 < H) (hfit : 2 * H + 1 ≤ N) (W : ℝ) (hW : 0 < W)
    (hHW : (H : ℝ) ≤ R * W) : AdmissibleWeights H (B.lower / B.upper) (B.upper / B.lower) :=
  paperSection3Weights (B.coreWeights N H hH hfit W hW hHW)
    (canonicalCoreBand_width hH) (div_pos B.lower_pos B.upper_pos)

theorem localSection3Weights_amplitude (B : CoreRadiusBounds p R) (N H : ℕ) [NeZero N]
    (hH : 0 < H) (hfit : 2 * H + 1 ≤ N) (W : ℝ) (hW : 0 < W)
    (hHW : (H : ℝ) ≤ R * W) (s : Fin (2 * H + 1)) :
    (Real.sqrt ((B.localSection3Weights N H hH hfit W hW hHW).q s) : ℂ) =
      p.coreRoutedAmplitude N (canonicalCoreBand H) H (canonicalCoreBand_width hH)
        (canonicalCoreCenter H hH) W s := rfl

end CoreRadiusBounds
end CircularLawSection6
