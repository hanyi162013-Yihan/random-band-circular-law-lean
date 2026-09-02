import CircularLawSections56.Section5.PaperLiteralGeometry
import CircularLawSections56.Section5.TaperInnerBand

/-! # The two Section 3 uses satisfy the actual high-bandwidth exponent

A single positive exponent margin works for the natural short branch and for
every mesoscopic length. The taper inner band then retains half this margin.
These are deterministic eligibility deductions, not new random-matrix inputs.
-/

open Filter Topology
noncomputable section
set_option maxHeartbeats 1400000
set_option autoImplicit false

namespace CircularLawSections56.Section5

def section3Margin (γ : ℝ) : ℝ := (1 / (1 + γ) - 8 / 9) / 2

theorem section3Margin_spec (γ : ℝ) (hγpos : 0 < γ) (hγ : γ < 1 / 8) :
    0 < section3Margin γ ∧ section3Margin γ < 1 / 9 ∧
      0 < 8 / 9 + section3Margin γ ∧
      (1 + γ) * (8 / 9 + section3Margin γ) < 1 := by
  have hden : 0 < 1 + γ := by linarith
  have hlo : (8 / 9 : ℝ) < 1 / (1 + γ) := (lt_div_iff₀ hden).2 (by nlinarith)
  have hhi : 1 / (1 + γ) < (1 : ℝ) := (div_lt_one hden).2 (by linarith)
  have heq : (1 + γ) * (1 / (1 + γ)) = 1 := by field_simp [ne_of_gt hden]
  unfold section3Margin
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

theorem high_band_of_short_threshold
    (M W : ℕ) (γ : ℝ) (hW : 0 < W) (hγpos : 0 < γ) (hγ : γ < 1 / 8)
    (hshort : (M : ℝ) ≤ (W : ℝ) ^ (1 + γ)) :
    (M : ℝ) ^ (8 / 9 + section3Margin γ) ≤ W := by
  have hs := section3Margin_spec γ hγpos hγ
  have hw : 1 ≤ (W : ℝ) := by exact_mod_cast (show 1 ≤ W by omega)
  calc
    _ ≤ ((W : ℝ) ^ (1 + γ)) ^ (8 / 9 + section3Margin γ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hshort hs.2.2.1.le
    _ = (W : ℝ) ^ ((1 + γ) * (8 / 9 + section3Margin γ)) :=
      (Real.rpow_mul (Nat.cast_nonneg _) _ _).symm
    _ ≤ (W : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hw hs.2.2.2.le
    _ = _ := Real.rpow_one _

theorem natural_short_branch_high_band
    (W : ℕ → ℕ) (γ : ℝ) (hγpos : 0 < γ) (hγ : γ < 1 / 8)
    (n : ℕ) (hW : 0 < W n) (hn : paperNaturalShortBranch W γ n = true) :
    (n + 1 : ℝ) ^ (8 / 9 + section3Margin γ) ≤ W n := by
  have hs : ((n + 1 : ℕ) : ℝ) ≤ (W n : ℝ) ^ (1 + γ) := by
    simpa only [paperNaturalShortBranch, decide_eq_true_eq, Nat.cast_add, Nat.cast_one] using hn
  simpa only [Nat.cast_add, Nat.cast_one] using
    high_band_of_short_threshold (n + 1) (W n) γ hW hγpos hγ hs

theorem eventually_mesoscopic_length_le_short_threshold
    (W : ℕ → ℕ) (δ γ : ℝ) (hδ : 0 < δ) (hδγ : δ < γ)
    (hW : Tendsto W atTop atTop) :
    ∀ᶠ n in atTop, ∀ m : ℕ, m ≤ 2 * paperMesoscopicCellLength δ W n →
      (m : ℝ) ≤ (W n : ℝ) ^ (1 + γ) := by
  have hWr : Tendsto (fun n => (W n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hW
  have hgap := ((tendsto_rpow_atTop (sub_pos.2 hδγ)).comp hWr).eventually_ge_atTop 4
  filter_upwards [hgap, hW.eventually_ge_atTop 1] with n hn hWn m hm
  change 4 ≤ (W n : ℝ) ^ (γ - δ) at hn
  have hw : 1 ≤ (W n : ℝ) := by exact_mod_cast hWn
  have hwpos : 0 < (W n : ℝ) := by linarith
  have hp : 1 ≤ (W n : ℝ) ^ (1 + δ) := Real.one_le_rpow hw (by linarith)
  have hceil : (paperMesoscopicCellLength δ W n : ℝ) < (W n : ℝ) ^ (1 + δ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hm' : (m : ℝ) ≤ 2 * (paperMesoscopicCellLength δ W n : ℝ) := by exact_mod_cast hm
  have hmul := mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hwpos.le (1 + δ))
  have he : (W n : ℝ) ^ (1 + δ) * (W n : ℝ) ^ (γ - δ) = (W n : ℝ) ^ (1 + γ) := by
    rw [← Real.rpow_add hwpos]
    congr 1
    ring
  rw [he] at hmul
  linarith

theorem eventually_all_mesoscopic_lengths_high_band
    (W : ℕ → ℕ) (δ γ : ℝ) (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8)
    (hW : Tendsto W atTop atTop) :
    ∀ᶠ n in atTop, ∀ m : ℕ, m ≤ 2 * paperMesoscopicCellLength δ W n →
      (m : ℝ) ^ (8 / 9 + section3Margin γ) ≤ W n := by
  filter_upwards [eventually_mesoscopic_length_le_short_threshold W δ γ hδ hδγ hW,
    hW.eventually_ge_atTop 1] with n hn hWn m hm
  exact high_band_of_short_threshold m (W n) γ (by omega) (hδ.trans hδγ) hγ (hn m hm)

theorem eventually_mesoscopic_ring_band_fits
    (W : ℕ → ℕ) (δ : ℝ) (hδ : 0 < δ) (hW : Tendsto W atTop atTop) :
    ∀ᶠ n in atTop, ∀ m : ℕ, paperMesoscopicCellLength δ W n ≤ m → 2 * W n + 1 ≤ m := by
  have hWr : Tendsto (fun n => (W n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hW
  have hlarge := ((tendsto_rpow_atTop hδ).comp hWr).eventually_ge_atTop 3
  filter_upwards [hlarge, hW.eventually_ge_atTop 1] with n hn hw m hm
  change 3 ≤ (W n : ℝ) ^ δ at hn
  have hw' : 1 ≤ (W n : ℝ) := by exact_mod_cast hw
  have hmul := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (W n))
  have hpow : (W n : ℝ) ^ (1 + δ) = (W n : ℝ) * (W n : ℝ) ^ δ := by
    rw [Real.rpow_add (by linarith : 0 < (W n : ℝ)), Real.rpow_one]
  have hceil : (W n : ℝ) ^ (1 + δ) ≤ (paperMesoscopicCellLength δ W n : ℝ) := Nat.le_ceil _
  have hm' : (paperMesoscopicCellLength δ W n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [hpow] at hceil
  have hbound : (2 : ℝ) * W n + 1 ≤ (m : ℝ) := by linarith
  exact_mod_cast hbound

theorem mesoscopic_length_tendsto
    (W m : ℕ → ℕ) (δ : ℝ) (hδ : 0 < δ) (hW : Tendsto W atTop atTop)
    (hm : ∀ᶠ n in atTop, paperMesoscopicCellLength δ W n ≤ m n) :
    Tendsto m atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_mesoscopic_ring_band_fits W δ hδ hW, hm,
    hW.eventually_ge_atTop b] with n hfit hmn hWn
  have h := hfit (m n) hmn
  omega

/-- A chosen auxiliary taper ring meets the inner-band high-band condition,
with an explicit positive exponent margin inherited from the same `γ`. -/
theorem mesoscopic_taper_inner_band_eligibility
    (W m : ℕ → ℕ) (δ γ : ℝ) (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8)
    (hW : Tendsto W atTop atTop)
    (hm : ∀ᶠ n in atTop,
      paperMesoscopicCellLength δ W n ≤ m n ∧ m n ≤ 2 * paperMesoscopicCellLength δ W n) :
    Tendsto m atTop atTop ∧ Tendsto (fun n => W n / 2) atTop atTop ∧
      ∀ᶠ n in atTop, 2 * W n + 1 ≤ m n ∧
        (m n : ℝ) ^ (8 / 9 + section3Margin γ / 2) ≤ (W n / 2 : ℕ) := by
  have hM := mesoscopic_length_tendsto W m δ hδ hW (hm.mono (fun _ h => h.1))
  have hband : ∀ᶠ n in atTop, (m n : ℝ) ^ (8 / 9 + section3Margin γ) ≤ W n := by
    filter_upwards [eventually_all_mesoscopic_lengths_high_band W δ γ hδ hδγ hγ hW, hm]
      with n hn hmn
    exact hn (m n) hmn.2
  refine ⟨hM, taper_half_width_tendsto W hW, ?_⟩
  filter_upwards [eventually_taper_high_band_margin m W (section3Margin γ)
    (section3Margin_spec γ (hδ.trans hδγ) hγ).1 hM hW hband,
    eventually_mesoscopic_ring_band_fits W δ hδ hW, hm] with n hn hfit hmn
  exact ⟨hfit (m n) hmn.1, hn⟩

end CircularLawSections56.Section5
