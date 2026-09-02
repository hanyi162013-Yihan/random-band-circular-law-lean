import CircularLawSections56.Section5.PaperLiteralGeometry

/-! # The actual balanced cell count diverges in the long regime

The conditional eventual bound also handles infinitely interlaced short and
long branches: no claim of global divergence is made for the short branch.
-/

open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace CircularLawSections56.Section5

theorem eventually_paperBandCellCount_ge_on_long
    (W : ℕ → ℕ) (δ γ : ℝ) (hδ : 0 < δ) (hδγ : δ < γ)
    (hW : Tendsto W atTop atTop) (b : ℕ) :
    ∀ᶠ n in atTop, (W n : ℝ) ^ (1 + γ) < (n + 1 : ℝ) → b ≤ paperBandCellCount W δ n := by
  have hWr : Tendsto (fun n => (W n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hW
  have hδr := ((tendsto_rpow_atTop hδ).comp hWr).eventually_ge_atTop 2
  have hgap := ((tendsto_rpow_atTop (sub_pos.2 hδγ)).comp hWr).eventually_ge_atTop
    (2 * (b : ℝ) + 2)
  filter_upwards [hWr.eventually_ge_atTop 1, hδr, hgap] with n hw1 hδn hgapn hlong
  change 2 ≤ (W n : ℝ) ^ δ at hδn
  change 2 * (b : ℝ) + 2 ≤ (W n : ℝ) ^ (γ - δ) at hgapn
  have hw : 0 < (W n : ℝ) := by linarith
  let P := (W n : ℝ) ^ (1 + δ)
  have hPpos : 0 < P := Real.rpow_pos_of_pos hw _
  have hP : P = (W n : ℝ) * (W n : ℝ) ^ δ := by
    dsimp only [P]
    rw [Real.rpow_add hw, Real.rpow_one]
  have hlarge : (W n : ℝ) ^ (1 + γ) = P * (W n : ℝ) ^ (γ - δ) := by
    dsimp only [P]
    rw [← Real.rpow_add hw]
    congr 1
    ring
  have hwidth : 2 * (W n : ℝ) ≤ P := by
    rw [hP]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hδn hw.le
  have hceil : P ≤ (paperMesoscopicCellLength δ W n : ℝ) := Nat.le_ceil P
  have hceilUpper : (paperMesoscopicCellLength δ W n : ℝ) < P + 1 :=
    Nat.ceil_lt_add_one hPpos.le
  have hm : (paperMesoscopicCellLength δ W n : ℝ) ≤ 2 * P := by linarith
  have hb := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg b)
  have hbound : (2 * (b : ℝ) + 2) * P ≤ (W n : ℝ) ^ (1 + γ) := by
    rw [hlarge]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hgapn hPpos.le
  have hfitReal : (b : ℝ) * (paperMesoscopicCellLength δ W n : ℝ) + 2 * (W n : ℝ) ≤ n + 1 := by
    nlinarith only [hb, hbound, hlong, hwidth, hPpos]
  have hfitNat : b * paperMesoscopicCellLength δ W n + 2 * W n ≤ n + 1 := by
    exact_mod_cast hfitReal
  have hmpos : 0 < paperMesoscopicCellLength δ W n :=
    Nat.cast_pos.1 (hPpos.trans_le hceil)
  change b ≤ (n + 1 - 2 * W n) / paperMesoscopicCellLength δ W n
  apply (Nat.le_div_iff_mul_le hmpos).2
  omega

theorem paperBandCellCount_tendsto_of_eventually_long
    (W : ℕ → ℕ) (δ γ : ℝ) (hδ : 0 < δ) (hδγ : δ < γ)
    (hW : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, (W n : ℝ) ^ (1 + γ) < (n + 1 : ℝ)) :
    Tendsto (paperBandCellCount W δ) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_paperBandCellCount_ge_on_long W δ γ hδ hδγ hW b, hlong]
    with n hn hln
  exact hn hln

end CircularLawSections56.Section5
