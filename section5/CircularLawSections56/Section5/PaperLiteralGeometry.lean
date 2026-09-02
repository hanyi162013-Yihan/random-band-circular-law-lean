import CircularLawSections56.Section5.BalancedPhysicalScaleAdapter
import CircularLawSections56.Section5.LiteralNearEndToEndAssembly
import CircularLawSections56.Section5.PaperMesoscopicScaleLimits

/-! # Automatic literal mesoscopic geometry, including finite-prefix fillers

The canonical cell count and length are the actual balanced quotients. The safe
branch differs from the manuscript branch only at finitely many indices; every
active index has all finite geometry needed by the literal Section 5 endpoint.
-/

open Filter Topology

noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5

def paperBandCellCount (W : ℕ → ℕ) (δ : ℝ) (n : ℕ) : ℕ :=
  balancedCellCount (n + 1 - 2 * W n) (paperMesoscopicCellLength δ W n)

def paperBandCellLength (W : ℕ → ℕ) (δ : ℝ) (n : ℕ) : ℕ :=
  balancedCellLength (n + 1 - 2 * W n) (paperMesoscopicCellLength δ W n)

def paperTransferReady (W : ℕ → ℕ) (δ : ℝ) (n : ℕ) : Prop :=
  0 < W n ∧ 2 * W n ≤ paperMesoscopicCellLength δ W n ∧
    2 * paperMesoscopicCellLength δ W n ≤ n + 1 - 2 * W n

def paperNaturalShortBranch (W : ℕ → ℕ) (γ : ℝ) (n : ℕ) : Bool := by
  classical
  exact decide ((n + 1 : ℝ) ≤ (W n : ℝ) ^ (1 + γ))

def paperSafeShortBranch (W : ℕ → ℕ) (δ γ : ℝ) (n : ℕ) : Bool := by
  classical
  exact decide ((n + 1 : ℝ) ≤ (W n : ℝ) ^ (1 + γ) ∨ ¬paperTransferReady W δ n)

theorem paperSafeShortBranch_active (W : ℕ → ℕ) (δ γ : ℝ) (n : ℕ)
    (h : literalLongActive (paperSafeShortBranch W δ γ) n = true) :
    (W n : ℝ) ^ (1 + γ) < (n + 1 : ℝ) ∧ paperTransferReady W δ n := by
  classical
  have hn : ¬((n + 1 : ℝ) ≤ (W n : ℝ) ^ (1 + γ) ∨ ¬paperTransferReady W δ n) := by
    intro hn
    simp [literalLongActive, paperSafeShortBranch, hn] at h
  exact ⟨lt_of_not_ge (fun he => hn (.inl he)), by
    by_contra hr
    exact hn (.inr hr)⟩

theorem paperTransferReady_geometry (W : ℕ → ℕ) (δ : ℝ) (n : ℕ)
    (h : paperTransferReady W δ n) :
    0 < paperMesoscopicCellLength δ W n ∧
      2 * W n + 1 ≤ n + 1 ∧
      0 < paperBandCellCount W δ n ∧
      paperMesoscopicCellLength δ W n ≤ paperBandCellLength W δ n ∧
      2 * W n ≤ paperBandCellLength W δ n ∧
      paperBandCellLength W δ n ≤ n + 1 := by
  obtain ⟨hW, hWidth, hFit⟩ := h
  have hm : 0 < paperMesoscopicCellLength δ W n := by omega
  have hs := balanced_cell_division_spec (n + 1 - 2 * W n)
    (paperMesoscopicCellLength δ W n) hm hFit
  refine ⟨hm, by omega, hs.1, hs.2.1, hWidth.trans hs.2.1, ?_⟩
  exact hs.2.2.1.le.trans (hFit.trans (Nat.sub_le _ _))

/-- The long-branch power separation automatically supplies the finite fit
conditions. No large-index geometry is an independent hypothesis. -/
theorem eventually_paperTransferReady_on_long
    (W : ℕ → ℕ) (δ γ : ℝ) (hδ : 0 < δ) (hδγ : δ < γ)
    (hW : Tendsto W atTop atTop) :
    ∀ᶠ n in atTop, (W n : ℝ) ^ (1 + γ) < (n + 1 : ℝ) → paperTransferReady W δ n := by
  have hWr : Tendsto (fun n => (W n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hW
  have hδr := ((tendsto_rpow_atTop hδ).comp hWr).eventually_ge_atTop 2
  have hgap := ((tendsto_rpow_atTop (sub_pos.2 hδγ)).comp hWr).eventually_ge_atTop 8
  filter_upwards [hWr.eventually_ge_atTop 1, hδr, hgap] with n hw1 hδn hgapn hlong
  change 2 ≤ (W n : ℝ) ^ δ at hδn
  change 8 ≤ (W n : ℝ) ^ (γ - δ) at hgapn
  have hw : (0 : ℝ) < W n := by linarith
  have hWn : 0 < W n := Nat.cast_pos.1 hw
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
  have hbound : 8 * P ≤ (W n : ℝ) ^ (1 + γ) := by
    rw [hlarge]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hgapn hPpos.le
  have hfitReal : 2 * (paperMesoscopicCellLength δ W n : ℝ) + 2 * (W n : ℝ) ≤ n + 1 := by
    linarith
  have hfitNat : 2 * paperMesoscopicCellLength δ W n + 2 * W n ≤ n + 1 := by
    exact_mod_cast hfitReal
  refine ⟨hWn, ?_, by omega⟩
  exact_mod_cast hwidth.trans hceil

/-- The safety filler never changes the eventual short/long split. -/
theorem paperSafeShortBranch_eventually_eq_natural
    (W : ℕ → ℕ) (δ γ : ℝ) (hδ : 0 < δ) (hδγ : δ < γ)
    (hW : Tendsto W atTop atTop) :
    paperSafeShortBranch W δ γ =ᶠ[atTop] paperNaturalShortBranch W γ := by
  classical
  filter_upwards [eventually_paperTransferReady_on_long W δ γ hδ hδγ hW] with n hn
  by_cases hs : (n + 1 : ℝ) ≤ (W n : ℝ) ^ (1 + γ)
  · simp [paperSafeShortBranch, paperNaturalShortBranch, hs]
  · have hr := hn (lt_of_not_ge hs)
    simp [paperSafeShortBranch, paperNaturalShortBranch, hs, hr]

end CircularLawSections56.Section5
