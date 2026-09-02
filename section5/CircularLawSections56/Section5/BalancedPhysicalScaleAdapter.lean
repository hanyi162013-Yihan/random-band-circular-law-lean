import CircularLawSections56.Section5.BalancedDivision
import CircularLawSections56.Section5.LiteralPressureAsymptoticClosure

/-!
# Physical length ratios for balanced mesoscopic cells

After reserving `2W` rows, the balanced cells cover all but fewer than `q`
of the remaining rows.  This module derives the physical covered-length
ratio and transports an unnormalized terminal-row cost to the precise
normalized remainder rate consumed by the literal final assembly.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace CircularLawSections56.Section5

/-- Fraction of the physical ring covered by complete balanced cells after
reserving `2W` rows. -/
def balancedPhysicalLengthRatio (N W m0 : Nat) : Real :=
  ((balancedCellCount (N - 2 * W) m0 *
    balancedCellLength (N - 2 * W) m0 : Nat) : Real) / (N : Real)

/-- The balanced length is the full physical cell length.  Removing a
fresh block of width `b` leaves `ell = m - b`, and restoring that fresh
block recovers exactly `m`, not merely the outside length `ell`. -/
theorem balanced_physical_freshOutside_row_count
    (N W m0 b : Nat)
    (hb : b <= balancedCellLength (N - 2 * W) m0) :
    b + (balancedCellLength (N - 2 * W) m0 - b) =
        balancedCellLength (N - 2 * W) m0 ∧
    balancedCellCount (N - 2 * W) m0 *
        (b + (balancedCellLength (N - 2 * W) m0 - b)) =
      balancedCellCount (N - 2 * W) m0 *
        balancedCellLength (N - 2 * W) m0 := by
  have hLength := Nat.add_sub_of_le hb
  exact ⟨hLength, congrArg (fun k => balancedCellCount (N - 2 * W) m0 * k) hLength⟩

/-- Fitting the fresh width into the base scale automatically fits it into
the balanced full cell. -/
theorem balanced_physical_freshWidth_le_cellLength
    (N W m0 b : Nat) (hm0 : 0 < m0)
    (hFit : 2 * m0 <= N - 2 * W) (hb : b <= m0) :
    b <= balancedCellLength (N - 2 * W) m0 :=
  hb.trans (balanced_cell_division_spec (N - 2 * W) m0 hm0 hFit).2.1

/-- The physical covered ratio counts complete fresh-plus-outside cells.
This is the exact row-count interface of the literal `B * Q` telescope. -/
theorem balancedPhysicalLengthRatio_eq_freshOutside
    (N W m0 b : Nat)
    (hb : b <= balancedCellLength (N - 2 * W) m0) :
    balancedPhysicalLengthRatio N W m0 =
      ((balancedCellCount (N - 2 * W) m0 *
        (b + (balancedCellLength (N - 2 * W) m0 - b)) : Nat) : Real) / (N : Real) := by
  rw [(balanced_physical_freshOutside_row_count N W m0 b hb).2]
  rfl

/-- The normalized number of uncovered balanced terminal rows is at most
`1 / m0`.  This is the finite geometric input for every row-cost remainder. -/
theorem balanced_physical_remainder_div_le
    (N W m0 : Nat) (hW : 0 < W) (hm0 : 0 < m0)
    (hReserve : 2 * W <= N) (hFit : 2 * m0 <= N - 2 * W) :
    (balancedCellRemainder (N - 2 * W) m0 : Real) / (N : Real) <=
      1 / (m0 : Real) := by
  have hN : 0 < N := by omega
  have hq := balanced_cell_division_spec (N - 2 * W) m0 hm0 hFit
  have hRem : balancedCellRemainder (N - 2 * W) m0 <=
      balancedCellCount (N - 2 * W) m0 := hq.2.2.2.le
  have hCount : balancedCellCount (N - 2 * W) m0 * m0 <= N - 2 * W := by
    exact Nat.div_mul_le_self _ _
  have hRemMul : balancedCellRemainder (N - 2 * W) m0 * m0 <= N :=
    (Nat.mul_le_mul_right m0 hRem).trans (hCount.trans (Nat.sub_le _ _))
  apply (div_le_div_iff₀ (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hm0)).2
  simpa only [one_mul, Nat.cast_mul] using (Nat.cast_le.mpr hRemMul :
    ((balancedCellRemainder (N - 2 * W) m0 * m0 : Nat) : Real) <= (N : Real))

/-- Complete finite physical geometry: positive cell count, the base-cell
lower bound, and an explicit bound for the uncovered length fraction. -/
theorem balanced_physical_division_spec
    (N W m0 : Nat) (hW : 0 < W) (hm0 : 0 < m0)
    (hReserve : 2 * W <= N) (hFit : 2 * m0 <= N - 2 * W) :
    0 < balancedCellCount (N - 2 * W) m0 ∧
    m0 <= balancedCellLength (N - 2 * W) m0 ∧
    0 <= balancedPhysicalLengthRatio N W m0 ∧
    balancedPhysicalLengthRatio N W m0 <= 1 ∧
    |balancedPhysicalLengthRatio N W m0 - 1| <=
      (2 : Real) * (W : Real) / (N : Real) + 1 / (m0 : Real) := by
  have hN : 0 < N := by omega
  have hNr : 0 < (N : Real) := Nat.cast_pos.mpr hN
  have hSpec := balanced_cell_division_spec (N - 2 * W) m0 hm0 hFit
  have hParts := balanced_cells_add_remainder (N - 2 * W) m0
  have hCovered : balancedCellCount (N - 2 * W) m0 *
      balancedCellLength (N - 2 * W) m0 <= N := by omega
  have hRatio0 : 0 <= balancedPhysicalLengthRatio N W m0 :=
    div_nonneg (Nat.cast_nonneg _) hNr.le
  have hRatio1 : balancedPhysicalLengthRatio N W m0 <= 1 := by
    apply (div_le_one hNr).2
    exact Nat.cast_le.mpr hCovered
  have hPartsReal :
      ((balancedCellCount (N - 2 * W) m0 *
        balancedCellLength (N - 2 * W) m0 : Nat) : Real) +
      (balancedCellRemainder (N - 2 * W) m0 : Real) +
      (2 : Real) * (W : Real) = (N : Real) := by
    have hNat : balancedCellCount (N - 2 * W) m0 *
        balancedCellLength (N - 2 * W) m0 +
        balancedCellRemainder (N - 2 * W) m0 + 2 * W = N := by omega
    exact_mod_cast hNat
  have hFraction : balancedPhysicalLengthRatio N W m0 +
      (2 : Real) * (W : Real) / (N : Real) +
      (balancedCellRemainder (N - 2 * W) m0 : Real) / (N : Real) = 1 := by
    unfold balancedPhysicalLengthRatio
    rw [← add_div, ← add_div]
    apply (div_eq_iff hNr.ne').2
    linarith
  have hRemainder := balanced_physical_remainder_div_le N W m0 hW hm0 hReserve hFit
  refine ⟨hSpec.1, hSpec.2.1, hRatio0, hRatio1, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hRatio1)]
  linarith

/-- Positive integer bandwidth makes the paper logarithm at least one. -/
theorem one_le_paperLogEW_of_bandwidth_pos
    (W : Nat -> Nat) (n : Nat) (hW : 0 < W n) :
    1 <= paperLogEW W n := by
  have hWr : 0 < (W n : Real) := Nat.cast_pos.mpr hW
  have hWone : (1 : Real) <= (W n : Real) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hW)
  unfold paperLogEW
  rw [Real.log_mul (Real.exp_pos 1).ne' hWr.ne', Real.log_exp]
  linarith [Real.log_nonneg hWone]

/-- The finite covered-length bound is dominated by the exact asymptotic
envelope used in `PhysicalLiteralLongBranchInputTri`. -/
theorem balanced_physical_lengthRatio_error_le_paperRate
    (δ : Real) (W N : Nat -> Nat) (n : Nat)
    (hW : 0 < W n)
    (hm0 : 0 < paperMesoscopicCellLength δ W n)
    (hReserve : 2 * W n <= N n)
    (hFit : 2 * paperMesoscopicCellLength δ W n <= N n - 2 * W n) :
    |balancedPhysicalLengthRatio (N n) (W n) (paperMesoscopicCellLength δ W n) - 1| <=
      2 * paperFinalSeamRate W N n + paperBalancedRemainderRate δ W n := by
  have hNr : 0 <= (N n : Real) := Nat.cast_nonneg _
  have hWr : 0 <= (W n : Real) := Nat.cast_nonneg _
  have hLog := one_le_paperLogEW_of_bandwidth_pos W n hW
  have hLog0 : 0 <= paperLogEW W n := le_trans (by norm_num) hLog
  have hFinal : (W n : Real) / (N n : Real) <= paperFinalSeamRate W N n := by
    calc
      (W n : Real) / (N n : Real) <=
          ((W n : Real) * paperLogEW W n) / (N n : Real) :=
        div_le_div_of_nonneg_right (by nlinarith) hNr
      _ <= paperFinalSeamRate W N n :=
        le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _) hLog0)
  have hRem : 1 / (paperMesoscopicCellLength δ W n : Real) <=
      paperBalancedRemainderRate δ W n :=
    div_le_div_of_nonneg_right hLog (Nat.cast_nonneg _)
  have hFinite := (balanced_physical_division_spec
    (N n) (W n) (paperMesoscopicCellLength δ W n) hW hm0 hReserve hFit).2.2.2.2
  calc
    _ <= (2 : Real) * (W n : Real) / (N n : Real) +
        1 / (paperMesoscopicCellLength δ W n : Real) := hFinite
    _ = 2 * ((W n : Real) / (N n : Real)) +
        1 / (paperMesoscopicCellLength δ W n : Real) := by ring
    _ <= 2 * paperFinalSeamRate W N n + paperBalancedRemainderRate δ W n := by
      linarith

/-- Normalizing a genuine terminal-row pressure cost gives the balanced
remainder rate.  The analytical row-cost estimate itself remains the sole
premise, and no inverse-row statement is silently assumed. -/
theorem balanced_physical_normalized_remainder_le
    (N W m0 : Nat) (hW : 0 < W) (hm0 : 0 < m0)
    (hReserve : 2 * W <= N) (hFit : 2 * m0 <= N - 2 * W)
    (Ps Pcells C logEW : Real) (hC : 0 <= C) (hLog : 0 <= logEW)
    (hCost : |Ps - Pcells| <=
      (balancedCellRemainder (N - 2 * W) m0 : Real) * C * logEW) :
    |Ps / (N : Real) - Pcells / (N : Real)| <= C * (logEW / (m0 : Real)) := by
  have hN : 0 < N := by omega
  have hNr : 0 < (N : Real) := Nat.cast_pos.mpr hN
  have hRem := balanced_physical_remainder_div_le N W m0 hW hm0 hReserve hFit
  rw [← sub_div, abs_div, abs_of_pos hNr]
  calc
    |Ps - Pcells| / (N : Real) <=
        ((balancedCellRemainder (N - 2 * W) m0 : Real) * C * logEW) / (N : Real) :=
      div_le_div_of_nonneg_right hCost hNr.le
    _ = ((balancedCellRemainder (N - 2 * W) m0 : Real) / (N : Real)) *
        (C * logEW) := by ring
    _ <= (1 / (m0 : Real)) * (C * logEW) :=
      mul_le_mul_of_nonneg_right hRem (mul_nonneg hC hLog)
    _ = C * (logEW / (m0 : Real)) := by ring

/-- Multiplying the complete-cell normalized pressure by the physical
length ratio is exactly normalization by the full ring length. -/
theorem balancedPhysicalLengthRatio_mul_normalized
    (N W m0 : Nat) (hm0 : 0 < m0) (hFit : 2 * m0 <= N - 2 * W)
    (Pcells : Real) :
    balancedPhysicalLengthRatio N W m0 *
      (Pcells / (((balancedCellCount (N - 2 * W) m0 *
        balancedCellLength (N - 2 * W) m0 : Nat) : Real))) =
      Pcells / (N : Real) := by
  have hSpec := balanced_cell_division_spec (N - 2 * W) m0 hm0 hFit
  have hCoveredPos : 0 < balancedCellCount (N - 2 * W) m0 *
      balancedCellLength (N - 2 * W) m0 :=
    Nat.mul_pos hSpec.1 (lt_of_lt_of_le hm0 hSpec.2.1)
  have hCoveredNe : (((balancedCellCount (N - 2 * W) m0 *
      balancedCellLength (N - 2 * W) m0 : Nat) : Real)) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hCoveredPos)
  let covered : Real := ((balancedCellCount (N - 2 * W) m0 *
    balancedCellLength (N - 2 * W) m0 : Nat) : Real)
  change covered / (N : Real) * (Pcells / covered) = Pcells / (N : Real)
  change covered ≠ 0 at hCoveredNe
  simp only [div_eq_mul_inv]
  calc
    covered * (N : Real)⁻¹ * (Pcells * covered⁻¹) =
        (covered * covered⁻¹) * (Pcells * (N : Real)⁻¹) := by ring
    _ = Pcells * (N : Real)⁻¹ := by rw [mul_inv_cancel₀ hCoveredNe, one_mul]

/-- The preceding normalization cancellation with the literal telescope's
row count `q * (b + ell)`, where `ell = m - b`.  The outside baseline keeps
length `ell`, while the complete product is normalized by full cell length
`m`; the two lengths are never identified. -/
theorem balancedPhysicalLengthRatio_mul_freshOutside_normalized
    (N W m0 b : Nat) (hm0 : 0 < m0)
    (hFit : 2 * m0 <= N - 2 * W)
    (hb : b <= balancedCellLength (N - 2 * W) m0) (Pcells : Real) :
    balancedPhysicalLengthRatio N W m0 *
      (Pcells / (((balancedCellCount (N - 2 * W) m0 *
        (b + (balancedCellLength (N - 2 * W) m0 - b)) : Nat) : Real))) =
      Pcells / (N : Real) := by
  rw [(balanced_physical_freshOutside_row_count N W m0 b hb).2]
  exact balancedPhysicalLengthRatio_mul_normalized N W m0 hm0 hFit Pcells

/-- Exact paper-rate receiver form, including the covered-length ratio
multiplying the normalized complete-cell pressure. -/
theorem balanced_physical_normalized_remainder_le_paperRate
    (δ : Real) (W N : Nat -> Nat) (n : Nat)
    (hW : 0 < W n) (hm0 : 0 < paperMesoscopicCellLength δ W n)
    (hReserve : 2 * W n <= N n)
    (hFit : 2 * paperMesoscopicCellLength δ W n <= N n - 2 * W n)
    (Ps Pcells C : Real) (hC : 0 <= C)
    (hCost : |Ps - Pcells| <=
      (balancedCellRemainder (N n - 2 * W n) (paperMesoscopicCellLength δ W n) : Real) *
        C * paperLogEW W n) :
    |Ps / (N n : Real) -
      balancedPhysicalLengthRatio (N n) (W n) (paperMesoscopicCellLength δ W n) *
      (Pcells / (((balancedCellCount (N n - 2 * W n) (paperMesoscopicCellLength δ W n) *
        balancedCellLength (N n - 2 * W n) (paperMesoscopicCellLength δ W n) : Nat) : Real)))| <=
      C * paperBalancedRemainderRate δ W n := by
  rw [balancedPhysicalLengthRatio_mul_normalized (N n) (W n)
    (paperMesoscopicCellLength δ W n) hm0 hFit Pcells]
  exact balanced_physical_normalized_remainder_le (N n) (W n)
    (paperMesoscopicCellLength δ W n) hW hm0 hReserve hFit Ps Pcells C
    (paperLogEW W n) hC
    (le_trans (by norm_num) (one_le_paperLogEW_of_bandwidth_pos W n hW)) hCost

end CircularLawSections56.Section5
