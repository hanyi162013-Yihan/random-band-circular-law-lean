import BernoulliSection10.AsymptoticScales
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exact mesoscopic scales for the discrete full-block branch

These are the literal scales in (8.23)--(8.24), not the single-cell
anchor used in Section 10. The Section 8 anchor contains a growing number
of complete cells followed by three terminal sites. All rounding and
high-band conclusions below are proved from these definitions.
-/

open Filter
open scoped Topology

noncomputable section

namespace BernoulliSection8

/-- Core block sites, `s_W` in (8.23). -/
def coreSites (W : ℕ) : ℕ := ⌈(W : ℝ) ^ (1 / 200 : ℝ)⌉₊

/-- Complete cell: three reset sites followed by the core. -/
def cellSites (W : ℕ) : ℕ := coreSites W + 3

/-- Scalar length `ell_W` of a complete cell. -/
def cellLength (W : ℕ) : ℕ := cellSites W * W

/-- Growing number `K_W` of complete cells in the independent anchor. -/
def anchorCells (W : ℕ) : ℕ := coreSites W

/-- Independent anchor block sites, including the terminal packet. -/
def anchorSites (W : ℕ) : ℕ := anchorCells W * cellSites W + 3

/-- Scalar anchor dimension `M_W` in (8.24). -/
def anchorSize (W : ℕ) : ℕ := W * anchorSites W

/-- Complete cells in a target after reserving its terminal packet. -/
def targetCells (m W : ℕ) : ℕ := (m - 3) / cellSites W

/-- Incomplete sites after the complete cells, before the terminal packet. -/
def remainderSites (m W : ℕ) : ℕ := (m - 3) % cellSites W

theorem coreSites_pos {W : ℕ} (hW : 0 < W) : 0 < coreSites W :=
  BernoulliSection10.densityCoreSites_pos hW

theorem cellSites_pos (W : ℕ) : 0 < cellSites W := by simp [cellSites]

theorem cellLength_pos {W : ℕ} (hW : 0 < W) : 0 < cellLength W :=
  Nat.mul_pos (cellSites_pos W) hW

theorem anchorCells_pos {W : ℕ} (hW : 0 < W) : 0 < anchorCells W :=
  coreSites_pos hW

theorem anchorSites_pos (W : ℕ) : 0 < anchorSites W := by simp [anchorSites]

theorem anchorSize_pos {W : ℕ} (hW : 0 < W) : 0 < anchorSize W :=
  Nat.mul_pos hW (anchorSites_pos W)

theorem four_le_anchorSites {W : ℕ} (hW : 0 < W) : 4 ≤ anchorSites W := by
  have hprod := Nat.mul_pos (anchorCells_pos hW) (cellSites_pos W)
  unfold anchorSites
  omega

theorem anchorSize_eq (W : ℕ) :
    anchorSize W = anchorCells W * cellLength W + 3 * W := by
  unfold anchorSize anchorSites cellLength
  ring

theorem remainderSites_lt (m W : ℕ) : remainderSites m W < cellSites W :=
  Nat.mod_lt _ (cellSites_pos W)

theorem remainderSites_eq_sub (m W : ℕ) :
    remainderSites m W = m - 3 - targetCells m W * cellSites W :=
  Nat.mod_eq_sub_div_mul

theorem target_partition {m : ℕ} (hm : 3 ≤ m) (W : ℕ) :
    targetCells m W * cellSites W + remainderSites m W + 3 = m :=
  BernoulliSection10.densityCell_partition hm W

theorem target_scalar_partition {m : ℕ} (hm : 3 ≤ m) (W : ℕ) :
    targetCells m W * cellLength W + (remainderSites m W + 3) * W = m * W := by
  have h := congrArg (fun t : ℕ => t * W) (target_partition hm W)
  simpa only [cellLength, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc] using h

/-- The exact long-branch hypothesis gives the stronger `K_N >= K_W`,
and therefore implies the paper's `K_N >= K_W - 1` in (8.64). -/
theorem anchorCells_le_targetCells {m W : ℕ} (hW : 0 < W)
    (hlong : anchorSize W ≤ m * W) : anchorCells W ≤ targetCells m W := by
  have hsites : anchorSites W ≤ m := by
    apply le_of_mul_le_mul_right (a := W) _ hW
    simpa only [anchorSize, Nat.mul_comm] using hlong
  apply (Nat.le_div_iff_mul_le (cellSites_pos W)).2
  unfold anchorSites at hsites
  omega

theorem target_dimension_ratio {m W : ℕ} (hm : 3 ≤ m) (hW : 0 < W) :
    (targetCells m W : ℝ) * cellLength W / ((m : ℝ) * W) =
      1 - (3 + (remainderSites m W : ℝ)) / m :=
  BernoulliSection10.densityCell_dimension_ratio hm hW

theorem anchor_dimension_ratio {W : ℕ} (hW : 0 < W) :
    (anchorCells W : ℝ) * cellLength W / anchorSize W =
      1 - 3 * (W : ℝ) / anchorSize W := by
  have hM : (anchorSize W : ℝ) ≠ 0 := by exact_mod_cast (anchorSize_pos hW).ne'
  have hid : (anchorSize W : ℝ) =
      (anchorCells W : ℝ) * cellLength W + 3 * (W : ℝ) := by
    exact_mod_cast anchorSize_eq W
  field_simp
  linarith

theorem rpow_le_coreSites (W : ℕ) :
    (W : ℝ) ^ (1 / 200 : ℝ) ≤ coreSites W := Nat.le_ceil _

theorem coreSites_le_two_mul_rpow {W : ℕ} (hW : 0 < W) :
    (coreSites W : ℝ) ≤ 2 * (W : ℝ) ^ (1 / 200 : ℝ) := by
  have hr := Real.one_le_rpow (by exact_mod_cast hW : (1 : ℝ) ≤ W)
    (by norm_num : (0 : ℝ) ≤ 1 / 200)
  have hc := Nat.ceil_lt_add_one
    (Real.rpow_nonneg (Nat.cast_nonneg W) (1 / 200 : ℝ))
  dsimp [coreSites]
  linarith

theorem rpow_le_cellSites (W : ℕ) :
    (W : ℝ) ^ (1 / 200 : ℝ) ≤ cellSites W :=
  BernoulliSection10.rpow_le_densityCellSites W

theorem cellSites_le_five_mul_rpow {W : ℕ} (hW : 0 < W) :
    (cellSites W : ℝ) ≤ 5 * (W : ℝ) ^ (1 / 200 : ℝ) :=
  BernoulliSection10.densityCellSites_le_five_mul_rpow hW

theorem rpow_le_cellLength {W : ℕ} (hW : 0 < W) :
    (W : ℝ) ^ (201 / 200 : ℝ) ≤ cellLength W :=
  BernoulliSection10.rpow_le_densityAnchorSize hW

theorem cellLength_le_five_mul_rpow {W : ℕ} (hW : 0 < W) :
    (cellLength W : ℝ) ≤ 5 * (W : ℝ) ^ (201 / 200 : ℝ) :=
  BernoulliSection10.densityAnchorSize_le_five_mul_rpow hW

theorem rpow_fullAnchor_exponent {W : ℕ} (hW : 0 < W) :
    (W : ℝ) ^ (101 / 100 : ℝ) =
      ((W : ℝ) ^ (1 / 200 : ℝ)) ^ 2 * W := by
  rw [← Real.rpow_mul_natCast (by positivity)]
  norm_num
  rw [show (101 / 100 : ℝ) = 1 / 100 + 1 by norm_num,
    Real.rpow_add_one (by exact_mod_cast Nat.ne_of_gt hW)]

theorem rpow_sq_le_anchorSites (W : ℕ) :
    ((W : ℝ) ^ (1 / 200 : ℝ)) ^ 2 ≤ anchorSites W := by
  have hprod := mul_le_mul (rpow_le_coreSites W) (rpow_le_cellSites W)
    (Real.rpow_nonneg (by positivity) _) (by positivity : 0 ≤ (coreSites W : ℝ))
  simp only [anchorSites, anchorCells, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

theorem anchorSites_le_thirteen_mul_rpow_sq {W : ℕ} (hW : 0 < W) :
    (anchorSites W : ℝ) ≤ 13 * ((W : ℝ) ^ (1 / 200 : ℝ)) ^ 2 := by
  have hr := Real.one_le_rpow (by exact_mod_cast hW : (1 : ℝ) ≤ W)
    (by norm_num : (0 : ℝ) ≤ 1 / 200)
  have hprod := mul_le_mul (coreSites_le_two_mul_rpow hW)
    (cellSites_le_five_mul_rpow hW) (by positivity : 0 ≤ (cellSites W : ℝ))
    (by positivity : 0 ≤ 2 * (W : ℝ) ^ (1 / 200 : ℝ))
  simp only [anchorSites, anchorCells, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

theorem rpow_le_anchorSize {W : ℕ} (hW : 0 < W) :
    (W : ℝ) ^ (101 / 100 : ℝ) ≤ anchorSize W := by
  rw [rpow_fullAnchor_exponent hW, anchorSize, Nat.cast_mul, mul_comm (W : ℝ)]
  exact mul_le_mul_of_nonneg_right (rpow_sq_le_anchorSites W) (by positivity)

theorem anchorSize_le_thirteen_mul_rpow {W : ℕ} (hW : 0 < W) :
    (anchorSize W : ℝ) ≤ 13 * (W : ℝ) ^ (101 / 100 : ℝ) := by
  rw [anchorSize, Nat.cast_mul, rpow_fullAnchor_exponent hW,
    mul_comm (W : ℝ), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (anchorSites_le_thirteen_mul_rpow_sq hW)
    (by positivity)

theorem width_div_cellLength_le {W : ℕ} (hW : 0 < W) :
    (W : ℝ) / cellLength W ≤ 1 / (W : ℝ) ^ (1 / 200 : ℝ) := by
  have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  calc
    (W : ℝ) / cellLength W = 1 / (cellSites W : ℝ) := by
      rw [cellLength, Nat.cast_mul]
      field_simp
    _ ≤ 1 / (W : ℝ) ^ (1 / 200 : ℝ) :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hW) _)
        (rpow_le_cellSites W)

theorem cellLength_div_anchorSize_le {W : ℕ} (hW : 0 < W) :
    (cellLength W : ℝ) / anchorSize W ≤ 1 / (W : ℝ) ^ (1 / 200 : ℝ) := by
  apply (div_le_div_iff₀ (by exact_mod_cast anchorSize_pos hW)
    (Real.rpow_pos_of_pos (by exact_mod_cast hW) _)).2
  have hprod := mul_le_mul_of_nonneg_right (rpow_le_coreSites W)
    (by positivity : 0 ≤ (cellLength W : ℝ))
  have hid : (anchorSize W : ℝ) =
      (coreSites W : ℝ) * cellLength W + 3 * (W : ℝ) := by
    exact_mod_cast anchorSize_eq W
  nlinarith

theorem cellLength_div_targetDimension_le {m W : ℕ} (hW : 0 < W)
    (hlong : anchorSize W ≤ m * W) :
    (cellLength W : ℝ) / ((m : ℝ) * W) ≤ 1 / (W : ℝ) ^ (1 / 200 : ℝ) := by
  apply le_trans _ (cellLength_div_anchorSize_le hW)
  apply div_le_div_of_nonneg_left (by positivity)
    (by exact_mod_cast anchorSize_pos hW)
  exact_mod_cast hlong

/-- A reusable scalar limit for all powers of the logarithm occurring in
the reset and concentration errors. -/
theorem tendsto_log_rpow_div_width_rpow (r : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun W : ℕ => (Real.log W) ^ r / (W : ℝ) ^ a) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop r ha).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop

theorem tendsto_coreOverhead :
    Tendsto (fun W : ℕ => (W : ℝ) * Real.log W / cellLength W)
      atTop (𝓝 0) := by
  apply squeeze_zero' _ _
    (tendsto_log_rpow_div_width_rpow 1 (by norm_num : (0 : ℝ) < 1 / 200))
  · filter_upwards [eventually_ge_atTop 1] with W hW
    exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hW)))
      (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with W hW
    have h := mul_le_mul_of_nonneg_right (width_div_cellLength_le hW)
      (Real.log_nonneg (by exact_mod_cast hW : (1 : ℝ) ≤ W))
    simpa only [Real.rpow_one, div_mul_eq_mul_div, one_mul, mul_div_assoc,
      Function.comp_def] using h

theorem tendsto_remainderOverhead {m W : ℕ → ℕ} (hW : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ m n * W n) :
    Tendsto (fun n => (cellLength (W n) : ℝ) * Real.log (W n) /
      ((m n : ℝ) * W n)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _
    ((tendsto_log_rpow_div_width_rpow 1 (by norm_num : (0 : ℝ) < 1 / 200)).comp hW)
  · filter_upwards [hW.eventually (eventually_ge_atTop 1)] with n hn
    exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hn)))
      (by positivity)
  · filter_upwards [hW.eventually (eventually_gt_atTop 0), hlong] with n hn hlongn
    have h := mul_le_mul_of_nonneg_right (cellLength_div_targetDimension_le hn hlongn)
      (Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ) ≤ W n))
    simpa only [Real.rpow_one, div_mul_eq_mul_div, one_mul, mul_div_assoc,
      Function.comp_def] using h

theorem width_rpow_le_sqrt_coreSites (W : ℕ) :
    (W : ℝ) ^ (1 / 400 : ℝ) ≤ Real.sqrt (coreSites W) := by
  calc
    (W : ℝ) ^ (1 / 400 : ℝ) =
        ((W : ℝ) ^ (1 / 200 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_mul (by positivity)]
      norm_num
    _ ≤ (coreSites W : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (rpow_le_coreSites W) (by norm_num)
    _ = Real.sqrt (coreSites W) := (Real.sqrt_eq_rpow _).symm

/-- The logarithmic degree union bound is harmless for the actual anchor
and for every longer target, because their cell counts are at least `K_W`.
Merely assuming `K -> infinity` would not suffice for this conclusion. -/
theorem tendsto_cellConcentrationOverhead {W K : ℕ → ℕ}
    (hW : Tendsto W atTop atTop)
    (hK : ∀ᶠ n in atTop, coreSites (W n) ≤ K n) :
    Tendsto (fun n => (Real.log (W n)) ^ (3 / 2 : ℝ) / Real.sqrt (K n))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) _
    ((tendsto_log_rpow_div_width_rpow (3 / 2)
      (by norm_num : (0 : ℝ) < 1 / 400)).comp hW)
  filter_upwards [hW.eventually (eventually_gt_atTop 0), hK] with n hn hKn
  have hden : (W n : ℝ) ^ (1 / 400 : ℝ) ≤ Real.sqrt (K n) :=
    (width_rpow_le_sqrt_coreSites (W n)).trans (Real.sqrt_le_sqrt (by exact_mod_cast hKn))
  exact div_le_div_of_nonneg_left (by positivity)
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) _) hden

theorem tendsto_coreSites : Tendsto coreSites atTop atTop :=
  tendsto_nat_ceil_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp
      tendsto_natCast_atTop_atTop)

theorem tendsto_anchorCells : Tendsto anchorCells atTop atTop := tendsto_coreSites

theorem tendsto_targetCells {m W : ℕ → ℕ} (hW : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ m n * W n) :
    Tendsto (fun n => targetCells (m n) (W n)) atTop atTop := by
  apply tendsto_atTop_mono' _ _ (tendsto_anchorCells.comp hW)
  filter_upwards [hW.eventually (eventually_gt_atTop 0), hlong] with n hn hlongn
  exact anchorCells_le_targetCells hn hlongn

/-- The full independent anchor, including all `K_W` cells, satisfies
the precise high-band exponent used by Proposition 3.8. -/
theorem eventually_anchor_highBand :
    ∀ᶠ W : ℕ in atTop, (anchorSize W : ℝ) ^ (8 / 9 + 1 / 20 : ℝ) ≤ W := by
  have hδ : (0 : ℝ) < 1 - (101 / 100) * (8 / 9 + 1 / 20) := by norm_num
  have ht : Tendsto (fun W : ℕ =>
      (W : ℝ) ^ (1 - (101 / 100) * (8 / 9 + 1 / 20) : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    ht.eventually (eventually_ge_atTop ((13 : ℝ) ^ (8 / 9 + 1 / 20 : ℝ)))] with W hW h13
  calc
    (anchorSize W : ℝ) ^ (8 / 9 + 1 / 20 : ℝ) ≤
        (13 * (W : ℝ) ^ (101 / 100 : ℝ)) ^ (8 / 9 + 1 / 20 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (anchorSize_le_thirteen_mul_rpow hW) (by norm_num)
    _ = (13 : ℝ) ^ (8 / 9 + 1 / 20 : ℝ) *
        (W : ℝ) ^ ((101 / 100) * (8 / 9 + 1 / 20) : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity)]
    _ ≤ (W : ℝ) ^ (1 - (101 / 100) * (8 / 9 + 1 / 20) : ℝ) *
        (W : ℝ) ^ ((101 / 100) * (8 / 9 + 1 / 20) : ℝ) :=
      mul_le_mul_of_nonneg_right h13 (by positivity)
    _ = W := by
      rw [← Real.rpow_add (by exact_mod_cast hW)]
      norm_num

/-- The direct branch can alternate with the long branch: this bound is
eventual in width and uniform over every target below that width's anchor. -/
theorem eventually_direct_highBand :
    ∀ᶠ W : ℕ in atTop, ∀ N : ℕ, N < anchorSize W →
      (N : ℝ) ^ (8 / 9 + 1 / 20 : ℝ) ≤ W := by
  filter_upwards [eventually_anchor_highBand] with W hW N hN
  exact (Real.rpow_le_rpow (by positivity)
    (by exact_mod_cast hN.le : (N : ℝ) ≤ anchorSize W) (by norm_num)).trans hW

end BernoulliSection8
