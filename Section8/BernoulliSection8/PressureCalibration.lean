import BernoulliSection8.CellPressureLimit
import BernoulliSection8.HighBandTransport
import BernoulliSection10.CellDimensionLimit

/-!
# Calibration by the independent many-cell anchor

This module contains the deterministic last step of the calibration. The
probability comparison supplied to the bridge is discharged for the
actual Bernoulli matrices by the reset and terminal estimates.
-/

open Filter MeasureTheory
open scoped NNReal Topology

noncomputable section

namespace BernoulliSection8

open BernoulliSection10 BernoulliSection10.ProbabilityLimits
open BernoulliSection10.DiskReference

set_option backward.isDefEq.respectTransparency false

def normalizedCorePressure (μ : Measure ℝ) (C : ℝ≥0) (W : ℕ) (z : ℂ) : ℝ :=
  clippedMaxCorePressure μ (cellClipBound C W) W (coreSites W) z / cellLength W

def anchorPressureCenter (μ : Measure ℝ) (C : ℝ≥0) (W : ℕ) (z : ℂ) : ℝ :=
  (anchorCells W : ℝ) *
    clippedMaxCorePressure μ (cellClipBound C W) W (coreSites W) z / anchorSize W

def targetPressureCenter (μ : Measure ℝ) (C : ℝ≥0) (W m : ℕ) (z : ℂ) : ℝ :=
  (targetCells m W : ℝ) *
    clippedMaxCorePressure μ (cellClipBound C W) W (coreSites W) z /
      ((m : ℝ) * W)

theorem anchorPressureCenter_factor (μ : Measure ℝ) (C : ℝ≥0)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    anchorPressureCenter μ C W z =
      ((anchorCells W : ℝ) * cellLength W / anchorSize W) *
        normalizedCorePressure μ C W z := by
  have hL : (cellLength W : ℝ) ≠ 0 := by exact_mod_cast (cellLength_pos hW).ne'
  unfold anchorPressureCenter normalizedCorePressure
  field_simp <;> ring

theorem targetPressureCenter_factor (μ : Measure ℝ) (C : ℝ≥0)
    (W m : ℕ) (hW : 0 < W) (z : ℂ) :
    targetPressureCenter μ C W m z =
      ((targetCells m W : ℝ) * cellLength W / ((m : ℝ) * W)) *
        normalizedCorePressure μ C W z := by
  have hL : (cellLength W : ℝ) ≠ 0 := by exact_mod_cast (cellLength_pos hW).ne'
  unfold targetPressureCenter normalizedCorePressure
  field_simp <;> ring

theorem tendsto_anchor_dimension_ratio :
    Tendsto (fun W : ℕ => (anchorCells W : ℝ) * cellLength W / anchorSize W)
      atTop (𝓝 1) := by
  have hsites : Tendsto anchorSites atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_anchorCells
    intro W
    have hc := cellSites_pos W
    dsimp [anchorSites]
    nlinarith
  have hi : Tendsto (fun W : ℕ => 3 / (anchorSites W : ℝ)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun W => (anchorSites W : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hsites
    simpa only [div_eq_mul_inv, Function.comp_def, mul_zero] using
      (tendsto_inv_atTop_zero.comp hcast).const_mul (3 : ℝ)
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hi
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with W hW
  rw [anchor_dimension_ratio hW, anchorSize, Nat.cast_mul]
  have hw : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  field_simp <;> ring

theorem tendsto_target_dimension_ratio {W m : ℕ → ℕ}
    (hW : Tendsto W atTop atTop) (hm : ∀ᶠ n in atTop, 3 ≤ m n)
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ m n * W n) :
    Tendsto (fun n => (targetCells (m n) (W n) : ℝ) * cellLength (W n) /
      ((m n : ℝ) * W n)) atTop (𝓝 1) := by
  apply tendsto_densityCell_dimension_ratio hW hm
  filter_upwards [hW.eventually (eventually_gt_atTop 0), hlong] with n hn hl
  exact (rpow_le_anchorSize hn).trans (by exact_mod_cast hl)

/-- Internal calibration bridge: the normalization is the actual full
anchor dimension, including its final three sites. -/
theorem normalizedCorePressure_tendsto_of_anchor_comparison
    (hSource : Section3SubgaussianHighBandInput rademacherLaw 1)
    (C : ℝ≥0) (W : ℕ → ℕ) (hW : ∀ n, 0 < W n)
    (hWtop : Tendsto W atTop atTop) (z : ℂ)
    (hClose : TendstoInProbabilityTri
      (fun n => intervalRowsLaw (W n) (anchorSites (W n)) rademacherLaw)
      (fun n x => anchorLogPotential (W n) z x -
        anchorPressureCenter rademacherLaw C (W n) z) 0) :
    Tendsto (fun n => normalizedCorePressure rademacherLaw C (W n) z)
      atTop (𝓝 (circularLogPotential z)) := by
  have hcenter := deterministic_center_tendsto_of_tri_anchor_and_close
    (fun n => intervalRowsLaw (W n) (anchorSites (W n)) rademacherLaw)
    (fun n => anchorLogPotential (W n) z)
    (fun n => anchorPressureCenter rademacherLaw C (W n) z) (circularLogPotential z)
    (rademacher_anchor_log_potential hSource W hW hWtop z) hClose
  have hratio := tendsto_anchor_dimension_ratio.comp hWtop
  have h := hcenter.div hratio (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  convert h using 1
  funext n
  rw [anchorPressureCenter_factor _ _ _ (hW n)]
  have hK : (anchorCells (W n) : ℝ) ≠ 0 := by exact_mod_cast (anchorCells_pos (hW n)).ne'
  have hL : (cellLength (W n) : ℝ) ≠ 0 := by exact_mod_cast (cellLength_pos (hW n)).ne'
  have hM : (anchorSize (W n) : ℝ) ≠ 0 := by exact_mod_cast (anchorSize_pos (hW n)).ne'
  field_simp <;> ring

/-- The target normalization is filled by one on the unused direct
branch, so arbitrary alternation causes no subsequence premise. -/
def longBranchDimensionRatio (W m : ℕ) : ℝ :=
  if anchorSize W ≤ m * W then
    (targetCells m W : ℝ) * cellLength W / ((m : ℝ) * W)
  else 1

theorem tendsto_longBranchDimensionRatio (W m : ℕ → ℕ)
    (hW : Tendsto W atTop atTop) (hm : ∀ᶠ n in atTop, 3 ≤ m n) :
    Tendsto (fun n => longBranchDimensionRatio (W n) (m n)) atTop (𝓝 1) := by
  have hi : Tendsto (fun n => 2 * (1 / (W n : ℝ) ^ (1 / 200 : ℝ))) atTop (𝓝 0) := by
    have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp
      (tendsto_natCast_atTop_atTop.comp hW)
    simpa only [one_div, Function.comp_def, mul_zero] using
      (tendsto_inv_atTop_zero.comp hp).const_mul (2 : ℝ)
  have hd : Tendsto (fun n => 1 - longBranchDimensionRatio (W n) (m n)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hi
    · filter_upwards [hW.eventually (eventually_gt_atTop 0), hm] with n hn hmn
      unfold longBranchDimensionRatio
      split
      · exact (densityCell_dimension_defect_bounds hmn hn).1
      · simp
    · filter_upwards [hW.eventually (eventually_gt_atTop 0), hm] with n hn hmn
      unfold longBranchDimensionRatio
      split
      · exact (densityCell_dimension_defect_bounds hmn hn).2.trans
          (mul_le_mul_of_nonneg_left (cellLength_div_targetDimension_le hn ‹_›) (by norm_num))
      · simp only [sub_self]
        positivity
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hd
  simpa only [sub_sub_cancel, sub_zero] using h

/-- A deterministic center for all indices; on long indices this is
exactly `K_N Phi_W/N`. -/
def calibratedLongBranchCenter (μ : Measure ℝ) (C : ℝ≥0) (W m : ℕ) (z : ℂ) : ℝ :=
  longBranchDimensionRatio W m * normalizedCorePressure μ C W z

theorem calibratedLongBranchCenter_eq (μ : Measure ℝ) (C : ℝ≥0)
    (W m : ℕ) (hW : 0 < W) (z : ℂ) (hlong : anchorSize W ≤ m * W) :
    calibratedLongBranchCenter μ C W m z = targetPressureCenter μ C W m z := by
  rw [calibratedLongBranchCenter, longBranchDimensionRatio, if_pos hlong,
    targetPressureCenter_factor μ C W m hW z]

theorem calibratedLongBranchCenter_tendsto (μ : Measure ℝ) (C : ℝ≥0)
    (W m : ℕ → ℕ) (hW : Tendsto W atTop atTop) (hm : ∀ᶠ n in atTop, 3 ≤ m n)
    (z : ℂ) {u : ℝ}
    (hPressure : Tendsto (fun n => normalizedCorePressure μ C (W n) z) atTop (𝓝 u)) :
    Tendsto (fun n => calibratedLongBranchCenter μ C (W n) (m n) z) atTop (𝓝 u) := by
  simpa only [one_mul, calibratedLongBranchCenter] using
    (tendsto_longBranchDimensionRatio W m hW hm).mul hPressure

end BernoulliSection8
