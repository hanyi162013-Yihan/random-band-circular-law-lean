import BernoulliSection8.PressureCalibration
import SubgaussianSection8.HighBandTransport
noncomputable section
open Filter MeasureTheory
open scoped NNReal Topology
namespace SubgaussianSection8
open BernoulliSection8 BernoulliSection10 BernoulliSection10.ProbabilityLimits
open BernoulliSection10.DiskReference ShortRingAnchor
set_option backward.isDefEq.respectTransparency false

theorem normalizedCorePressure_tendsto_of_anchor_comparison (Ξ : Atom)
    (hSource : Section3Input Ξ)
    (C : ℝ≥0) (W : ℕ → ℕ) (hW : ∀ n, 0 < W n)
    (hWtop : Tendsto W atTop atTop) (z : ℂ)
    (hClose : TendstoInProbabilityTri
      (fun n => intervalRowsLaw (W n) (anchorSites (W n)) Ξ.law)
      (fun n x => anchorLogPotential Ξ (W n) z x -
        anchorPressureCenter Ξ.law C (W n) z) 0) :
    Tendsto (fun n => normalizedCorePressure Ξ.law C (W n) z)
      atTop (𝓝 (circularLogPotential z)) := by
  have hcenter := deterministic_center_tendsto_of_tri_anchor_and_close
    (fun n => intervalRowsLaw (W n) (anchorSites (W n)) Ξ.law)
    (fun n => anchorLogPotential Ξ (W n) z)
    (fun n => anchorPressureCenter Ξ.law C (W n) z) (circularLogPotential z)
    (subgaussian_anchor_log_potential Ξ hSource W hW hWtop z) hClose
  have hratio := tendsto_anchor_dimension_ratio.comp hWtop
  have h := hcenter.div hratio (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  convert h using 1
  funext n
  change normalizedCorePressure Ξ.law C (W n) z =
    anchorPressureCenter Ξ.law C (W n) z /
      ((anchorCells (W n) : ℝ) * cellLength (W n) / anchorSize (W n))
  rw [anchorPressureCenter_factor Ξ.law C (W n) (hW n) z]
  have hK : (anchorCells (W n) : ℝ) ≠ 0 := by exact_mod_cast (anchorCells_pos (hW n)).ne'
  have hL : (cellLength (W n) : ℝ) ≠ 0 := by exact_mod_cast (cellLength_pos (hW n)).ne'
  have hM : (anchorSize (W n) : ℝ) ≠ 0 := by exact_mod_cast (anchorSize_pos (hW n)).ne'
  field_simp [hK, hL, hM] <;> ring

end SubgaussianSection8
