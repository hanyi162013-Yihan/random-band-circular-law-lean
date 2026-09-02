import CircularLawSection6.GaussianCyclicConcentration
import CircularLawSection6.ProfileDiagonalBound
import CircularLawSection6.GaussianTailJensen

/-! # Concentration of the full, truncated, and normalized-core profiles

All diagonal bounds are proved from the original profile. The bandwidth and
core radius may vary arbitrarily in these concentration statements; only
the matrix dimension must diverge.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open CircularLawSections56.Section5

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

theorem rawProfileLogDet_memLp (p : NoncompactProfile) (d : ℕ) (W : ℝ) (z : ℂ) :
    MemLp (p.rawProfileLogDet (d + 2) W z) 2 (gaussianProfileLaw (d + 2)) := by
  have h := (gaussian_cyclic_memLp_and_variance d (p.weight (d + 2) W)
    p.diagonalComparisonConstant_pos (r := 1) zero_lt_one z (p.diagonal_weight_ge (d + 2) W)).1
  simpa only [cyclicRawLogDet, rawProfileLogDet, matrix, gaussianProfileLaw,
    Complex.ofReal_one, one_smul] using h

theorem rawCoreLogDet_memLp (p : NoncompactProfile) (d H : ℕ) (W : ℝ) (z : ℂ) :
    MemLp (p.rawCoreLogDet (d + 2) H W z) 2 (gaussianProfileLaw (d + 2)) := by
  have hq : p.diagonalComparisonConstant / (d + 2 : ℝ) ≤
      maskedWeight (coreOffsets (d + 2) H) (p.weight (d + 2) W) 0 := by
    simpa only [maskedWeight, if_pos (zero_mem_coreOffsets _ _)] using
      p.diagonal_weight_ge (d + 2) W
  have h := (gaussian_cyclic_memLp_and_variance d _
    p.diagonalComparisonConstant_pos (r := 1) zero_lt_one z hq).1
  simpa only [cyclicRawLogDet, rawCoreLogDet, coreMatrix, gaussianProfileLaw,
    Complex.ofReal_one, one_smul] using h

theorem full_profile_L1_concentration (p : NoncompactProfile) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => d n + 2) atTop atTop) (W : ℕ → ℝ) (z : ℂ) :
    Tendsto (fun n => ∫ ω,
      |p.rawProfileLogDet (d n + 2) (W n) z ω / (d n + 2 : ℝ) -
        ∫ x, p.rawProfileLogDet (d n + 2) (W n) z x / (d n + 2 : ℝ)
          ∂gaussianProfileLaw (d n + 2)| ∂gaussianProfileLaw (d n + 2)) atTop (𝓝 0) := by
  have h := (gaussian_cyclic_concentration d hd (fun n => p.weight (d n + 2) (W n))
    p.diagonalComparisonConstant_pos (r := 1) zero_lt_one z
    (fun n => p.diagonal_weight_ge (d n + 2) (W n))).1
  simpa only [cyclicRawLogDet, rawProfileLogDet, matrix, gaussianProfileLaw,
    Complex.ofReal_one, one_smul] using h

theorem full_profile_concentration (p : NoncompactProfile) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => d n + 2) atTop atTop) (W : ℕ → ℝ) (z : ℂ) :
    TendstoInProbabilityTri (fun n => gaussianProfileLaw (d n + 2))
      (fun n ω => p.rawProfileLogDet (d n + 2) (W n) z ω / (d n + 2 : ℝ) -
        ∫ x, p.rawProfileLogDet (d n + 2) (W n) z x / (d n + 2 : ℝ)
          ∂gaussianProfileLaw (d n + 2)) 0 := by
  have h := (gaussian_cyclic_concentration d hd (fun n => p.weight (d n + 2) (W n))
    p.diagonalComparisonConstant_pos (r := 1) zero_lt_one z
    (fun n => p.diagonal_weight_ge (d n + 2) (W n))).2
  simpa only [cyclicRawLogDet, rawProfileLogDet, matrix, gaussianProfileLaw,
    Complex.ofReal_one, one_smul] using h

theorem core_profile_concentration (p : NoncompactProfile) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => d n + 2) atTop atTop) (H : ℕ → ℕ) (W : ℕ → ℝ) (z : ℂ) :
    TendstoInProbabilityTri (fun n => gaussianProfileLaw (d n + 2))
      (fun n ω => p.rawCoreLogDet (d n + 2) (H n) (W n) z ω / (d n + 2 : ℝ) -
        ∫ x, p.rawCoreLogDet (d n + 2) (H n) (W n) z x / (d n + 2 : ℝ)
          ∂gaussianProfileLaw (d n + 2)) 0 := by
  have hq (n : ℕ) : p.diagonalComparisonConstant / (d n + 2 : ℝ) ≤
      maskedWeight (coreOffsets (d n + 2) (H n)) (p.weight (d n + 2) (W n)) 0 := by
    simpa only [maskedWeight, if_pos (zero_mem_coreOffsets _ _)] using
      p.diagonal_weight_ge (d n + 2) (W n)
  have h := (gaussian_cyclic_concentration d hd _
    p.diagonalComparisonConstant_pos (r := 1) zero_lt_one z hq).2
  simpa only [cyclicRawLogDet, rawCoreLogDet, coreMatrix, gaussianProfileLaw,
    Complex.ofReal_one, one_smul] using h

theorem unitCore_profile_concentration (p : NoncompactProfile) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => d n + 2) atTop atTop) (H : ℕ → ℕ) (W : ℕ → ℝ)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    TendstoInProbabilityTri (fun n => gaussianProfileLaw (d n + 2))
      (fun n ω => Real.log ‖((r : ℂ) • p.unitCoreMatrix (d n + 2) (H n) (W n) ω - z • 1).det‖ /
          (d n + 2 : ℝ) -
        ∫ x, Real.log ‖((r : ℂ) • p.unitCoreMatrix (d n + 2) (H n) (W n) x - z • 1).det‖ /
          (d n + 2 : ℝ) ∂gaussianProfileLaw (d n + 2)) 0 := by
  have hq (n : ℕ) : p.diagonalComparisonConstant / (d n + 2 : ℝ) ≤
      maskedWeight (coreOffsets (d n + 2) (H n)) (p.normalizedCoreWeight (d n + 2) (H n) (W n)) 0 := by
    simpa only [maskedWeight, if_pos (zero_mem_coreOffsets _ _)] using
      p.diagonal_normalizedCoreWeight_ge (d n + 2) (H n) (W n)
  have h := (gaussian_cyclic_concentration d hd _ p.diagonalComparisonConstant_pos hr z hq).2
  simpa only [cyclicRawLogDet, unitCoreMatrix, gaussianProfileLaw] using h

end CircularLawSection6.NoncompactProfile
