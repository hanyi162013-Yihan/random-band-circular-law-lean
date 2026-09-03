import CircularLawSection6.NoncompactReferenceMean
import CircularLawSection6.ProfileDiagonalBound

/-! # The actual Gaussian profile mean implies its probability limit

The previously proved diagonal estimate and all-positive-dimension
Gaussian concentration discharge the fluctuation input. This bridge has
no excluded dimension-one prefix and no assumed concentration statement.
-/

open MeasureTheory Filter Topology
open CircularLawSections56.Section5

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

theorem full_profile_probability_of_mean (p : NoncompactProfile)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop)
    (W : ℕ → ℝ) (z : ℂ) {target : ℝ}
    (hmean : Tendsto (fun n => (∫ ω, p.rawProfileLogDet (N n) (W n) z ω
      ∂gaussianProfileLaw (N n)) / (N n : ℝ)) atTop (𝓝 target)) :
    TendstoInProbabilityTri (fun n => gaussianProfileLaw (N n))
      (fun n ω => matrixRawPotential (p.matrix (N n) (W n) ω - z • 1)) target := by
  have hclose := (gaussian_cyclic_concentration_all N hN (fun n => p.weight (N n) (W n))
    p.diagonalComparisonConstant_pos (r := 1) zero_lt_one z (fun n => p.diagonal_weight_ge (N n) (W n))).2
  have hc : TendstoInProbabilityTri (fun n => gaussianProfileLaw (N n))
      (fun n ω => matrixRawPotential (p.matrix (N n) (W n) ω - z • 1) -
        ∫ η, matrixRawPotential (p.matrix (N n) (W n) η - z • 1) ∂gaussianProfileLaw (N n)) 0 := by
    simpa only [matrixRawPotential, ZMod.card, matrix, gaussianProfileLaw,
      cyclicRawLogDet, Complex.ofReal_one, one_smul] using hclose
  have hm : Tendsto (fun n => ∫ ω, matrixRawPotential (p.matrix (N n) (W n) ω - z • 1)
      ∂gaussianProfileLaw (N n)) atTop (𝓝 target) := by
    simpa only [matrixRawPotential, ZMod.card, rawProfileLogDet, integral_div] using hmean
  have hdet := tendstoInProbabilityTri_const (fun n => gaussianProfileLaw (N n)) _ target hm
  simpa only [sub_add_cancel, zero_add] using hc.add (fun n => gaussianProfileLaw (N n)) hdet

end CircularLawSection6.NoncompactProfile
