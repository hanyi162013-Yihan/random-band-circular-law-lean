import CircularLawSection6.CyclicMatrixReplacement
import CircularLawSection6.SubsequenceFillers

/-! # Actual profile replacement along any increasing dimension subsequence

Missing dimensions are filled with the Ginibre comparison matrix. Both
mean energies remain exactly one. Restricting the proved replacement
conclusion recovers the original profile at every selected dimension.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem ginibre_expected_cyclicEnergy (N : ℕ) [NeZero N] :
    Integrable (fun ω => cyclicEnergy N (ginibreMatrix N ω)) (cyclicAtomLaw N circularComplexGaussian) ∧
      (∫ ω, cyclicEnergy N (ginibreMatrix N ω) ∂cyclicAtomLaw N circularComplexGaussian) = 1 := by
  unfold cyclicEnergy
  refine ⟨(ginibre_expected_energy N).1.div_const _, ?_⟩
  rw [integral_div, (ginibre_expected_energy N).2, div_self (Nat.cast_ne_zero.mpr (NeZero.ne N))]

namespace NoncompactProfile

theorem profile_ginibre_replacement_along_subsequence (p : NoncompactProfile)
    (W : ℕ → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ) (target : ℂ → ℝ)
    (hProfile : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun n => gaussianProfileLaw (φ n + 1))
        (fun n ω => matrixRawPotential (p.matrix (φ n + 1) (W (φ n)) ω - z • 1)) (target z))
    (hGinibre : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun k => cyclicAtomLaw (k + 1) circularComplexGaussian)
        (fun k ω => matrixRawPotential (ginibreMatrix (k + 1) ω - z • 1)) (target z)) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => esdDifference (cyclicPhysicalMatrix (φ n) (p.matrix (φ n + 1) (W (φ n)) (ω (φ n)).1))
          (cyclicPhysicalMatrix (φ n) (ginibreMatrix (φ n + 1) (ω (φ n)).2)) f) atTop 0 := by
  classical
  let A (k : ℕ) (ω : ZMod (k + 1) × ZMod (k + 1) → ℂ) :=
    if k ∈ Set.range φ then p.matrix (k + 1) (W k) ω else ginibreMatrix (k + 1) ω
  have hA (k : ℕ) : Measurable (A k) := by
    by_cases hk : k ∈ Set.range φ
    · simpa only [A, if_pos hk] using weightedCyclicMatrix_measurable_matrix (k + 1) (p.weight (k + 1) (W k))
    · simpa only [A, if_neg hk] using ginibreMatrix_measurable (k + 1)
  have hAE (k : ℕ) : Integrable (fun ω => cyclicEnergy (k + 1) (A k ω)) (gaussianProfileLaw (k + 1)) ∧
      (∫ ω, cyclicEnergy (k + 1) (A k ω) ∂gaussianProfileLaw (k + 1)) = 1 := by
    by_cases hk : k ∈ Set.range φ
    · simpa only [A, if_pos hk] using p.gaussian_expected_energy (k + 1) (W k)
    · simpa only [A, if_neg hk] using ginibre_expected_cyclicEnergy (k + 1)
  have hLog : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun k => gaussianProfileLaw (k + 1))
        (fun k ω => matrixRawPotential (A k ω - z • 1)) (target z) := by
    filter_upwards [hProfile, hGinibre] with z hx hy
    have hfill := tendstoInProbabilityTri_subsequence_filler
      (fun k => gaussianProfileLaw (k + 1))
      (fun k ω => matrixRawPotential (p.matrix (k + 1) (W k) ω - z • 1))
      (fun k ω => matrixRawPotential (ginibreMatrix (k + 1) ω - z • 1)) φ hφ hx hy
    apply hfill.congr ?_ rfl
    intro k ω
    by_cases hk : k ∈ Set.range φ <;> simp [A, hk]
  have hrep := cyclic_matrix_pair_replacement_of_log_limits A (fun k => ginibreMatrix (k + 1)) hA
    (fun k => ginibreMatrix_measurable (k + 1)) hAE (fun k => ginibre_expected_cyclicEnergy (k + 1))
    target hLog hGinibre
  intro f hf hc
  have hs := (hrep f hf hc).comp hφ.tendsto_atTop
  apply hs.congr ?_ Filter.EventuallyEq.rfl
  intro n
  filter_upwards with ω
  simp only [Function.comp_apply, A, if_pos (Set.mem_range_self n)]

end NoncompactProfile
end CircularLawSection6
