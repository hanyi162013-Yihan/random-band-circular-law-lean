import CircularLawSection6.ProfileReplacement

/-! # Reusable actual cyclic-matrix replacement on the Gaussian pair space

This version accepts arbitrary measurable cyclic matrices with unit mean
normalized energies. It supports subsequence fillers without modifying
the fixed-dimension replacement theorem or assuming a new replacement law.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem cyclic_matrix_pair_replacement_of_log_limits
    (A B : ∀ k : ℕ, (ZMod (k + 1) × ZMod (k + 1) → ℂ) →
      Matrix (ZMod (k + 1)) (ZMod (k + 1)) ℂ)
    (hA : ∀ k, Measurable (A k)) (hB : ∀ k, Measurable (B k))
    (hAE : ∀ k, Integrable (fun ω => cyclicEnergy (k + 1) (A k ω)) (gaussianProfileLaw (k + 1)) ∧
      (∫ ω, cyclicEnergy (k + 1) (A k ω) ∂gaussianProfileLaw (k + 1)) = 1)
    (hBE : ∀ k, Integrable (fun ω => cyclicEnergy (k + 1) (B k ω)) (cyclicAtomLaw (k + 1) circularComplexGaussian) ∧
      (∫ ω, cyclicEnergy (k + 1) (B k ω) ∂cyclicAtomLaw (k + 1) circularComplexGaussian) = 1)
    (target : ℂ → ℝ)
    (hLogA : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun k => gaussianProfileLaw (k + 1))
        (fun k ω => matrixRawPotential (A k ω - z • 1)) (target z))
    (hLogB : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun k => cyclicAtomLaw (k + 1) circularComplexGaussian)
        (fun k ω => matrixRawPotential (B k ω - z • 1)) (target z)) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun k ω => esdDifference (cyclicPhysicalMatrix k (A k (ω k).1))
          (cyclicPhysicalMatrix k (B k (ω k).2)) f) atTop 0 := by
  let X (k : ℕ) (ω : ZMod (k + 1) × ZMod (k + 1) → ℂ) :=
    cyclicPhysicalMatrix k (A k ω)
  let Y (k : ℕ) (ω : ZMod (k + 1) × ZMod (k + 1) → ℂ) :=
    cyclicPhysicalMatrix k (B k ω)
  have hX (k : ℕ) (i j : Fin (k + 1)) : Measurable (fun ω => X k ω i j) :=
    cyclicPhysicalMatrix_entry_measurable k _ (hA k) i j
  have hY (k : ℕ) (i j : Fin (k + 1)) : Measurable (fun ω => Y k ω i j) :=
    cyclicPhysicalMatrix_entry_measurable k _ (hB k) i j
  have hEX (k : ℕ) : Integrable (fun ω => physicalEnergy (X k ω)) (gaussianProfileLaw (k + 1)) ∧
      (∫ ω, physicalEnergy (X k ω) ∂gaussianProfileLaw (k + 1)) = 1 := by
    simpa only [X, cyclicPhysicalMatrix_energy] using hAE k
  have hEY (k : ℕ) : Integrable (fun ω => physicalEnergy (Y k ω)) (cyclicAtomLaw (k + 1) circularComplexGaussian) ∧
      (∫ ω, physicalEnergy (Y k ω) ∂cyclicAtomLaw (k + 1) circularComplexGaussian) = 1 := by
    simpa only [Y, cyclicPhysicalMatrix_energy] using hBE k
  apply triangular_physical_replacement profileGinibrePairLaw
    (fun k ω => X k ω.1) (fun k ω => Y k ω.2)
    (fun k i j => (hX k i j).comp measurable_fst) (fun k i j => (hY k i j).comp measurable_snd)
    2 (by norm_num) ?_ ?_ target ?_ ?_
  · intro k
    exact (measurePreserving_fst.integrable_comp_of_integrable (hEX k).1).add
      (measurePreserving_snd.integrable_comp_of_integrable (hEY k).1)
  · intro k
    have hiX : Integrable (fun ω => physicalEnergy (X k ω.1)) (profileGinibrePairLaw k) :=
      measurePreserving_fst.integrable_comp_of_integrable (hEX k).1
    have hiY : Integrable (fun ω => physicalEnergy (Y k ω.2)) (profileGinibrePairLaw k) :=
      measurePreserving_snd.integrable_comp_of_integrable (hEY k).1
    have heX : (∫ ω, physicalEnergy (X k ω.1) ∂profileGinibrePairLaw k) = 1 :=
      (integral_comp_of_measurePreserving_aes measurePreserving_fst _
        (hEX k).1.aestronglyMeasurable).trans (hEX k).2
    have heY : (∫ ω, physicalEnergy (Y k ω.2) ∂profileGinibrePairLaw k) = 1 :=
      (integral_comp_of_measurePreserving_aes measurePreserving_snd _
        (hEY k).1.aestronglyMeasurable).trans (hEY k).2
    rw [integral_add hiX hiY, heX, heY]
    norm_num
  · filter_upwards [hLogA] with z hz
    have hp : TendstoInProbabilityTri (fun k => gaussianProfileLaw (k + 1))
        (fun k ω => physicalLogPotential (X k ω) z) (target z) := by
      simpa only [X, cyclicPhysicalMatrix_logPotential] using hz
    exact tendstoInProbabilityTri_comp_measurePreserving profileGinibrePairLaw
      (fun k => gaussianProfileLaw (k + 1)) (fun _ => Prod.fst) (fun _ => measurePreserving_fst)
      (fun k ω => physicalLogPotential (X k ω) z) (fun k => measurable_physicalLogPotential (X k) (hX k) z) hp
  · filter_upwards [hLogB] with z hz
    have hp : TendstoInProbabilityTri (fun k => cyclicAtomLaw (k + 1) circularComplexGaussian)
        (fun k ω => physicalLogPotential (Y k ω) z) (target z) := by
      simpa only [Y, cyclicPhysicalMatrix_logPotential] using hz
    exact tendstoInProbabilityTri_comp_measurePreserving profileGinibrePairLaw
      (fun k => cyclicAtomLaw (k + 1) circularComplexGaussian) (fun _ => Prod.snd) (fun _ => measurePreserving_snd)
      (fun k ω => physicalLogPotential (Y k ω) z) (fun k => measurable_physicalLogPotential (Y k) (hY k) z) hp


end CircularLawSection6
