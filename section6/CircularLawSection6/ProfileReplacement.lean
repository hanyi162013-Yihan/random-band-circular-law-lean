import CircularLawSection6.ProfileProbability
import CircularLawSection6.CoupledCdfComparison
import CircularLawSection6.TriangularLawTransport
import CircularLawSections56.Section6.LiteralIndicatorModel

/-! # Actual profile-versus-Ginibre spectral replacement

The finite Gaussian sample spaces are coupled independently and then
realized on their canonical countable product. Coordinate reindexing,
normalization and the two exact mean energies are discharged. The proved
Tao--Vu replacement theorem is reused, not supplied as an assumption.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

def cyclicPhysicalMatrix (k : ℕ) (A : Matrix (ZMod (k + 1)) (ZMod (k + 1)) ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  A.submatrix (ZMod.finEquiv (k + 1)).toEquiv (ZMod.finEquiv (k + 1)).toEquiv

theorem cyclicPhysicalMatrix_logPotential (k : ℕ)
    (A : Matrix (ZMod (k + 1)) (ZMod (k + 1)) ℂ) (z : ℂ) :
    physicalLogPotential (cyclicPhysicalMatrix k A) z = matrixRawPotential (A - z • 1) := by
  have hm : cyclicPhysicalMatrix k A - z • 1 =
      (A - z • 1).submatrix (ZMod.finEquiv (k + 1)).toEquiv (ZMod.finEquiv (k + 1)).toEquiv := by
    ext i j
    simp only [cyclicPhysicalMatrix, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, (ZMod.finEquiv (k + 1)).injective.eq_iff]
  unfold physicalLogPotential
  rw [hm, Matrix.det_submatrix_equiv_self]
  simp only [matrixRawPotential, ZMod.card, Nat.cast_add, Nat.cast_one]

theorem cyclicPhysicalMatrix_energy (k : ℕ)
    (A : Matrix (ZMod (k + 1)) (ZMod (k + 1)) ℂ) :
    physicalEnergy (cyclicPhysicalMatrix k A) = cyclicEnergy (k + 1) A := by
  unfold physicalEnergy cyclicPhysicalMatrix cyclicEnergy
  rw [hilbertSchmidtSq_reindex (ZMod.finEquiv (k + 1)).toEquiv]
  simp only [Nat.cast_add, Nat.cast_one]

theorem cyclicPhysicalMatrix_entry_measurable {Ω : Type*} [MeasurableSpace Ω]
    (k : ℕ) (A : Ω → Matrix (ZMod (k + 1)) (ZMod (k + 1)) ℂ) (hA : Measurable A)
    (i j : Fin (k + 1)) : Measurable (fun ω => cyclicPhysicalMatrix k (A ω) i j) :=
  (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hA)

def profileGinibrePairLaw (k : ℕ) :
    Measure ((ZMod (k + 1) × ZMod (k + 1) → ℂ) × (ZMod (k + 1) × ZMod (k + 1) → ℂ)) :=
  (gaussianProfileLaw (k + 1)).prod (cyclicAtomLaw (k + 1) circularComplexGaussian)

instance profileGinibrePairLaw_probability (k : ℕ) : IsProbabilityMeasure (profileGinibrePairLaw k) := by
  unfold profileGinibrePairLaw
  infer_instance

namespace NoncompactProfile

theorem profile_ginibre_replacement_of_log_limits (p : NoncompactProfile) (W : ℕ → ℝ)
    (target : ℂ → ℝ)
    (hProfile : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun k => gaussianProfileLaw (k + 1))
        (fun k ω => matrixRawPotential (p.matrix (k + 1) (W k) ω - z • 1)) (target z))
    (hGinibre : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun k => cyclicAtomLaw (k + 1) circularComplexGaussian)
        (fun k ω => matrixRawPotential (ginibreMatrix (k + 1) ω - z • 1)) (target z)) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun k ω => esdDifference (cyclicPhysicalMatrix k (p.matrix (k + 1) (W k) (ω k).1))
          (cyclicPhysicalMatrix k (ginibreMatrix (k + 1) (ω k).2)) f) atTop 0 := by
  let X (k : ℕ) (ω : ZMod (k + 1) × ZMod (k + 1) → ℂ) :=
    cyclicPhysicalMatrix k (p.matrix (k + 1) (W k) ω)
  let Y (k : ℕ) (ω : ZMod (k + 1) × ZMod (k + 1) → ℂ) :=
    cyclicPhysicalMatrix k (ginibreMatrix (k + 1) ω)
  have hX (k : ℕ) (i j : Fin (k + 1)) : Measurable (fun ω => X k ω i j) :=
    cyclicPhysicalMatrix_entry_measurable k _ (weightedCyclicMatrix_measurable_matrix _ _) i j
  have hY (k : ℕ) (i j : Fin (k + 1)) : Measurable (fun ω => Y k ω i j) :=
    cyclicPhysicalMatrix_entry_measurable k _ (ginibreMatrix_measurable _) i j
  have hEX (k : ℕ) : Integrable (fun ω => physicalEnergy (X k ω)) (gaussianProfileLaw (k + 1)) ∧
      (∫ ω, physicalEnergy (X k ω) ∂gaussianProfileLaw (k + 1)) = 1 := by
    simpa only [X, cyclicPhysicalMatrix_energy] using p.gaussian_expected_energy (k + 1) (W k)
  have hEY (k : ℕ) : Integrable (fun ω => physicalEnergy (Y k ω)) (cyclicAtomLaw (k + 1) circularComplexGaussian) ∧
      (∫ ω, physicalEnergy (Y k ω) ∂cyclicAtomLaw (k + 1) circularComplexGaussian) = 1 := by
    simp only [Y, cyclicPhysicalMatrix_energy, cyclicEnergy]
    refine ⟨(ginibre_expected_energy (k + 1)).1.div_const _, ?_⟩
    rw [integral_div, (ginibre_expected_energy (k + 1)).2,
      div_self (by positivity : ((k + 1 : ℕ) : ℝ) ≠ 0)]
  apply triangular_physical_replacement profileGinibrePairLaw
    (fun k ω => X k ω.1) (fun k ω => Y k ω.2)
    (fun k i j => (hX k i j).comp measurable_fst) (fun k i j => (hY k i j).comp measurable_snd)
    2 (by norm_num) _ _ target
  · intro k
    exact (measurePreserving_fst.integrable_comp_of_integrable (hEX k).1).add
      (measurePreserving_snd.integrable_comp_of_integrable (hEY k).1)
  · intro k
    rw [integral_add (measurePreserving_fst.integrable_comp_of_integrable (hEX k).1)
      (measurePreserving_snd.integrable_comp_of_integrable (hEY k).1),
      integral_comp_of_measurePreserving_aes measurePreserving_fst _ (hEX k).1.aestronglyMeasurable,
      integral_comp_of_measurePreserving_aes measurePreserving_snd _ (hEY k).1.aestronglyMeasurable,
      (hEX k).2, (hEY k).2]
    norm_num
  · filter_upwards [hProfile] with z hz
    have hp : TendstoInProbabilityTri (fun k => gaussianProfileLaw (k + 1))
        (fun k ω => physicalLogPotential (X k ω) z) (target z) := by
      simpa only [X, cyclicPhysicalMatrix_logPotential] using hz
    exact tendstoInProbabilityTri_comp_measurePreserving profileGinibrePairLaw
      (fun k => gaussianProfileLaw (k + 1)) (fun _ => Prod.fst) (fun _ => measurePreserving_fst)
      (fun k ω => physicalLogPotential (X k ω) z) (fun k => measurable_physicalLogPotential (X k) (hX k) z) hp
  · filter_upwards [hGinibre] with z hz
    have hp : TendstoInProbabilityTri (fun k => cyclicAtomLaw (k + 1) circularComplexGaussian)
        (fun k ω => physicalLogPotential (Y k ω) z) (target z) := by
      simpa only [Y, cyclicPhysicalMatrix_logPotential] using hz
    exact tendstoInProbabilityTri_comp_measurePreserving profileGinibrePairLaw
      (fun k => cyclicAtomLaw (k + 1) circularComplexGaussian) (fun _ => Prod.snd) (fun _ => measurePreserving_snd)
      (fun k ω => physicalLogPotential (Y k ω) z) (fun k => measurable_physicalLogPotential (Y k) (hY k) z) hp

end NoncompactProfile
end CircularLawSection6
