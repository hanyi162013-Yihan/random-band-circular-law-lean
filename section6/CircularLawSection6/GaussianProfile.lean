import CircularLawSection6.ComplexGaussian
import CircularLawSection6.ProfileMatrices
import CircularLawSection6.CyclicIndependence

/-! # Gaussian profile: product law, energy, and tail rotations

This is the literal finite model underlying Section 6. The exact identities
below include the normalization of the atoms, not just their weights.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace CircularLawSection6

def gaussianProfileLaw (N : ℕ) [NeZero N] : Measure (ZMod N × ZMod N → ℂ) :=
  cyclicAtomLaw N circularComplexGaussian

instance gaussianProfileLaw_isProbability (N : ℕ) [NeZero N] :
    IsProbabilityMeasure (gaussianProfileLaw N) := by
  unfold gaussianProfileLaw
  infer_instance

def rotateCyclicAtoms (N : ℕ) (a : ZMod N × ZMod N → Circle)
    (ω : ZMod N × ZMod N → ℂ) (k : ZMod N × ZMod N) : ℂ :=
  (a k : ℂ) * ω k

theorem rotateCyclicAtoms_measurable (N : ℕ) (a : ZMod N × ZMod N → Circle) :
    Measurable (rotateCyclicAtoms N a) :=
  measurable_pi_lambda _ fun _ => measurable_const.mul (measurable_pi_apply _)

theorem gaussianProfileLaw_rotation (N : ℕ) [NeZero N]
    (a : ZMod N × ZMod N → Circle) :
    (gaussianProfileLaw N).map (rotateCyclicAtoms N a) = gaussianProfileLaw N := by
  have h := Measure.pi_map_pi
    (μ := fun _ : ZMod N × ZMod N => circularComplexGaussian)
    (f := fun k (z : ℂ) => (a k : ℂ) * z) (fun _ => by fun_prop)
  simpa only [gaussianProfileLaw, cyclicAtomLaw, rotateCyclicAtoms,
    circularComplexGaussian_rotation] using h

theorem gaussianProfileLaw_rotation_preserving (N : ℕ) [NeZero N]
    (a : ZMod N × ZMod N → Circle) :
    MeasurePreserving (rotateCyclicAtoms N a) (gaussianProfileLaw N) (gaussianProfileLaw N) :=
  ⟨rotateCyclicAtoms_measurable N a, gaussianProfileLaw_rotation N a⟩

def tailRotation (N : ℕ) (S : Finset (ZMod N)) (a : Circle)
    (ω : ZMod N × ZMod N → ℂ) : ZMod N × ZMod N → ℂ :=
  rotateCyclicAtoms N (fun k => if k.2 ∈ S then 1 else a) ω

theorem gaussianProfileLaw_tailRotation_preserving (N : ℕ) [NeZero N]
    (S : Finset (ZMod N)) (a : Circle) :
    MeasurePreserving (tailRotation N S a) (gaussianProfileLaw N) (gaussianProfileLaw N) :=
  gaussianProfileLaw_rotation_preserving N _

theorem coreMatrix_tailRotation (N : ℕ) [NeZero N]
    (S : Finset (ZMod N)) (q : ZMod N → ℝ) (a : Circle)
    (ω : ZMod N × ZMod N → ℂ) :
    weightedCyclicMatrix N (maskedWeight S q) (tailRotation N S a ω) =
      weightedCyclicMatrix N (maskedWeight S q) ω := by
  ext i j
  by_cases hs : j - i ∈ S <;>
    simp [weightedCyclicMatrix, tailRotation, rotateCyclicAtoms, maskedWeight, hs]

theorem tailMatrix_tailRotation (N : ℕ) [NeZero N]
    (S : Finset (ZMod N)) (q : ZMod N → ℝ) (a : Circle)
    (ω : ZMod N × ZMod N → ℂ) :
    weightedCyclicMatrix N (maskedWeight Sᶜ q) (tailRotation N S a ω) =
      (a : ℂ) • weightedCyclicMatrix N (maskedWeight Sᶜ q) ω := by
  ext i j
  by_cases hs : j - i ∈ S <;>
    simp [weightedCyclicMatrix, tailRotation, rotateCyclicAtoms, maskedWeight, hs, mul_left_comm]

namespace NoncompactProfile

theorem gaussian_core_tail_independent (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) :
    IndepFun (p.coreMatrix N H W) (p.tailMatrix N H W) (gaussianProfileLaw N) :=
  weightedCyclicMatrix_core_tail_independent N _ _ _

theorem gaussian_expected_energy (p : NoncompactProfile) (N : ℕ) [NeZero N] (W : ℝ) :
    Integrable (fun ω => cyclicEnergy N (p.matrix N W ω)) (gaussianProfileLaw N) ∧
      (∫ ω, cyclicEnergy N (p.matrix N W ω) ∂gaussianProfileLaw N) = 1 :=
  p.expected_energy N W _ circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment

theorem gaussian_expected_core_energy (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) :
    Integrable (fun ω => cyclicEnergy N (p.coreMatrix N H W ω)) (gaussianProfileLaw N) ∧
      (∫ ω, cyclicEnergy N (p.coreMatrix N H W ω) ∂gaussianProfileLaw N) = p.coreMass N H W :=
  p.expected_core_energy N H W _
    circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment

theorem gaussian_expected_tail_energy (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) :
    Integrable (fun ω => cyclicEnergy N (p.tailMatrix N H W ω)) (gaussianProfileLaw N) ∧
      (∫ ω, cyclicEnergy N (p.tailMatrix N H W ω) ∂gaussianProfileLaw N) = p.tailMass N H W :=
  p.expected_tail_energy N H W _
    circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment

theorem gaussian_expected_unitCore_energy (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) :
    Integrable (fun ω => cyclicEnergy N (p.unitCoreMatrix N H W ω)) (gaussianProfileLaw N) ∧
      (∫ ω, cyclicEnergy N (p.unitCoreMatrix N H W ω) ∂gaussianProfileLaw N) = 1 :=
  p.expected_unitCore_energy N H W _
    circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment

theorem matrix_tailRotation (p : NoncompactProfile) (N H : ℕ) [NeZero N]
    (W : ℝ) (a : Circle) (ω : ZMod N × ZMod N → ℂ) :
    p.matrix N W (tailRotation N (coreOffsets N H) a ω) =
      p.coreMatrix N H W ω + (a : ℂ) • p.tailMatrix N H W ω := by
  rw [← p.coreMatrix_add_tailMatrix N H W (tailRotation N (coreOffsets N H) a ω)]
  exact congrArg₂ (· + ·) (coreMatrix_tailRotation N _ _ a ω) (tailMatrix_tailRotation N _ _ a ω)

end NoncompactProfile
end CircularLawSection6
