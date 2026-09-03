import CircularLawSection6.SampledProfile
import CircularLawSection6.CyclicMatrix

/-! # Literal profile matrices, their truncations, and normalization

All three matrices live on the same explicitly indexed atom space. The core
and tail have disjoint entries. No positivity of a tail mass is required;
an empty tail is represented by the zero matrix.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace CircularLawSection6

theorem maskedWeight_nonneg {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (q : ι → ℝ) (hq : ∀ s, 0 ≤ q s) (s : ι) : 0 ≤ maskedWeight S q s := by
  by_cases hs : s ∈ S <;> simp [maskedWeight, hs, hq s]

theorem sum_maskedWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (q : ι → ℝ) : ∑ s, maskedWeight S q s = ∑ s ∈ S, q s := by
  simp [maskedWeight]

theorem weightedCyclicMatrix_scale (N : ℕ) (q : ZMod N → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (ω : ZMod N × ZMod N → ℂ) :
    weightedCyclicMatrix N (fun s => t * q s) ω =
      (Real.sqrt t : ℂ) • weightedCyclicMatrix N q ω := by
  ext i j
  simp [weightedCyclicMatrix, Real.sqrt_mul ht, mul_assoc]

namespace NoncompactProfile

def matrix (p : NoncompactProfile) (N : ℕ) [NeZero N] (W : ℝ)
    (ω : ZMod N × ZMod N → ℂ) : Matrix (ZMod N) (ZMod N) ℂ :=
  weightedCyclicMatrix N (p.weight N W) ω

def coreMatrix (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ)
    (ω : ZMod N × ZMod N → ℂ) : Matrix (ZMod N) (ZMod N) ℂ :=
  weightedCyclicMatrix N (maskedWeight (coreOffsets N H) (p.weight N W)) ω

def tailMatrix (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ)
    (ω : ZMod N × ZMod N → ℂ) : Matrix (ZMod N) (ZMod N) ℂ :=
  weightedCyclicMatrix N (maskedWeight (coreOffsets N H)ᶜ (p.weight N W)) ω

def unitCoreMatrix (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ)
    (ω : ZMod N × ZMod N → ℂ) : Matrix (ZMod N) (ZMod N) ℂ :=
  weightedCyclicMatrix N (maskedWeight (coreOffsets N H) (p.normalizedCoreWeight N H W)) ω

theorem coreMatrix_add_tailMatrix (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ)
    (ω : ZMod N × ZMod N → ℂ) :
    p.coreMatrix N H W ω + p.tailMatrix N H W ω = p.matrix N W ω :=
  weightedCyclicMatrix_core_add_tail N (coreOffsets N H) (p.weight N W) ω

theorem coreEnergy_add_tailEnergy (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ)
    (ω : ZMod N × ZMod N → ℂ) :
    cyclicEnergy N (p.coreMatrix N H W ω) + cyclicEnergy N (p.tailMatrix N H W ω) =
      cyclicEnergy N (p.matrix N W ω) :=
  cyclicEnergy_core_add_tail N (coreOffsets N H) (p.weight N W) ω

theorem coreMatrix_eq_scale_unitCoreMatrix (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) (ω : ZMod N × ZMod N → ℂ) :
    p.coreMatrix N H W ω =
      (Real.sqrt (p.coreMass N H W) : ℂ) • p.unitCoreMatrix N H W ω := by
  have hw : maskedWeight (coreOffsets N H) (p.weight N W) =
      fun s => p.coreMass N H W *
        maskedWeight (coreOffsets N H) (p.normalizedCoreWeight N H W) s := by
    funext s
    by_cases hs : s ∈ coreOffsets N H
    · simp only [maskedWeight, if_pos hs, p.normalizedCoreWeight_eq]
      field_simp [(p.coreMass_pos N H W).ne']
    · simp [maskedWeight, hs]
  unfold coreMatrix unitCoreMatrix
  rw [hw, weightedCyclicMatrix_scale N _ (p.coreMass_pos N H W).le]

theorem row_variance_sum (p : NoncompactProfile) (N : ℕ) [NeZero N]
    (W : ℝ) (i : ZMod N) : ∑ j, p.weight N W (j - i) = 1 := by
  rw [cyclic_row_variance_sum, p.sum_weight]

theorem column_variance_sum (p : NoncompactProfile) (N : ℕ) [NeZero N]
    (W : ℝ) (j : ZMod N) : ∑ i, p.weight N W (j - i) = 1 := by
  rw [cyclic_column_variance_sum, p.sum_weight]

theorem expected_energy (p : NoncompactProfile) (N : ℕ) [NeZero N] (W : ℝ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun z : ℂ => ‖z‖ ^ 2) ν)
    (hUnit : (∫ z : ℂ, ‖z‖ ^ 2 ∂ν) = 1) :
    Integrable (fun ω => cyclicEnergy N (p.matrix N W ω)) (cyclicAtomLaw N ν) ∧
      (∫ ω, cyclicEnergy N (p.matrix N W ω) ∂cyclicAtomLaw N ν) = 1 := by
  simpa only [matrix, p.sum_weight, hUnit, one_mul] using
    weightedCyclicMatrix_expected_energy N (p.weight N W)
      (fun s => (p.weight_pos N W s).le) ν hInt

theorem expected_core_energy (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun z : ℂ => ‖z‖ ^ 2) ν)
    (hUnit : (∫ z : ℂ, ‖z‖ ^ 2 ∂ν) = 1) :
    Integrable (fun ω => cyclicEnergy N (p.coreMatrix N H W ω)) (cyclicAtomLaw N ν) ∧
      (∫ ω, cyclicEnergy N (p.coreMatrix N H W ω) ∂cyclicAtomLaw N ν) = p.coreMass N H W := by
  simpa only [coreMatrix, sum_maskedWeight, coreMass, hUnit, mul_one] using
    weightedCyclicMatrix_expected_energy N _
      (maskedWeight_nonneg _ _ (fun s => (p.weight_pos N W s).le)) ν hInt

theorem expected_tail_energy (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun z : ℂ => ‖z‖ ^ 2) ν)
    (hUnit : (∫ z : ℂ, ‖z‖ ^ 2 ∂ν) = 1) :
    Integrable (fun ω => cyclicEnergy N (p.tailMatrix N H W ω)) (cyclicAtomLaw N ν) ∧
      (∫ ω, cyclicEnergy N (p.tailMatrix N H W ω) ∂cyclicAtomLaw N ν) = p.tailMass N H W := by
  simpa only [tailMatrix, sum_maskedWeight, tailMass, hUnit, mul_one] using
    weightedCyclicMatrix_expected_energy N _
      (maskedWeight_nonneg _ _ (fun s => (p.weight_pos N W s).le)) ν hInt

theorem expected_unitCore_energy (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun z : ℂ => ‖z‖ ^ 2) ν)
    (hUnit : (∫ z : ℂ, ‖z‖ ^ 2 ∂ν) = 1) :
    Integrable (fun ω => cyclicEnergy N (p.unitCoreMatrix N H W ω)) (cyclicAtomLaw N ν) ∧
      (∫ ω, cyclicEnergy N (p.unitCoreMatrix N H W ω) ∂cyclicAtomLaw N ν) = 1 := by
  simpa only [unitCoreMatrix, sum_maskedWeight, p.sum_normalizedCoreWeight, hUnit, one_mul] using
    weightedCyclicMatrix_expected_energy N
      (maskedWeight (coreOffsets N H) (p.normalizedCoreWeight N H W))
      (maskedWeight_nonneg _ _ (fun s =>
        (div_pos (p.positive _) (p.rawCoreMass_pos N H W)).le)) ν hInt

end NoncompactProfile
end CircularLawSection6
