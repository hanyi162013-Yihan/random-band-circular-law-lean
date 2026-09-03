import ShortRingAnchor.Proposition38.Profile
import ShortRingAnchor.Proposition38.AtomMoments
import Vendor.SubgaussianNorm.Data

/-!
# Proposition 3.8: independent atoms and the actual matrix

The independent array includes unused entries outside the mask. They never
affect the matrix. This is the conventional `A ∘ X` realization needed by
Cook 1.12; no estimate or nonsingularity assertion is a field of the model.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ShortRingAnchor.Proposition38

structure AtomArray {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Atom) (I : Type*) where
  entry : I → Ω → ℝ
  measurable : ∀ i, Measurable (entry i)
  independent : iIndepFun entry μ
  law : ∀ i, IdentDistrib (entry i) (fun x : ℝ => x) μ A.law

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {A : Atom}

def AtomArray.subgaussianFamily {I : Type*} (S : AtomArray μ A I) :
    SubgaussianNorm.IidSubgaussianFamily Ω μ I where
  atom := S.entry
  measurable_atom := S.measurable
  independent := S.independent
  identically_distributed i j := (S.law i).trans (S.law j).symm
  centered i := (S.law i).integral_eq.trans A.centered
  variance_one i := (S.law i).pow.integral_eq.trans A.second_moment
  subgaussianParameter := A.parameter
  subgaussian i := A.subgaussian.congr_identDistrib (S.law i).symm

def AtomArray.subgaussianSquare {n : ℕ} (S : AtomArray μ A (Fin n × Fin n)) :
    SubgaussianNorm.IidSubgaussianSquare Ω μ n :=
  S.subgaussianFamily.squareRestriction (Function.Embedding.refl _)

/-- Equation (2.13): real IID atoms can be regarded as complex IID atoms,
without imposing a planar density or a non-real support condition. -/
theorem AtomArray.complexCopies {I : Type*} (S : AtomArray μ A I) :
    IndependentAtomCopies21 μ A.law (fun x : ℝ => (x : ℂ))
      (fun i sample => (S.entry i sample : ℂ)) where
  measurable i := Complex.measurable_ofReal.comp (S.measurable i)
  independent := S.independent.comp (fun _ x => (x : ℂ))
    (fun _ => Complex.measurable_ofReal)
  law i := (S.law i).comp Complex.measurable_ofReal

def fullBlockMatrix {W s : ℕ}
    (S : AtomArray μ A (Fin ((s + 3) * W) × Fin ((s + 3) * W))) (sample : Ω) :
    Matrix (Fin ((s + 3) * W)) (Fin ((s + 3) * W)) ℂ :=
  fun i j => (coefficient W s i j : ℂ) * (S.entry (i, j) sample : ℂ)

def fullBlockV3Model {W s : ℕ} (hW : 0 < W)
    (S : AtomArray μ A (Fin ((s + 3) * W) × Fin ((s + 3) * W))) :
    Arxiv2410V3.RandomMatrixModelV3 ((s + 3) * W) Ω ℝ μ A.law where
  matrix := fullBlockMatrix S
  atom := fun x : ℝ => (x : ℂ)
  profile := varianceProfile W s hW
  entry_measurable i j := (S.complexCopies.measurable (i, j)).const_mul _
  entries_independent := S.complexCopies.independent.comp
    (fun ij x => (coefficient W s ij.1 ij.2 : ℂ) * x)
    (fun _ => measurable_const.mul measurable_id)
  entry_law i j := (S.complexCopies.law (i, j)).const_mul _
  atom_integrable := A.momentAssumption21.integrable
  atom_mean_zero := A.momentAssumption21.centered
  atom_variance_one := A.momentAssumption21.unitSecondMoment
  atom_third_moment_finite := A.momentAssumption21.thirdMomentIntegrable

/-- Proposition 3.8, use of v3 estimates in (3.23)--(3.24): the literal
matrix, not an unrelated surrogate ensemble, has bandwidth `3W`. -/
theorem fullBlockV3Model_isBandwidth {W s : ℕ} (hW : 0 < W)
    (S : AtomArray μ A (Fin ((s + 3) * W) × Fin ((s + 3) * W))) :
    Arxiv2410V3.IsBandwidth (fullBlockV3Model hW S).profile (3 * (W : ℝ)) :=
  varianceProfile_isBandwidth W s hW

end ShortRingAnchor.Proposition38
