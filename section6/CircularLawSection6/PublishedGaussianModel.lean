import CircularLawSection6.PublishedLimitingHardEdge
import CircularLawSection6.GaussianAtomTransfer
import CircularLawSection6.GinibreReference
import CircularLawSections56.Section5.PublishedSection3Sampling
import ShortRingAnchor.DenseV3Model

/-! # The actual Ginibre law is the published Section 3 dense model

The moment and density records are proved for the already constructed Gaussian
measure. A coordinate permutation gives the actual independent dense atoms,
and the matrix identity includes its exact square-root normalization.
-/

open MeasureTheory ProbabilityTheory ShortRingAnchor Arxiv2410V3
open CircularLawSections56.Section5 CircularLawSection4
noncomputable section
set_option autoImplicit false

namespace CircularLawSection6

theorem circularComplexGaussian_thirdMoment_integrable :
    Integrable (fun z : ℂ => ‖z‖ ^ 3) circularComplexGaussian := by
  simpa only [id_eq] using
    (IsGaussian.memLp_id circularComplexGaussian 3 (by norm_num)).integrable_norm_pow (by norm_num)

theorem circularComplexGaussian_publishedMoments :
    AtomMomentAssumption21 circularComplexGaussian id where
  stronglyMeasurable := stronglyMeasurable_id
  centered := circularComplexGaussian_mean
  unitSecondMoment := circularComplexGaussian_secondMoment
  thirdMomentIntegrable := circularComplexGaussian_thirdMoment_integrable

def denseFinAtomCoordinate (N : ℕ) [NeZero N] (ij : Fin N × Fin N) : ZMod N × ZMod N :=
  (ZMod.finEquiv N ij.1, ZMod.finEquiv N ij.2 - ZMod.finEquiv N ij.1)

theorem denseFinAtomCoordinate_injective (N : ℕ) [NeZero N] :
    Function.Injective (denseFinAtomCoordinate N) := by
  intro x y h
  have hrow : ZMod.finEquiv N x.1 = ZMod.finEquiv N y.1 :=
    congrArg (fun p : ZMod N × ZMod N => p.1) h
  have hcol : ZMod.finEquiv N x.2 - ZMod.finEquiv N x.1 =
      ZMod.finEquiv N y.2 - ZMod.finEquiv N y.1 :=
    congrArg (fun p : ZMod N × ZMod N => p.2) h
  apply Prod.ext ((ZMod.finEquiv N).injective hrow)
  rw [hrow] at hcol
  exact (ZMod.finEquiv N).injective (sub_left_inj.mp hcol)

def denseFinAtoms (N : ℕ) [NeZero N] (ω : ZMod N × ZMod N → ℂ) : Fin N × Fin N → ℂ :=
  fun ij => ω (denseFinAtomCoordinate N ij)

theorem denseFinAtoms_measurePreserving (N : ℕ) [NeZero N] :
    MeasurePreserving (denseFinAtoms N) (cyclicAtomLaw N circularComplexGaussian)
      (Measure.pi (fun _ : Fin N × Fin N => circularComplexGaussian)) :=
  measurePreserving_pi_restrict_injective (denseFinAtomCoordinate N)
    (denseFinAtomCoordinate_injective N) circularComplexGaussian

def publishedGinibreModel (N : ℕ) [NeZero N] :
    RandomMatrixModelV3 N (ZMod N × ZMod N → ℂ) ℂ
      (cyclicAtomLaw N circularComplexGaussian) circularComplexGaussian :=
  denseV3Model (NeZero.pos N) (fun ω i j => denseFinAtoms N ω (i, j)) id
    circularComplexGaussian_publishedMoments
    (independentAtomCopies21_of_jointLaw _ _ _ (denseFinAtoms_measurePreserving N))

theorem publishedGinibreModel_matrix (N : ℕ) [NeZero N] (ω : ZMod N × ZMod N → ℂ) :
    (publishedGinibreModel N).matrix ω =
      (ginibreMatrix N ω).submatrix (ZMod.finEquiv N) (ZMod.finEquiv N) := by
  ext i j
  simp [publishedGinibreModel, denseV3Model, denseFinAtoms, denseFinAtomCoordinate,
    ginibreMatrix, weightedCyclicMatrix, div_eq_mul_inv, mul_comm]

theorem publishedGinibreModel_bandwidth (N : ℕ) [NeZero N] :
    IsBandwidth (publishedGinibreModel N).profile (N : ℝ) :=
  denseVarianceProfile_isBandwidth (NeZero.pos N)

def gaussianSection3ComparisonConstant (comparisonConstant : ℝ) : ℝ :=
  max comparisonConstant
    (max 8 ((∫ z : ℂ, ‖z‖ ^ 3 ∂circularComplexGaussian) + BVH.complexGaussianThirdMomentConstant))

theorem gaussianSection3ComparisonConstant_ge_eight (comparisonConstant : ℝ) :
    8 ≤ gaussianSection3ComparisonConstant comparisonConstant :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem publishedGinibreModel_thirdMoment_bound (N : ℕ) [NeZero N] (comparisonConstant : ℝ) :
    BVH.atomThirdMoment (publishedGinibreModel N) + BVH.complexGaussianThirdMomentConstant ≤
      gaussianSection3ComparisonConstant comparisonConstant :=
  (le_max_right _ _).trans (le_max_right _ _)

end CircularLawSection6
