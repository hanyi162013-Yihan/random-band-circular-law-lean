import ShortRingAnchor.CyclicV3Model
import ShortRingAnchor.DenseV3Model
import ShortRingAnchor.ConcreteBulkScales
import ShortRingAnchor.Lemma35FromV3

/-!
# Lemma 3.5 for the actual cyclic and normalized dense arrays

The input is the manuscript's independent atom data, not pre-constructed
v3 models. Matrix identities, exact bandwidths, the common moment budget,
and the polynomial bandwidth scale are all discharged here. Only the
centralized BBV comparison is an external theorem premise.
-/

noncomputable section
namespace ShortRingAnchor
open MeasureTheory ProbabilityTheory Filter Arxiv2410V3
open scoped Topology

variable {Omega OmegaXiA OmegaXiG : Type*}
  [MeasurableSpace Omega] [MeasurableSpace OmegaXiA] [MeasurableSpace OmegaXiG]
  {mu : Measure Omega} {nuA : Measure OmegaXiA} {nuG : Measure OmegaXiG}

/-- v3 (3.11): one explicit finite real budget for the two fixed atom third moments. -/
def sourceV3MomentBudget (nuA : Measure OmegaXiA) (nuG : Measure OmegaXiG)
    (atomA : OmegaXiA → ℂ) (atomG : OmegaXiG → ℂ) : ℝ :=
  max 8 (max (∫ x, ‖atomA x‖ ^ 3 ∂nuA) (∫ x, ‖atomG x‖ ^ 3 ∂nuG) +
    BVH.complexGaussianThirdMomentConstant)

/-- v3 (3.11): the common budget dominates the numerical constant. -/
theorem sourceV3MomentBudget_ge_eight (atomA : OmegaXiA → ℂ) (atomG : OmegaXiG → ℂ) :
    8 ≤ sourceV3MomentBudget nuA nuG atomA atomG := le_max_left _ _

/-- v3 (3.11): the common budget controls the cyclic atom and canonical Gaussian. -/
theorem sourceV3MomentBudget_ge_left (atomA : OmegaXiA → ℂ) (atomG : OmegaXiG → ℂ) :
    (∫ x, ‖atomA x‖ ^ 3 ∂nuA) + BVH.complexGaussianThirdMomentConstant ≤
      sourceV3MomentBudget nuA nuG atomA atomG := by
  have h := le_max_left (∫ x, ‖atomA x‖ ^ 3 ∂nuA) (∫ x, ‖atomG x‖ ^ 3 ∂nuG)
  have hb := le_max_right (8 : ℝ)
    (max (∫ x, ‖atomA x‖ ^ 3 ∂nuA) (∫ x, ‖atomG x‖ ^ 3 ∂nuG) +
      BVH.complexGaussianThirdMomentConstant)
  unfold sourceV3MomentBudget
  linarith

/-- v3 (3.11): the common budget controls the dense atom and canonical Gaussian. -/
theorem sourceV3MomentBudget_ge_right (atomA : OmegaXiA → ℂ) (atomG : OmegaXiG → ℂ) :
    (∫ x, ‖atomG x‖ ^ 3 ∂nuG) + BVH.complexGaussianThirdMomentConstant ≤
      sourceV3MomentBudget nuA nuG atomA atomG := by
  have h := le_max_right (∫ x, ‖atomA x‖ ^ 3 ∂nuA) (∫ x, ‖atomG x‖ ^ 3 ∂nuG)
  have hb := le_max_right (8 : ℝ)
    (max (∫ x, ‖atomA x‖ ^ 3 ∂nuA) (∫ x, ‖atomG x‖ ^ 3 ∂nuG) +
      BVH.complexGaussianThirdMomentConstant)
  unfold sourceV3MomentBudget
  linarith

/-- **Manuscript Lemma 3.5 / (3.11) for the actual arrays in (3.1).**
The only external comparison premises are `bbvA` and `bbvG`, two
instantiations of the same centralized BBV interface. All other inputs are
explicit atom/model data and the source bandwidth growth. The shift is
arbitrary and fixed; the cutoff can be any fixed nonnegative real number.
For `0 < beta <= 2`, one common CDF exponent is exactly `beta / 128`.
The arbitrary `comparisonConstant` allows any absolute constant in BBV;
it is enlarged by the explicit atom budget, never fixed to a guessed value.
-/
theorem lemma35LocalBulkComparisonInput_cyclic_dense
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nuA] [IsProbabilityMeasure nuG]
    {M W : ℕ → ℕ} {c0 C0 : ℝ}
    (weights : ∀ n, AdmissibleWeights (W n) c0 C0)
    (hfit : ∀ n, 2 * W n + 1 ≤ M n) (hMpos : ∀ n, 0 < M n)
    (ringEntry : ∀ n, Omega → Fin (M n) → BandOffset (W n) → ℂ)
    (denseAtom : ∀ n, Omega → Fin (M n) → Fin (M n) → ℂ)
    (atomA : OmegaXiA → ℂ) (atomG : OmegaXiG → ℂ)
    (hatomA : AtomMomentAssumption21 nuA atomA)
    (hatomG : AtomMomentAssumption21 nuG atomG)
    (hcopiesA : ∀ n, IndependentAtomCopies21 mu nuA atomA
      (fun is : Fin (M n) × BandOffset (W n) => fun sample => ringEntry n sample is.1 is.2))
    (hcopiesG : ∀ n, IndependentAtomCopies21 mu nuG atomG
      (fun ij : Fin (M n) × Fin (M n) => fun sample => denseAtom n sample ij.1 ij.2))
    (z : ℂ) (comparisonConstant : ℝ)
    {R beta : ℝ} (hR : 0 ≤ R) (hbeta : 0 < beta) (hbeta2 : beta ≤ 2)
    (hM : Tendsto M atTop atTop)
    (hband : ∀ n, (M n : ℝ) ^ beta ≤ (W n : ℝ))
    (bbvA : ∀ n u, CanonicalBBVAt
      (cyclicV3Model (weights n) (hfit n) (ringEntry n) atomA hatomA (hcopiesA n)) z
      (spectralParameter u (localBulkHeight (beta / 2) (M n)))
      (weights n).bandwidthParameter
      (max comparisonConstant (sourceV3MomentBudget nuA nuG atomA atomG)))
    (bbvG : ∀ n u, CanonicalBBVAt
      (denseV3Model (hMpos n) (denseAtom n) atomG hatomG (hcopiesG n)) z
      (spectralParameter u (localBulkHeight (beta / 2) (M n)))
      (M n) (max comparisonConstant (sourceV3MomentBudget nuA nuG atomA atomG))) :
    Lemma35LocalBulkComparisonInput mu
      (shiftedSingularValueProcess
        (fun n => cyclicShortRingRandomMatrix (weights n) (hfit n) (ringEntry n)) z)
      (shiftedSingularValueProcess (normalizedDenseMatrixProcess denseAtom) z)
      R (fun n => (M n : ℝ) ^ (-(beta / 128))) := by
  let modelA := fun n => cyclicV3Model (weights n) (hfit n) (ringEntry n)
    atomA hatomA (hcopiesA n)
  let modelG := fun n => denseV3Model (hMpos n) (denseAtom n) atomG hatomG (hcopiesG n)
  have h := lemma35LocalBulkComparisonInput_of_v3_models hM modelA modelG z hR
    ((sourceV3MomentBudget_ge_eight atomA atomG).trans (le_max_right comparisonConstant _))
    (by positivity : 0 < beta / 2)
    (fun n => (weights n).bandwidthParameter) (fun n => (M n : ℝ))
    (fun n => cyclicVarianceProfile_isBandwidth (weights n) (hfit n))
    (fun n => denseVarianceProfile_isBandwidth (hMpos n))
    (eventually_cyclic_bandwidth_ge_half_power weights hM hbeta hband)
    (Eventually.of_forall (fun n => dense_bandwidth_ge_half_power (hMpos n) hbeta2))
    (fun _ => (sourceV3MomentBudget_ge_left atomA atomG).trans
      (le_max_right comparisonConstant _))
    (fun _ => (sourceV3MomentBudget_ge_right atomA atomG).trans
      (le_max_right comparisonConstant _)) bbvA bbvG
  unfold normalizedDenseMatrixProcess
  simpa only [localBulkRateExponent_half_eq hbeta2, modelA, modelG,
    cyclicV3Model, denseV3Model, normalizedDenseMatrixProcess] using h

end ShortRingAnchor
