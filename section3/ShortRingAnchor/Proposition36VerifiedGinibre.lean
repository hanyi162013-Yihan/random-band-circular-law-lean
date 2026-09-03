import ShortRingAnchor.BC12.GaussianMatrixLawBridge
import ShortRingAnchor.BC12.GinibreNegativeMoments
import ShortRingAnchor.Proposition36PublishedTheorem31

/-!
# Proposition 3.6 without BC12 hypotheses

The Gaussian lower edge, negative-moment tightness, exact correlation
formulas, and full logarithmic-potential convergence are constructed.
The published short-ring Theorem 3.1 remains connected as before.
The explicit geometric Brascamp--Lieb premise in its real branch and
the BBV comparisons are not claimed to be discharged by this integration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Arxiv2410V3
open scoped Topology
namespace ShortRingAnchor

local instance (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _
local instance (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩

/-- **Proposition 3.6 / (3.8), with no BC12 theorem or formula premise.**
The retained dense BBV comparison is available at all positive heights:
the proved negative-moment shortcut also uses the dense counting height.
`hGinibre` specifies a distribution, not a probabilistic estimate. -/
theorem proposition36_cyclicShortRing_withoutBC12
    {Omega OmegaXiA OmegaXiG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXiA] [MeasurableSpace OmegaXiG]
    {mu : Measure Omega} {nuA : Measure OmegaXiA} {nuG : Measure OmegaXiG}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nuA] [IsProbabilityMeasure nuG]
    {M W : ℕ → ℕ} [∀ n, Nonempty (Fin (M n))] {c0 C0 : ℝ}
    (weights : ∀ n, AdmissibleWeights (W n) c0 C0)
    (hfit : ∀ n, 2 * W n + 1 ≤ M n)
    (ringEntry : ∀ n, Omega → Fin (M n) → BandOffset (W n) → ℂ)
    (denseAtom : ∀ n, Omega → Fin (M n) → Fin (M n) → ℂ)
    (atomA : OmegaXiA → ℂ) (atomG : OmegaXiG → ℂ)
    (hatomA : AtomMomentAssumption21 nuA atomA)
    (hatomG : AtomMomentAssumption21 nuG atomG)
    (hcopiesA : ∀ n, IndependentAtomCopies21 mu nuA atomA
      (fun is : Fin (M n) × BandOffset (W n) => fun sample => ringEntry n sample is.1 is.2))
    (hcopiesG : ∀ n, IndependentAtomCopies21 mu nuG atomG
      (fun ij : Fin (M n) × Fin (M n) => fun sample => denseAtom n sample ij.1 ij.2))
    (hGinibre : ∀ n, HasLaw (normalizedDenseMatrixProcess denseAtom n)
      (BC12.normalizedGinibreLaw (M n)) mu)
    (hDensityA : AtomDensityAlternative21 nuA atomA)
    (hGBL : LivshytsProjectionFormalization.RealFiniteGeometricBrascampLieb)
    (hDensityG : AtomDensityAlternative21 nuG atomG)
    (z : ℂ) (comparisonConstant omega chi kappa tau K : ℝ) (R : ℕ → ℝ)
    (homega : 0 < omega ∧ omega < 1 / 9)
    (hparam : HardEdgeAdmissible (v3BandwidthExponent omega) chi kappa tau)
    (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop) (hW : Tendsto W atTop atTop)
    (hband : ∀ n, (M n : ℝ) ^ v3BandwidthExponent omega ≤ (W n : ℝ))
    (hKdom : C0 ^ (1 / 8 : ℝ) ≤ K)
    (hRtop : Tendsto R atTop atTop) (hR : ∀ r, Real.sqrt (Real.exp 1) < R r)
    (bbvA : ∀ n eta, 0 < eta.im → CanonicalBBVAt
      (cyclicV3Model (weights n) (hfit n) (ringEntry n) atomA hatomA (hcopiesA n)) z
      eta (weights n).bandwidthParameter
      (max comparisonConstant (sourceV3MomentBudget nuA nuG atomA atomG)))
    (bbvG : ∀ n eta, 0 < eta.im → CanonicalBBVAt
      (denseV3Model (hMpos n) (denseAtom n) atomG hatomG (hcopiesG n)) z eta
      (M n) (max comparisonConstant (sourceV3MomentBudget nuA nuG atomA atomG))) :
    Proposition36SequenceConclusion mu M
      (fun n => cyclicShortRingRandomMatrix (weights n) (hfit n) (ringEntry n)) z := by
  let C := max comparisonConstant (sourceV3MomentBudget nuA nuG atomA atomG)
  have hC : 8 ≤ C := (sourceV3MomentBudget_ge_eight atomA atomG).trans
    (le_max_right comparisonConstant _)
  have hthird : (∫ x, ‖atomG x‖ ^ 3 ∂nuG) + BVH.complexGaussianThirdMomentConstant ≤ C :=
    (sourceV3MomentBudget_ge_right atomA atomG).trans (le_max_right comparisonConstant _)
  have hnegative := BC12.negativeMomentTightness_normalizedDenseMatrixProcess
    hMpos hM denseAtom atomG hatomG hcopiesG hGinibre z hC hthird
    (fun n v hv => bbvG n (spectralParameter 0 v) (by simpa [spectralParameter] using hv))
  have hfull := BC12.ginibre_logdet_convergesInProbability_of_ginibreLaw
    hMpos hM (normalizedDenseMatrixProcess denseAtom) hGinibre z
  apply proposition36_cyclicShortRing_from_published_theorem31 weights hfit ringEntry denseAtom
    atomA atomG hatomA hatomG hcopiesA hcopiesG hDensityA hGBL hDensityG z comparisonConstant
    omega chi kappa tau K (1 / 128) R homega hparam hMpos hM hW hband hKdom hRtop hR
    bbvA _ (by norm_num) hnegative hfull
  intro n u
  apply bbvG n
  simpa [spectralParameter, localBulkHeight] using
    Real.rpow_pos_of_pos (by exact_mod_cast hMpos n : (0 : ℝ) < M n)
      (-(localBulkEffectiveExponent (v3BandwidthExponent omega / 2) / 16))

end ShortRingAnchor
