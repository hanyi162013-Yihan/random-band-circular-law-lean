import ShortRingAnchor.Proposition36Models
import ShortRingAnchor.Lemma35Concrete
import ShortRingAnchor.AtomDensityTransport

/-!
# Proposition 3.6 with Lemma 3.5 derived for the actual arrays

This source-facing endpoint has no `hBulk`, no supplied v3 models, no
supplied row moments, and no assumed bandwidth identification. The two BBV
premises stay explicit. The separate hard-edge and BC12 premises have not
been silently discharged by this adapter.
-/

noncomputable section
namespace ShortRingAnchor
open MeasureTheory ProbabilityTheory Filter Set Arxiv2410V3
open scoped Topology

/-- **Proposition 3.6, formula (3.8), with the Lemma 3.5 premise eliminated.**

Actual independent atom arrays supply the cyclic and dense v3 models.
The local comparison uses the common exponent `(8/9 + omega)/128` at
every fixed cutoff, for an arbitrary fixed complex shift. Its BBV premises
are explicit specializations of the centralized external interface.
The separate `hLSV`, `hCount`, `hBC12Negative` and `hBC12Full` conclusions
remain conditional inputs; none is asserted by this theorem.
-/
theorem proposition36_cyclicShortRing_of_atom_copies_and_bbv
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
    (hDensityG : AtomDensityAlternative21 nuG atomG)
    (z : ℂ) (comparisonConstant omega chi kappa tau K C35 p : ℝ) (R : ℕ → ℝ)
    (homega : 0 < omega ∧ omega < 1 / 9)
    (hparam : HardEdgeAdmissible (v3BandwidthExponent omega) chi kappa tau)
    (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop) (hW : Tendsto W atTop atTop)
    (hband : ∀ n, (M n : ℝ) ^ v3BandwidthExponent omega ≤ (W n : ℝ))
    (hKdom : C0 ^ (1 / 8 : ℝ) ≤ K) (hC35 : 0 ≤ C35)
    (hRtop : Tendsto R atTop atTop) (hR : ∀ r, Real.sqrt (Real.exp 1) < R r)
    (bbvA : ∀ n u, CanonicalBBVAt
      (cyclicV3Model (weights n) (hfit n) (ringEntry n) atomA hatomA (hcopiesA n)) z
      (spectralParameter u (localBulkHeight (v3BandwidthExponent omega / 2) (M n)))
      (weights n).bandwidthParameter
      (max comparisonConstant (sourceV3MomentBudget nuA nuG atomA atomG)))
    (bbvG : ∀ n u, CanonicalBBVAt
      (denseV3Model (hMpos n) (denseAtom n) atomG hatomG (hcopiesG n)) z
      (spectralParameter u (localBulkHeight (v3BandwidthExponent omega / 2) (M n)))
      (M n) (max comparisonConstant (sourceV3MomentBudget nuA nuG atomA atomG)))
    (goodLSV goodCount : ℕ → Set Omega)
    (hLSV : Theorem31MinimumSingularValueInput hMpos mu
      (fun n => cyclicShortRingRandomMatrix (weights n) (hfit n) (ringEntry n)) z
      (sourceHardEdgeScale M W kappa) goodLSV)
    (hCount : HermitizationAllCutoffsCountingInput mu
      (fun n => cyclicShortRingRandomMatrix (weights n) (hfit n) (ringEntry n)) z
      (fun n => manuscriptHardEdgeCutoff (weights n) (M n) tau) (fun _ => C35) goodCount)
    (hp : 0 < p)
    (hBC12Negative : BC12GinibreNegativeMomentTightness mu p
      (shiftedSingularValueProcess (normalizedDenseMatrixProcess denseAtom) z))
    (hBC12Full : ConvergesInProbability mu
      (fun n sample => normalizedShiftLogDet (normalizedDenseMatrixProcess denseAtom n sample) z)
      (circularLogPotential z)) :
    Proposition36SequenceConclusion mu M
      (fun n => cyclicShortRingRandomMatrix (weights n) (hfit n) (ringEntry n)) z := by
  have hbeta : 0 < v3BandwidthExponent omega := by
    unfold v3BandwidthExponent
    linarith [homega.1]
  have hbeta2 : v3BandwidthExponent omega ≤ 2 := by
    unfold v3BandwidthExponent
    linarith [homega.2]
  exact proposition36_cyclicShortRing_of_source_scales weights hfit ringEntry denseAtom z
    omega chi kappa tau K C35 p R (fun _ => v3BandwidthExponent omega / 128)
    homega hparam hMpos hM hW hband hKdom hC35 hRtop hR
    (fun _ => by positivity)
    (fun n => (hcopiesG n).independent)
    (fun n i j => AtomDensityAlternative21.of_identDistrib ((hcopiesG n).law (i, j)) hDensityG)
    goodLSV goodCount hLSV hCount
    (fun r => by
      unfold sourceBulkRate
      exact lemma35LocalBulkComparisonInput_cyclic_dense weights hfit hMpos
        ringEntry denseAtom atomA atomG hatomA hatomG hcopiesA hcopiesG z comparisonConstant
        ((Real.sqrt_nonneg _).trans (hR r).le) hbeta hbeta2 hM hband bbvA bbvG)
    hp hBC12Negative hBC12Full
    (ringEntryMomentCopies21_of_independentAtomCopies ringEntry hatomA hcopiesA)
    (denseAtomMomentCopies21_of_independentAtomCopies denseAtom hatomG hcopiesG)

end ShortRingAnchor
