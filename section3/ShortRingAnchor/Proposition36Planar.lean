import ShortRingAnchor.Proposition36Counting
import ShortRingAnchor.Theorem31CyclicPlanar

/-!
# Proposition 3.6 with the published Theorem 3.1 and Hermitization count connected

The copied Theorem 3.1 is applied to the actual cyclic matrix law, without
an external least-value or geometric projection premise. BBV and the two
BC12 conclusions remain explicit inputs; no `hLSV` or `hCount` is supplied.
-/

noncomputable section
namespace ShortRingAnchor
open MeasureTheory ProbabilityTheory Filter Set Arxiv2410V3
open scoped Topology

/-- Manuscript Proposition 3.6 / (3.8), using the copied Theorem 3.1,
the internally derived Corollary 3.5 count, and the actual Lemma 3.5 comparison. -/
theorem proposition36_cyclicShortRing_planar_from_published_theorem31
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
    (hDensityA : HasBoundedDensityWithRespectTo (Measure.map atomA nuA) (volume : Measure ℂ))
    (hDensityG : AtomDensityAlternative21 nuG atomG)
    (z : ℂ) (comparisonConstant omega chi kappa tau K p : ℝ) (R : ℕ → ℝ)
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
    (bbvG : ∀ n u, CanonicalBBVAt
      (denseV3Model (hMpos n) (denseAtom n) atomG hatomG (hcopiesG n)) z
      (spectralParameter u (localBulkHeight (v3BandwidthExponent omega / 2) (M n)))
      (M n) (max comparisonConstant (sourceV3MomentBudget nuA nuG atomA atomG)))
    (hp : 0 < p)
    (hBC12Negative : BC12GinibreNegativeMomentTightness mu p
      (shiftedSingularValueProcess (normalizedDenseMatrixProcess denseAtom) z))
    (hBC12Full : ConvergesInProbability mu
      (fun n sample => normalizedShiftLogDet (normalizedDenseMatrixProcess denseAtom n sample) z)
      (circularLogPotential z)) :
    Proposition36SequenceConclusion mu M
      (fun n => cyclicShortRingRandomMatrix (weights n) (hfit n) (ringEntry n)) z := by
  have hbeta : v3BandwidthExponent omega ≤ 1 := by
    unfold v3BandwidthExponent
    linarith [homega.2]
  obtain ⟨goodLSV, hLSV⟩ := theorem31MinimumSingularValueInput_cyclic_planar weights hfit hMpos hM
    ringEntry atomA hatomA hcopiesA hDensityA
    hparam.1 hparam.2.2.2.1 hbeta hparam.2.1 hband z
  exact proposition36_cyclicShortRing_of_atom_copies_bbv_and_lsv weights hfit ringEntry denseAtom
    atomA atomG hatomA hatomG hcopiesA hcopiesG hDensityG z comparisonConstant
    omega chi kappa tau K p R homega hparam hMpos hM hW hband hKdom hRtop hR
    bbvA bbvG goodLSV hLSV hp hBC12Negative hBC12Full

end ShortRingAnchor

