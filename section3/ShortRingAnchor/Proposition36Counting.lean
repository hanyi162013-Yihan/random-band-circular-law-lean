import ShortRingAnchor.Proposition36Concrete
import ShortRingAnchor.HermitizationCountingFromV3

/-!
# Proposition 3.6 with the Hermitization counting premise eliminated

The cyclic BBV comparison is used at both the horizontal bulk grid and the
vertical counting grid. This is the same external BBV theorem, at different
spectral parameters, not a new probability input. The all-cutoff counting
event and its constant 6 are constructed internally.
-/

noncomputable section
namespace ShortRingAnchor
open MeasureTheory ProbabilityTheory Filter Set Arxiv2410V3
open scoped Topology

/-- Manuscript Proposition 3.6 / (3.8): derive both Lemma 3.5 and the
Corollary 3.5 Hermitization count from the actual atom arrays and v3 BBV.
Theorem 3.1 and the two BC12 conclusions remain explicit in this endpoint. -/
theorem proposition36_cyclicShortRing_of_atom_copies_bbv_and_lsv
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
    (goodLSV : ℕ → Set Omega)
    (hLSV : Theorem31MinimumSingularValueInput hMpos mu
      (fun n => cyclicShortRingRandomMatrix (weights n) (hfit n) (ringEntry n)) z
      (sourceHardEdgeScale M W kappa) goodLSV)
    (hp : 0 < p)
    (hBC12Negative : BC12GinibreNegativeMomentTightness mu p
      (shiftedSingularValueProcess (normalizedDenseMatrixProcess denseAtom) z))
    (hBC12Full : ConvergesInProbability mu
      (fun n sample => normalizedShiftLogDet (normalizedDenseMatrixProcess denseAtom n sample) z)
      (circularLogPotential z)) :
    Proposition36SequenceConclusion mu M
      (fun n => cyclicShortRingRandomMatrix (weights n) (hfit n) (ringEntry n)) z := by
  obtain ⟨goodCount, hCount⟩ := hermitizationAllCutoffsCountingInput_cyclic
    weights hfit hMpos hM ringEntry atomA hatomA hcopiesA z
    ((sourceV3MomentBudget_ge_eight atomA atomG).trans (le_max_right comparisonConstant _))
    hparam.2.2.1
    ((sourceV3MomentBudget_ge_left atomA atomG).trans (le_max_right comparisonConstant _))
    (fun n v hv => bbvA n (spectralParameter 0 v) (by simpa [spectralParameter] using hv))
  apply proposition36_cyclicShortRing_of_atom_copies_and_bbv weights hfit
    ringEntry denseAtom atomA atomG hatomA hatomG hcopiesA hcopiesG hDensityG
    z comparisonConstant omega chi kappa tau K 6 p R homega hparam hMpos hM hW hband
    hKdom (by norm_num) hRtop hR ?_ bbvG goodLSV goodCount hLSV hCount hp
    hBC12Negative hBC12Full
  intro n u
  apply bbvA n
  have hn : (0 : ℝ) < M n := by exact_mod_cast hMpos n
  simpa [spectralParameter, localBulkHeight] using
    Real.rpow_pos_of_pos hn (-(localBulkEffectiveExponent (v3BandwidthExponent omega / 2) / 16))

end ShortRingAnchor

