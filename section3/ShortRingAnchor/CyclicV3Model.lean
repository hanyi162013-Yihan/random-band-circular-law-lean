import ShortRingAnchor.CyclicVarianceProfile
import ShortRingAnchor.IndependentConstantExtension
import ShortRingAnchor.IndependentAtomCopies

/-!
# Manuscript (3.1) as an actual v3 random-matrix model

The active entries are reindexed independent scaled atoms. Off-band entries
are deterministic zero; their independence and laws are proved, not assumed.
-/

noncomputable section
namespace ShortRingAnchor
open MeasureTheory ProbabilityTheory Arxiv2410V3

/-- Manuscript (3.1) / v3 Proposition 3.4: cyclic placement preserves entry independence. -/
theorem cyclicShortRingRandomMatrix_entries_independent
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
    {M W : ℕ} {c0 C0 : ℝ} (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 ≤ M) (entry : Omega → Fin M → BandOffset W → ℂ)
    (hind : iIndepFun (fun is : Fin M × BandOffset W =>
      fun sample => entry sample is.1 is.2) mu) :
    iIndepFun (fun ij : Fin M × Fin M =>
      fun sample => cyclicShortRingRandomMatrix weights hfit entry sample ij.1 ij.2) mu := by
  classical
  let p : Fin M × Fin M → Prop := fun ij => ∃ s, cyclicColumn hfit ij.1 s = ij.2
  let place : Fin M × BandOffset W → Subtype p := fun is =>
    ⟨(is.1, cyclicColumn hfit is.1 is.2), ⟨is.2, rfl⟩⟩
  have hplace : Function.Surjective place := by
    rintro ⟨⟨i, j⟩, s, hs⟩
    refine ⟨(i, s), ?_⟩
    apply Subtype.ext
    change (i, cyclicColumn hfit i s) = (i, j)
    rw [hs]
  apply iIndepFun_of_constant_outside _ p (fun _ => 0)
  · apply iIndepFun.of_precomp hplace
    have h := hind.comp (fun is x => (Real.sqrt (weights.q is.2) : ℂ) * x)
      (fun _ => measurable_const.mul measurable_id)
    simpa only [Function.comp_def, place, cyclicShortRingRandomMatrix,
      cyclicShortRingMatrix_at] using h
  · intro ij hij sample
    exact cyclicShortRingMatrix_off_band weights hfit (entry sample) ij.1 ij.2 hij

/-- Manuscript (3.1) / v3 entry law, including all deterministic zero positions. -/
theorem cyclicShortRingRandomMatrix_entry_law
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {M W : ℕ} {c0 C0 : ℝ} (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 ≤ M) (entry : Omega → Fin M → BandOffset W → ℂ)
    (atom : OmegaXi → ℂ)
    (hlaw : ∀ i s, IdentDistrib (fun sample => entry sample i s) atom mu nu) (i j : Fin M) :
    IdentDistrib (fun sample => cyclicShortRingRandomMatrix weights hfit entry sample i j)
      (fun sample => ((cyclicVarianceProfile weights hfit).coefficient i j : ℂ) * atom sample)
      mu nu := by
  classical
  by_cases h : ∃ s, cyclicColumn hfit i s = j
  · obtain ⟨s, rfl⟩ := h
    simpa only [cyclicShortRingRandomMatrix, cyclicVarianceProfile,
      cyclicShortRingMatrix_at, cyclicVarianceCoefficient_at] using
      (hlaw i s).const_mul (Real.sqrt (weights.q s) : ℂ)
  · simpa only [cyclicShortRingRandomMatrix, cyclicVarianceProfile,
      cyclicShortRingMatrix_off_band weights hfit _ i j h,
      cyclicVarianceCoefficient_off_band weights hfit i j h, Complex.ofReal_zero, zero_mul]
      using identDistrib_zero_probability mu nu

/-- Construct the full v3 model directly from the manuscript's actual atom array (3.1).
No probability estimate or model-validity conclusion is supplied as a premise. -/
def cyclicV3Model
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {M W : ℕ} {c0 C0 : ℝ} (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 ≤ M) (entry : Omega → Fin M → BandOffset W → ℂ)
    (atom : OmegaXi → ℂ) (hatom : AtomMomentAssumption21 nu atom)
    (hcopies : IndependentAtomCopies21 mu nu atom
      (fun is : Fin M × BandOffset W => fun sample => entry sample is.1 is.2)) :
    RandomMatrixModelV3 M Omega OmegaXi mu nu where
  matrix := cyclicShortRingRandomMatrix weights hfit entry
  atom := atom
  profile := cyclicVarianceProfile weights hfit
  entry_measurable := cyclicShortRingRandomMatrix_entry_measurable weights hfit entry
    (fun i s => hcopies.measurable (i, s))
  entries_independent := cyclicShortRingRandomMatrix_entries_independent weights hfit entry
    hcopies.independent
  entry_law := cyclicShortRingRandomMatrix_entry_law weights hfit entry atom
    (fun i s => hcopies.law (i, s))
  atom_integrable := hatom.integrable
  atom_mean_zero := hatom.centered
  atom_variance_one := hatom.unitSecondMoment
  atom_third_moment_finite := hatom.thirdMomentIntegrable

end ShortRingAnchor
