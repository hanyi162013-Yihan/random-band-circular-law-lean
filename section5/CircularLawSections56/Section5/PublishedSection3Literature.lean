import CircularLawSections56.Section5.PublishedSection3ConcreteSampling

/-! # The only retained literature inputs for concrete Section 5 anchors

These are hypotheses, not axioms. BBV concerns the canonical companion and
BC12 only the literal circular Gaussian matrix divided by sqrt N. Neither
contains a Section 5 conclusion, sampling certificate, or non-Gaussian LSV.
-/

open MeasureTheory Filter Topology ShortRingAnchor Arxiv2410V3
noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5.PublishedSection3Concrete

def BBVComparisonInput : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Ω E : Type) [MeasurableSpace Ω] [MeasurableSpace E]
      (P : Measure Ω) (ν : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
      (N : ℕ), 0 < N →
      ∀ (model : RandomMatrixModelV3 N Ω E P ν) (B : ℝ),
        IsBandwidth model.profile B →
        ∀ z η : ℂ, 0 < η.im → CanonicalBBVAt model z η B C

theorem canonicalBBVAt_mono
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {ν : Measure E} [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {N : ℕ} {model : RandomMatrixModelV3 N Ω E P ν} {B C D : ℝ} {z η : ℂ}
    (h : CanonicalBBVAt model z η B C) (hB : 0 < B) (hη : 0 < η.im)
    (hCD : C ≤ D) : CanonicalBBVAt model z η B D :=
  ⟨h.estimate.trans (div_le_div_of_nonneg_right hCD (by positivity))⟩

def BC12GinibreInput : Prop :=
  ∀ (N : ℕ → ℕ), (∀ n, 0 < N n) → Tendsto N atTop atTop →
    ∀ z : ℂ, ∃ p : ℝ, 0 < p ∧
      BC12GinibreNegativeMomentTightness gaussianSequenceLaw p
        (shiftedSingularValueProcess (fun n => ginibreOnSequence (N n)) z) ∧
      ConvergesInProbability gaussianSequenceLaw
        (fun n ω => normalizedShiftLogDet (ginibreOnSequence (N n) ω) z)
        (circularLogPotential z)

theorem sampleLaw_snd_event
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (s : Set (ℕ → ℂ)) :
    sampleLaw ν {ω | ω.2 ∈ s} = gaussianSequenceLaw s := by
  have heq : {ω : Sample | ω.2 ∈ s} = Set.univ ×ˢ s := by
    ext ω
    simp
  rw [heq, sampleLaw, Measure.prod_prod, measure_univ, one_mul]

theorem bc12_on_sampleLaw
    (hBC12 : BC12GinibreInput) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hNtop : Tendsto N atTop atTop) (z : ℂ) :
    ∃ p : ℝ, 0 < p ∧
      BC12GinibreNegativeMomentTightness (sampleLaw ν) p
        (shiftedSingularValueProcess (fun n => actualGinibre (N n)) z) ∧
      ConvergesInProbability (sampleLaw ν)
        (fun n ω => normalizedShiftLogDet (actualGinibre (N n) ω) z)
        (circularLogPotential z) := by
  obtain ⟨p, hp, hneg, hlog⟩ := hBC12 N hN hNtop z
  refine ⟨p, hp, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨C, hC, htail⟩ := hneg δ hδ
    refine ⟨C, hC, ?_⟩
    filter_upwards [htail] with n hn
    exact (sampleLaw_snd_event ν {ω | C < ‖normalizedNegativeMoment p
      (shiftedSingularValueProcess (fun n => ginibreOnSequence (N n)) z n ω)‖}).trans_lt hn
  · rw [convergesInProbability_iff_norm] at hlog ⊢
    intro ε hε
    exact (hlog ε hε).congr fun n =>
      (sampleLaw_snd_event ν {ω | ε ≤
        ‖normalizedShiftLogDet (ginibreOnSequence (N n) ω) z - circularLogPotential z‖}).symm

end CircularLawSections56.Section5.PublishedSection3Concrete
