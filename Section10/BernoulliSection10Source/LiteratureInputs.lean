import BernoulliSection10Source.GaussianReferenceModel
import ShortRingAnchor.V3PointwiseProbability
import ShortRingAnchor.GinibreLowerEdge

/-!
# Explicit, accepted literature boundary

These are named hypotheses, not axioms or proved literature theorems.
`BBVComparisonInput` is precisely the Gaussian-to-free comparison used by
the repository's Section 3 proofs (including its canonical free transform).
`BC12GinibreInput` concerns only the literal normalized circular Ginibre
ensemble. Neither hypothesis contains a Section 10 conclusion, a non-Gaussian
LSV estimate, a counting certificate, or an arbitrary comparison ensemble.

The real endpoint additionally displays `RealFiniteGeometricBrascampLieb`.
All three retained external results were explicitly accepted by the user.
-/

open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section
set_option autoImplicit false
namespace BernoulliSection10Source
open BernoulliSection10.SourceInputs ShortRingAnchor Arxiv2410V3

/-- A universal BBV constant for the actual canonical Gaussian companions
of the admissible Section 3 models. All spaces needed here lie in `Type`. -/
def BBVComparisonInput : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Ω E : Type) [MeasurableSpace Ω] [MeasurableSpace E]
      (P : Measure Ω) (μ : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
      (N : ℕ), 0 < N →
      ∀ (model : RandomMatrixModelV3 N Ω E P μ) (B : ℝ),
        IsBandwidth model.profile B →
        ∀ z η : ℂ, 0 < η.im → CanonicalBBVAt model z η B C

theorem canonicalBBVAt_mono
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {μ : Measure E} [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    {N : ℕ} {model : RandomMatrixModelV3 N Ω E P μ} {B C D : ℝ} {z η : ℂ}
    (h : CanonicalBBVAt model z η B C) (hB : 0 < B) (hη : 0 < η.im)
    (hCD : C ≤ D) : CanonicalBBVAt model z η B D :=
  ⟨h.estimate.trans (div_le_div_of_nonneg_right hCD (by positivity))⟩

abbrev GaussianSequence := ℕ → ℝ × ℝ

def gaussianSequenceLaw : Measure GaussianSequence :=
  Measure.infinitePi fun _ : ℕ => circularGaussianPairLaw

instance : IsProbabilityMeasure gaussianSequenceLaw := by
  unfold gaussianSequenceLaw
  infer_instance

def ginibreOnSequence (N : ℕ) (ω : GaussianSequence) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => circularGaussianAtom (ω (squareAtomIndex i j)) / (Real.sqrt (N : ℝ) : ℂ)

/-- BC12 only for independent `N(0,1/2) + i N(0,1/2)` entries, divided
by `sqrt N`. Its nonsingularity and moment assumptions are proved separately. -/
def BC12GinibreInput : Prop :=
  ∀ (N : ℕ → ℕ), (∀ n, 0 < N n) → Tendsto N atTop atTop →
    ∀ z : ℂ, ∃ p : ℝ, 0 < p ∧
      BC12GinibreNegativeMomentTightness gaussianSequenceLaw p
        (shiftedSingularValueProcess (fun n => ginibreOnSequence (N n)) z) ∧
      ConvergesInProbability gaussianSequenceLaw
        (fun n ω => normalizedShiftLogDet (ginibreOnSequence (N n) ω) z)
        (circularLogPotential z)

theorem sampleLaw_snd_event {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (s : Set GaussianSequence) :
    sampleLaw μ {ω | ω.2 ∈ s} = gaussianSequenceLaw s := by
  have heq : {ω : SampleSpace E | ω.2 ∈ s} = Set.univ ×ˢ s := by
    ext ω
    simp
  rw [heq, sampleLaw, Measure.prod_prod, measure_univ, one_mul]
  rfl

/-- Adding the independent non-Gaussian coordinate array changes none of
the Gaussian tail probabilities. This law transport is proved, not assumed. -/
theorem bc12_on_sampleLaw
    (hBC12 : BC12GinibreInput) {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hNtop : Tendsto N atTop atTop) (z : ℂ) :
    ∃ p : ℝ, 0 < p ∧
      BC12GinibreNegativeMomentTightness (sampleLaw μ) p
        (shiftedSingularValueProcess (fun n => actualGinibre (E := E) (N n)) z) ∧
      ConvergesInProbability (sampleLaw μ)
        (fun n ω => normalizedShiftLogDet (actualGinibre (N n) ω) z)
        (circularLogPotential z) := by
  obtain ⟨p, hp, hneg, hlog⟩ := hBC12 N hN hNtop z
  refine ⟨p, hp, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨C, hC, htail⟩ := hneg δ hδ
    refine ⟨C, hC, ?_⟩
    filter_upwards [htail] with n hn
    have hevent : (sampleLaw μ) {ω | C < ‖normalizedNegativeMoment p
        (shiftedSingularValueProcess (fun n => actualGinibre (E := E) (N n)) z n ω)‖} =
        gaussianSequenceLaw {ω | C < ‖normalizedNegativeMoment p
          (shiftedSingularValueProcess (fun n => ginibreOnSequence (N n)) z n ω)‖} :=
      sampleLaw_snd_event μ {ω | C < ‖normalizedNegativeMoment p
        (shiftedSingularValueProcess (fun n => ginibreOnSequence (N n)) z n ω)‖}
    exact hevent.trans_lt hn
  · rw [convergesInProbability_iff_norm] at hlog ⊢
    intro ε hε
    exact (hlog ε hε).congr fun n =>
      (sampleLaw_snd_event μ {ω | ε ≤
        ‖normalizedShiftLogDet (ginibreOnSequence (N n) ω) z - circularLogPotential z‖}).symm

end BernoulliSection10Source
