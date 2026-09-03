import BernoulliSection10Source.IIDModels
import BernoulliSection10Source.DensityRepresentative
import ShortRingAnchor.AtomDensityTransport
import ShortRingAnchor.DensityNonsingularity

/-! # The literal circular Ginibre reference as a proved Section 3 model -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace BernoulliSection10Source
open BernoulliSection10.SourceInputs ShortRingAnchor Arxiv2410V3

theorem gaussianAtomMoments :
    AtomMomentAssumption21 circularGaussianPairLaw circularGaussianAtom :=
  ⟨measurable_circularGaussianAtom.stronglyMeasurable,
    circularGaussianAtom_centered, circularGaussianAtom_second_moment,
    circularGaussianAtom_third_integrable⟩

theorem gaussianAtomDensity :
    AtomDensityAlternative21 circularGaussianPairLaw circularGaussianAtom := by
  letI : IsProbabilityMeasure (Measure.map circularGaussianAtom circularGaussianPairLaw) :=
    Measure.isProbabilityMeasure_map measurable_circularGaussianAtom.aemeasurable
  apply AtomDensityAlternative21.complex
  exact boundedDensityOfMeasureLe (L := 1) (by simpa using circularGaussianAtom_law_le_volume)

def gaussianEntry {E : Type*} (N : ℕ) (ω : SampleSpace E) (i j : Fin N) : ℂ :=
  circularGaussianAtom (ω.2 (squareAtomIndex i j))

theorem gaussianEntryCopies
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (N : ℕ) :
    IndependentAtomCopies21 (sampleLaw μ) circularGaussianPairLaw circularGaussianAtom
      (fun ij : Fin N × Fin N => fun ω => gaussianEntry N ω ij.1 ij.2) := by
  have hselect : MeasurePreserving
      (fun ω : ℕ → ℝ × ℝ => fun ij : Fin N × Fin N => ω (squareAtomIndex ij.1 ij.2))
      (Measure.infinitePi fun _ : ℕ => circularGaussianPairLaw)
      (Measure.pi fun _ : Fin N × Fin N => circularGaussianPairLaw) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.map_infinitePi_infinitePi_of_inj
        (P := fun _ : ℕ => circularGaussianPairLaw) (squareAtomIndex_injective N))
  exact copies_of_product_sampling _
    (hselect.comp (measurePreserving_snd
      (μ := Measure.infinitePi fun _ : ℕ => μ)
      (ν := Measure.infinitePi fun _ : ℕ => circularGaussianPairLaw)))
    circularGaussianAtom measurable_circularGaussianAtom

/-- Entries are exactly `(g₁ + i g₂) / sqrt N`, with independent
`N(0,1/2)` coordinates, not an arbitrary dense ensemble. -/
def gaussianV3Model {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N) :
    RandomMatrixModelV3 N (SampleSpace E) (ℝ × ℝ) (sampleLaw μ) circularGaussianPairLaw :=
  denseV3Model hN (gaussianEntry N) circularGaussianAtom gaussianAtomMoments
    (gaussianEntryCopies μ N)

def actualGinibre {E : Type*} (N : ℕ) (ω : SampleSpace E) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => gaussianEntry N ω i j / (Real.sqrt (N : ℝ) : ℂ)

theorem gaussianV3Model_matrix {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N) :
    (gaussianV3Model μ hN).matrix = actualGinibre N := rfl

theorem gaussianV3Model_bandwidth {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N) :
    IsBandwidth (gaussianV3Model μ hN).profile (N : ℝ) :=
  denseVarianceProfile_isBandwidth hN

theorem actualGinibre_row_moments
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) :
    CenteredMatrixRowSecondMomentInputs (sampleLaw μ)
      (fun n => actualGinibre (E := E) (N n)) 1 := by
  letI (n : ℕ) : Nonempty (Fin (N n)) := ⟨⟨0, hN n⟩⟩
  exact (denseAtomMomentCopies21_of_independentAtomCopies
    (fun n => gaussianEntry (E := E) (N n)) gaussianAtomMoments
    (fun n => gaussianEntryCopies μ (N n))).centeredMatrixRowSecondMomentInputs _

/-- Nonsingularity is proved from the actual independent Gaussian entries;
it is not bundled into the retained BC12 input. -/
theorem actualGinibre_nonsingular
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (z : ℂ) :
    ShiftedNonsingularInProbability (sampleLaw μ)
      (fun n => actualGinibre (E := E) (N n)) z := by
  exact normalizedDense_shiftedNonsingularInProbability_of_independent_density
    (fun n => gaussianEntry (E := E) (N n)) hN
    (fun n i j => ((gaussianEntryCopies μ (N n)).measurable (i, j)).aemeasurable)
    (fun n => (gaussianEntryCopies μ (N n)).independent)
    (fun n i j => AtomDensityAlternative21.of_identDistrib
      ((gaussianEntryCopies μ (N n)).law (i, j)) gaussianAtomDensity) z

end BernoulliSection10Source
