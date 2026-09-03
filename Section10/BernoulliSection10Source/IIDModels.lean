import BernoulliSection10.VarianceProfiles
import BernoulliSection10.GaussianReferenceFacts
import ShortRingAnchor.CyclicPlanarHighBandModel
import ShortRingAnchor.DenseV3Model

/-!
# Construct the actual IID models consumed by Section 3

All fields in these constructions are model data or proofs of the
specified product laws, not random-matrix estimates.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
set_option autoImplicit false
namespace BernoulliSection10Source
open BernoulliSection10 BernoulliSection10.SourceInputs ShortRingAnchor Arxiv2410V3

set_option maxHeartbeats 1200000

abbrev SampleSpace (E : Type*) := (ℕ → E) × (ℕ → ℝ × ℝ)

def sampleLaw {E : Type*} [MeasurableSpace E] (μ : Measure E) :
    Measure (SampleSpace E) :=
  (Measure.infinitePi fun _ : ℕ => μ).prod
    (Measure.infinitePi fun _ : ℕ => circularGaussianPairLaw)

instance {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (sampleLaw μ) := by
  unfold sampleLaw
  infer_instance

/-- A finite selection of distinct IID coordinates has its literal product law. -/
theorem selectedCoordinates_measurePreserving
    {E I : Type*} [MeasurableSpace E] [Fintype I]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (idx : I → ℕ) (hinj : Function.Injective idx) :
    MeasurePreserving (fun ω : SampleSpace E => fun i => ω.1 (idx i))
      (sampleLaw μ) (Measure.pi fun _ : I => μ) := by
  have hselect : MeasurePreserving (fun ω : ℕ → E => fun i => ω (idx i))
      (Measure.infinitePi fun _ : ℕ => μ) (Measure.pi fun _ : I => μ) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ) hinj)
  exact hselect.comp (measurePreserving_fst
    (μ := Measure.infinitePi fun _ : ℕ => μ)
    (ν := Measure.infinitePi fun _ : ℕ => circularGaussianPairLaw))

/-- No independence or marginal-law certificate is left to the caller
when an actual finite product sampling map has been constructed. -/
theorem copies_of_product_sampling
    {Ω E I : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [Fintype I]
    {P : Measure Ω} {μ : Measure E} [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (samples : Ω → I → E)
    (hsamples : MeasurePreserving samples P (Measure.pi fun _ : I => μ))
    (atom : E → ℂ) (hatom : Measurable atom) :
    IndependentAtomCopies21 P μ atom (fun i ω => atom (samples ω i)) := by
  have hmarg (i : I) : MeasurePreserving (fun ω => samples ω i) P μ :=
    (measurePreserving_eval (fun _ : I => μ) i).comp hsamples
  have hind : iIndepFun (fun i ω => samples ω i) P := by
    apply (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (hmarg i).measurable.aemeasurable)).mpr
    simp_rw [(hmarg _).map_eq]
    exact hsamples.map_eq
  refine ⟨fun i => hatom.comp (hmarg i).measurable,
    hind.comp (fun _ => atom) (fun _ => hatom), ?_⟩
  intro i
  have hraw : IdentDistrib (fun ω => samples ω i) (fun x : E => x) P μ :=
    ⟨(hmarg i).measurable.aemeasurable, measurable_id.aemeasurable,
      by simpa using (hmarg i).map_eq⟩
  exact hraw.comp hatom

theorem squareAtomIndex_injective (N : ℕ) :
    Function.Injective (fun ij : Fin N × Fin N => squareAtomIndex ij.1 ij.2) := by
  intro ij kl h
  exact finProdFinEquiv.injective (Fin.ext h)

def actualProfileMatrix {E : Type*} (atom : E → ℂ) {N : ℕ}
    (σ : Matrix (Fin N) (Fin N) ℝ) (ω : SampleSpace E) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (σ i j : ℂ) * atom (ω.1 (squareAtomIndex i j))

def sourceVarianceProfile {N : ℕ} (σ : Matrix (Fin N) (Fin N) ℝ)
    (hσ : DoublyStochasticProfile σ) : DoublyStochasticVarianceProfile (Fin N) :=
  ⟨σ, hσ.nonnegative, hσ.row, hσ.column⟩

/-- Section 3's actual v3 model, with entry independence and laws derived
from the original IID coordinate process. -/
def profileV3Model
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (atom : E → ℂ) (hatom : AtomMomentAssumption21 μ atom)
    {N : ℕ} (σ : Matrix (Fin N) (Fin N) ℝ) (hσ : DoublyStochasticProfile σ) :
    RandomMatrixModelV3 N (SampleSpace E) E (sampleLaw μ) μ := by
  let copies := copies_of_product_sampling
    (fun ω : SampleSpace E => fun ij : Fin N × Fin N => ω.1 (squareAtomIndex ij.1 ij.2))
    (selectedCoordinates_measurePreserving μ _ (squareAtomIndex_injective N)) atom hatom.measurable
  exact
    { matrix := actualProfileMatrix atom σ
      atom := atom
      profile := sourceVarianceProfile σ hσ
      entry_measurable := fun i j => measurable_const.mul (copies.measurable (i, j))
      entries_independent := copies.independent.comp (fun ij x => (σ ij.1 ij.2 : ℂ) * x)
        (fun _ => measurable_const.mul measurable_id)
      entry_law := fun i j => (copies.law (i, j)).const_mul (σ i j : ℂ)
      atom_integrable := hatom.integrable
      atom_mean_zero := hatom.centered
      atom_variance_one := hatom.unitSecondMoment
      atom_third_moment_finite := hatom.thirdMomentIntegrable }

/-- The full-block source model has bandwidth exactly `3W`. -/
theorem physical_source_bandwidth (W s : ℕ) (hW : 0 < W) :
    IsBandwidth (sourceVarianceProfile (physicalProfile W s)
      (physicalProfile_doublyStochastic W s hW)) (3 * (W : ℝ)) := by
  refine ⟨by positivity, physicalProfile_sq_le W s, ?_⟩
  let i : Fin ((s + 3) * W) := ⟨0, Nat.mul_pos (by omega) hW⟩
  refine ⟨i, i, ?_⟩
  simp [sourceVarianceProfile, physicalProfile, physicalSiteAdjacent,
    BernoulliSection10.blockNormalization_sq]

end BernoulliSection10Source
