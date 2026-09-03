import CircularLawSections56.Section5.PublishedSection3GaussianBounds
import CircularLawSections56.Section5.PublishedSection3Sampling
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Explicit common sample space for the two finite Section 5 anchors

The Gaussian facts are reused from the verified Section 6 construction. The
infinite-coordinate sampling argument follows the verified Section 10 interface.
Only finitely many coordinates are selected for each matrix; no independence
between different matrix sizes is required.
-/

open MeasureTheory ProbabilityTheory ShortRingAnchor
open CircularLawSection4
open scoped ENNReal
noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5.PublishedSection3Concrete

theorem gaussianMoments : AtomMomentAssumption21 circularComplexGaussian id where
  stronglyMeasurable := stronglyMeasurable_id
  centered := circularComplexGaussian_mean
  unitSecondMoment := circularComplexGaussian_secondMoment
  thirdMomentIntegrable := by
    simpa only [id_eq] using
      (IsGaussian.memLp_id circularComplexGaussian 3 (by norm_num)).integrable_norm_pow (by norm_num)

def gaussianDensity :
    HasBoundedDensityWithRespectTo (Measure.map id circularComplexGaussian) (volume : Measure ℂ) where
  density := circularComplexGaussian.rnDeriv volume
  densityAEMeasurable := (Measure.measurable_rnDeriv circularComplexGaussian volume).aemeasurable
  bound := 2
  bound_lt_top := by norm_num
  density_le_bound := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (Measure.measurable_rnDeriv circularComplexGaussian volume)
    intro s _ _
    have h := (Measure.setLIntegral_rnDeriv_le (μ := circularComplexGaussian)
      (ν := (volume : Measure ℂ)) s).trans (circularComplexGaussian_le_two_volume s)
    simpa only [lintegral_const, Measure.restrict_apply_univ,
      Measure.smul_apply, smul_eq_mul] using h
  law_eq_withDensity := by
    rw [Measure.map_id]
    exact (Measure.withDensity_rnDeriv_eq _ _
      (Measure.absolutelyContinuous_of_le_smul circularComplexGaussian_le_two_volume)).symm

theorem gaussianDensityAlternative : AtomDensityAlternative21 circularComplexGaussian id :=
  .complex gaussianDensity

abbrev Sample := (ℕ → ℂ) × (ℕ → ℂ)

def gaussianSequenceLaw : Measure (ℕ → ℂ) :=
  Measure.infinitePi fun _ : ℕ => circularComplexGaussian

instance : IsProbabilityMeasure gaussianSequenceLaw := by
  unfold gaussianSequenceLaw
  infer_instance

def sampleLaw (ν : Measure ℂ) : Measure Sample :=
  (Measure.infinitePi fun _ : ℕ => ν).prod gaussianSequenceLaw

instance (ν : Measure ℂ) [IsProbabilityMeasure ν] : IsProbabilityMeasure (sampleLaw ν) := by
  unfold sampleLaw
  infer_instance

def samples (L : ℕ) (ω : Sample) : Fin L → ℂ := fun i => ω.1 i.val

theorem selectedCoordinates_measurePreserving
    {I : Type*} [Fintype I] (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (idx : I → ℕ) (hinj : Function.Injective idx) :
    MeasurePreserving (fun ω : ℕ → ℂ => fun i => ω (idx i))
      (Measure.infinitePi fun _ : ℕ => ν) (Measure.pi fun _ : I => ν) := by
  refine ⟨by fun_prop, ?_⟩
  simpa only [Measure.infinitePi_eq_pi] using
    (Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ν) hinj)

theorem samples_measurePreserving (ν : Measure ℂ) [IsProbabilityMeasure ν] (L : ℕ) :
    MeasurePreserving (samples L) (sampleLaw ν) (iidMeasure ν L) := by
  rw [iidMeasure_eq_pi]
  exact (selectedCoordinates_measurePreserving ν Fin.val Fin.val_injective).comp
    (measurePreserving_fst (μ := Measure.infinitePi fun _ : ℕ => ν) (ν := gaussianSequenceLaw))

def denseCoordinate {N : ℕ} (ij : Fin N × Fin N) : ℕ := (finProdFinEquiv ij).val

theorem denseCoordinate_injective (N : ℕ) :
    Function.Injective (denseCoordinate (N := N)) := by
  intro x y h
  exact finProdFinEquiv.injective (Fin.ext h)

def denseSamples (N : ℕ) (ω : Sample) (ij : Fin N × Fin N) : ℂ :=
  ω.2 (denseCoordinate ij)

theorem denseSamples_measurePreserving (ν : Measure ℂ) [IsProbabilityMeasure ν] (N : ℕ) :
    MeasurePreserving (denseSamples N) (sampleLaw ν)
      (Measure.pi fun _ : Fin N × Fin N => circularComplexGaussian) :=
  (selectedCoordinates_measurePreserving circularComplexGaussian denseCoordinate
    (denseCoordinate_injective N)).comp
    (measurePreserving_snd (μ := Measure.infinitePi fun _ : ℕ => ν) (ν := gaussianSequenceLaw))

def ginibreOnSequence (N : ℕ) (ω : ℕ → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ω (denseCoordinate (i, j)) / (Real.sqrt (N : ℝ) : ℂ)

def actualGinibre (N : ℕ) (ω : Sample) : Matrix (Fin N) (Fin N) ℂ :=
  ginibreOnSequence N ω.2

theorem samples_prefix (L K : ℕ) (h : L ≤ K) (ω : Sample) :
    (fun i => samples K ω (Fin.castLE h i)) = samples L ω := rfl

end CircularLawSections56.Section5.PublishedSection3Concrete
