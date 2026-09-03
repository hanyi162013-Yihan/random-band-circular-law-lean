import CircularLawSection6.GinibreReferenceSources
import CircularLawSection6.PublishedGaussianModel
import ShortRingAnchor.BC12.GinibreNegativeMoments
import CircularLawSection4.FlatIIDRows

/-! # Identifying the actual scalar Gaussian array with the proved LSV model

The finite-dimensional Gaussian law is proved from characteristic functions.
This is the missing connection between Section 5's scalar Gaussian coordinates
and the Euclidean Gaussian columns used in the already developed small-ball
argument. In particular `HasLaw` is constructed, not given by the caller.

With uniform BBV, the existing lower-edge/counting argument then proves the
negative-moment source for the actual Section 5 Ginibre process at p=1/128.
No BC12 negative-moment or log-potential convergence is assumed in that result.
-/

open MeasureTheory ProbabilityTheory Filter Topology ShortRingAnchor Arxiv2410V3
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput)
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace CircularLawSection6.GinibreReferenceSources

theorem complexGaussian_pi_toLp (N : ℕ) :
    (Measure.pi fun _ : Fin N => stdGaussian ℂ).map (WithLp.toLp 2) =
      stdGaussian (EuclideanSpace ℂ (Fin N)) := by
  apply Measure.ext_of_charFun (E := EuclideanSpace ℂ (Fin N))
  ext t
  simp_rw [charFun_pi, charFun_stdGaussian, ← Complex.exp_sum, ← Complex.ofReal_pow,
    EuclideanSpace.norm_sq_eq]
  simp [Finset.sum_div, Finset.sum_neg_distrib, Complex.ofReal_sum, neg_div]

theorem complexGaussian_columns_measurePreserving (N : ℕ) :
    MeasurePreserving (fun C : Fin N → Fin N → ℂ => fun j => WithLp.toLp 2 (C j))
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => stdGaussian ℂ)
      (GinibreLSV.complexGinibreColumns N) :=
  measurePreserving_pi _ _ fun _ => ⟨by fun_prop, complexGaussian_pi_toLp N⟩

def normalizedColumnEntries (N : ℕ) (C : Fin N → Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ := fun i j => C j i / (Real.sqrt (N : ℝ) : ℂ)

theorem normalizedColumnEntries_measurable (N : ℕ) :
    Measurable (normalizedColumnEntries N) := by
  unfold normalizedColumnEntries
  fun_prop

/-- Exact law identity, including both factors `1/sqrt 2` and `1/sqrt N`. -/
theorem normalizedGinibreLaw_eq_map_iidColumns (N : ℕ) :
    BC12.normalizedGinibreLaw N =
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => circularComplexGaussian).map
        (normalizedColumnEntries N) := by
  let Q := Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => stdGaussian ℂ
  let scale := fun C : Fin N → Fin N → ℂ => fun j i => complexGaussianScale (C j i)
  have hs : MeasurePreserving scale Q
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => circularComplexGaussian) :=
    measurePreserving_pi _ _ fun _ => measurePreserving_pi _ _ fun _ =>
      ⟨complexGaussianScale.measurable, rfl⟩
  have hc := complexGaussian_columns_measurePreserving N
  change (GinibreLSV.complexGinibreColumns N).map (BC12.normalizedGinibreMatrix N) = _
  rw [← hc.map_eq, ← hs.map_eq,
    Measure.map_map (BC12.continuous_normalizedGinibreMatrix N).measurable hc.measurable,
    Measure.map_map (normalizedColumnEntries_measurable N) hs.measurable]
  congr 1
  funext C
  ext i j
  simp [Function.comp_def, normalizedColumnEntries, BC12.normalizedGinibreMatrix,
    GinibreLSV.normalizedComplexGinibreMatrix, GinibreLSV.matrixOfColumns,
    scale, complexGaussianScale, Algebra.smul_def, div_eq_mul_inv, mul_comm, mul_left_comm]

def sequenceColumns (N : ℕ) (ω : ℕ → ℂ) : Fin N → Fin N → ℂ :=
  fun j i => ω (CircularLawSections56.Section5.PublishedSection3Concrete.denseCoordinate (i, j))

theorem sequenceColumns_measurePreserving (N : ℕ) :
    MeasurePreserving (sequenceColumns N)
      CircularLawSections56.Section5.PublishedSection3Concrete.gaussianSequenceLaw
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => circularComplexGaussian) := by
  have hidx : Function.Injective (fun ij : Fin N × Fin N =>
      CircularLawSections56.Section5.PublishedSection3Concrete.denseCoordinate (ij.2, ij.1)) := by
    intro x y h
    have hp := CircularLawSections56.Section5.PublishedSection3Concrete.denseCoordinate_injective N h
    exact Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)
  exact (CircularLawSection4.measurePreserving_curry_fin_iid N N circularComplexGaussian).comp
    (CircularLawSections56.Section5.PublishedSection3Concrete.selectedCoordinates_measurePreserving
      circularComplexGaussian _ hidx)

/-- The source process really has the normalized Gaussian matrix law used
by the independently proved least-singular-value estimate. -/
theorem ginibreOnSequence_hasLaw (N : ℕ) :
    HasLaw (CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence N)
      (BC12.normalizedGinibreLaw N)
      CircularLawSections56.Section5.PublishedSection3Concrete.gaussianSequenceLaw := by
  have hT := sequenceColumns_measurePreserving N
  refine ⟨((normalizedColumnEntries_measurable N).comp hT.measurable).aemeasurable, ?_⟩
  change Measure.map (normalizedColumnEntries N ∘ sequenceColumns N) _ = _
  rw [← Measure.map_map (normalizedColumnEntries_measurable N) hT.measurable,
    hT.map_eq, ← normalizedGinibreLaw_eq_map_iidColumns]

def sequenceDenseModel (N : ℕ) (hN : 0 < N) :
    RandomMatrixModelV3 N (ℕ → ℂ) ℂ
      CircularLawSections56.Section5.PublishedSection3Concrete.gaussianSequenceLaw
      circularComplexGaussian :=
  denseV3Model hN
    (fun ω i j => ω (CircularLawSections56.Section5.PublishedSection3Concrete.denseCoordinate (i, j)))
    id circularComplexGaussian_publishedMoments
    (independentAtomCopies21_of_jointLaw _ _ _
      (CircularLawSections56.Section5.PublishedSection3Concrete.selectedCoordinates_measurePreserving
        circularComplexGaussian _
        (CircularLawSections56.Section5.PublishedSection3Concrete.denseCoordinate_injective N)))

/-- The actual reference's BC12 negative moment, derived from uniform BBV
and the proved Gaussian small-ball estimate, with no BC12 premise. -/
theorem ginibre_negative_on_sequence_of_bbv
    (hBBV : BBVComparisonInput) (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop) (z : ℂ) :
    BC12GinibreNegativeMomentTightness
      CircularLawSections56.Section5.PublishedSection3Concrete.gaussianSequenceLaw (1 / 128)
      (shiftedSingularValueProcess
        (fun n => CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence (N n)) z) := by
  obtain ⟨C, _hC, hcomp⟩ := hBBV
  let D := gaussianSection3ComparisonConstant C
  apply BC12.negativeMomentTightness_of_ginibreLaw_and_v3 hNpos hN
    (fun n => sequenceDenseModel (N n) (hNpos n))
    (fun n => ginibreOnSequence_hasLaw (N n))
    (fun n => denseVarianceProfile_isBandwidth (hNpos n)) z
    (gaussianSection3ComparisonConstant_ge_eight C)
  · intro n
    change (∫ x : ℂ, ‖id x‖ ^ 3 ∂circularComplexGaussian) +
      BVH.complexGaussianThirdMomentConstant ≤ D
    exact (le_max_right _ _).trans (le_max_right _ _)
  · intro n v hv
    have hη : 0 < (spectralParameter 0 v).im := by simpa [spectralParameter] using hv
    exact CircularLawSections56.Section5.PublishedSection3Concrete.canonicalBBVAt_mono
      (hcomp (ℕ → ℂ) ℂ
        CircularLawSections56.Section5.PublishedSection3Concrete.gaussianSequenceLaw
        circularComplexGaussian (N n) (hNpos n) (sequenceDenseModel (N n) (hNpos n))
        (N n : ℝ) (denseVarianceProfile_isBandwidth (hNpos n)) z _ hη)
      (by exact_mod_cast hNpos n) hη (le_max_left _ _)

end CircularLawSection6.GinibreReferenceSources
