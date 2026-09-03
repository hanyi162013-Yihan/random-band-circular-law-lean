import CircularLawSections56.Section5.PublishedSection3Literature
import ShortRingAnchor.DenseV3Model
import ShortRingAnchor.BC12.GinibreNegativeMoments
import ShortRingAnchor.BC12.GaussianMatrixLawBridge
import CircularLawSection4.FlatIIDRows

/-!
# Proved Gaussian reference for the concrete Section 5 anchors

The Gaussian-column identification and BBV negative-moment argument are the
lower-level version of `CircularLawSection6.GinibreReferenceSources`' checked
construction. They use only Section 5 sampling, so there is no dependency on
the later Section 6 circular-law endpoint. The logarithmic potential follows
from the independently proved Ginibre correlation identities in Section 3.

`BC12GinibreInput` remains a compatibility proposition, but is constructed
here from BBV, not supplied as an external Gaussian theorem.
-/

open MeasureTheory ProbabilityTheory Filter Topology ShortRingAnchor Arxiv2410V3
open CircularLawSections56.Section5
open scoped BigOperators
noncomputable section

namespace CircularLawSections56.Section5.PublishedSection3Concrete

/-- Gaussian coordinates: the scalar product law is the Euclidean column law. -/
theorem complexGaussian_pi_toLp (N : ℕ) :
    (Measure.pi fun _ : Fin N => stdGaussian ℂ).map (WithLp.toLp 2) =
      stdGaussian (EuclideanSpace ℂ (Fin N)) := by
  apply Measure.ext_of_charFun (E := EuclideanSpace ℂ (Fin N))
  ext t
  simp_rw [charFun_pi, charFun_stdGaussian, ← Complex.exp_sum, ← Complex.ofReal_pow,
    EuclideanSpace.norm_sq_eq]
  simp [Finset.sum_div, Finset.sum_neg_distrib, Complex.ofReal_sum, neg_div]

/-- Independent scalar Gaussian columns give the actual Section 3 column model. -/
theorem complexGaussian_columns_measurePreserving (N : ℕ) :
    MeasurePreserving (fun C : Fin N → Fin N → ℂ => fun j => WithLp.toLp 2 (C j))
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => stdGaussian ℂ)
      (GinibreLSV.complexGinibreColumns N) :=
  measurePreserving_pi _ _ fun _ => ⟨by fun_prop, complexGaussian_pi_toLp N⟩

def normalizedColumnEntries (N : ℕ) (C : Fin N → Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ := fun i j => C j i / (Real.sqrt (N : ℝ) : ℂ)

/-- Section 3 model transport: normalized matrix entries are measurable. -/
theorem normalizedColumnEntries_measurable (N : ℕ) :
    Measurable (normalizedColumnEntries N) := by
  have hc : Continuous (normalizedColumnEntries N) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact ((continuous_apply i).comp (continuous_apply j)).div_const _
  exact hc.measurable

/-- Exact normalization of the Section 5 reference, including `1/sqrt 2`. -/
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
  change ((Real.sqrt (N : ℝ))⁻¹ : ℂ) *
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * C j i) =
    ((Real.sqrt 2)⁻¹ • C j i) / (Real.sqrt (N : ℝ) : ℂ)
  simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

def sequenceColumns (N : ℕ) (ω : ℕ → ℂ) : Fin N → Fin N → ℂ :=
  fun j i => ω (denseCoordinate (i, j))

/-- Section 5 finite-coordinate extraction preserves the independent Gaussian law. -/
theorem sequenceColumns_measurePreserving (N : ℕ) :
    MeasurePreserving (sequenceColumns N) gaussianSequenceLaw
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => circularComplexGaussian) := by
  have hidx : Function.Injective (fun ij : Fin N × Fin N => denseCoordinate (ij.2, ij.1)) := by
    intro x y h
    have hp := denseCoordinate_injective N h
    exact Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)
  exact (CircularLawSection4.measurePreserving_curry_fin_iid N N circularComplexGaussian).comp
    (selectedCoordinates_measurePreserving circularComplexGaussian _ hidx)

/-- The literal Section 5 reference has the proved Section 3 Ginibre law. -/
theorem ginibreOnSequence_hasLaw (N : ℕ) :
    HasLaw (ginibreOnSequence N) (BC12.normalizedGinibreLaw N) gaussianSequenceLaw := by
  have hT := sequenceColumns_measurePreserving N
  refine ⟨((normalizedColumnEntries_measurable N).comp hT.measurable).aemeasurable, ?_⟩
  change Measure.map (normalizedColumnEntries N ∘ sequenceColumns N) _ = _
  rw [← Measure.map_map (normalizedColumnEntries_measurable N) hT.measurable,
    hT.map_eq, ← normalizedGinibreLaw_eq_map_iidColumns]

def sequenceDenseModel (N : ℕ) (hN : 0 < N) :
    RandomMatrixModelV3 N (ℕ → ℂ) ℂ gaussianSequenceLaw circularComplexGaussian :=
  denseV3Model hN (fun ω i j => ω (denseCoordinate (i, j))) id gaussianMoments
    (independentAtomCopies21_of_jointLaw _ _ _
      (selectedCoordinates_measurePreserving circularComplexGaussian _
        (denseCoordinate_injective N)))

/-- Proposition 3.6 Gaussian lower tail: BBV plus proved small-ball gives `p=1/128`. -/
theorem ginibre_negative_on_sequence_of_bbv
    (hBBV : BBVComparisonInput) (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop) (z : ℂ) :
    BC12GinibreNegativeMomentTightness gaussianSequenceLaw (1 / 128)
      (shiftedSingularValueProcess (fun n => ginibreOnSequence (N n)) z) := by
  obtain ⟨C, _hC, hcomp⟩ := hBBV
  let D := max C
    (max 8 ((∫ x : ℂ, ‖x‖ ^ 3 ∂circularComplexGaussian) + BVH.complexGaussianThirdMomentConstant))
  apply BC12.negativeMomentTightness_of_ginibreLaw_and_v3 hNpos hN
    (fun n => sequenceDenseModel (N n) (hNpos n))
    (fun n => ginibreOnSequence_hasLaw (N n))
    (fun n => denseVarianceProfile_isBandwidth (hNpos n)) z
    (C := D) ((le_max_left _ _).trans (le_max_right _ _))
  · intro n
    change (∫ x : ℂ, ‖id x‖ ^ 3 ∂circularComplexGaussian) +
      BVH.complexGaussianThirdMomentConstant ≤ D
    exact (le_max_right _ _).trans (le_max_right _ _)
  · intro n v hv
    have hη : 0 < (spectralParameter 0 v).im := by simpa [spectralParameter] using hv
    exact canonicalBBVAt_mono
      (hcomp (ℕ → ℂ) ℂ gaussianSequenceLaw circularComplexGaussian (N n) (hNpos n)
        (sequenceDenseModel (N n) (hNpos n)) (N n : ℝ)
        (denseVarianceProfile_isBandwidth (hNpos n)) z _ hη)
      (by exact_mod_cast hNpos n) hη (le_max_left _ _)

/-- Gaussian full-log potential for the actual reference; no literature premise. -/
theorem ginibre_logPotential_on_sequence
    (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop) (z : ℂ) :
    ConvergesInProbability gaussianSequenceLaw
      (fun n ω => normalizedShiftLogDet (ginibreOnSequence (N n) ω) z)
      (circularLogPotential z) :=
  BC12.ginibre_logdet_convergesInProbability_of_ginibreLaw hNpos hN
    (fun n => ginibreOnSequence (N n)) (fun n => ginibreOnSequence_hasLaw (N n)) z

/-- The former external BC12 bundle is now a consequence of BBV and proved Gaussian facts. -/
theorem provedGinibreInput (hBBV : BBVComparisonInput) : BC12GinibreInput := by
  intro N hNpos hN z
  exact ⟨1 / 128, by norm_num,
    ginibre_negative_on_sequence_of_bbv hBBV N hNpos hN z,
    ginibre_logPotential_on_sequence N hNpos hN z⟩

end CircularLawSections56.Section5.PublishedSection3Concrete
