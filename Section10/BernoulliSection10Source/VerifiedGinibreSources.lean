import BernoulliSection10Source.LiteratureInputs
import ShortRingAnchor.BC12.GinibreNegativeMoments
import ShortRingAnchor.BC12.GaussianMatrixLawBridge

/-!
# Discharging the Gaussian source for Section 10

Finite-coordinate extraction identifies the actual independent real-pair
matrix with the verified Section 3 Ginibre law. Its full-log limit follows
from the proved correlation formulas, and its negative moment from BBV and
the proved small-ball/counting argument. No BC12 theorem is assumed here.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
noncomputable section
namespace BernoulliSection10Source
open BernoulliSection10.SourceInputs ShortRingAnchor Arxiv2410V3

local instance section10GaussianMatrixMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _
local instance section10GaussianMatrixBorelSpace (n : ℕ) :
    BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩

/-- The normalized pair atom has real-coordinate variance `1/(2N)`. -/
theorem normalizedGaussianPair_map {N : ℕ} (hN : 0 < N) :
    circularGaussianPairLaw.map
      (fun p => circularGaussianAtom p / (Real.sqrt (N : ℝ) : ℂ)) =
      Ginibre.gaussianEntryLaw N := by
  let r : ℝ := (Real.sqrt (N : ℝ))⁻¹
  let v : ℝ≥0 := NNReal.mk (r ^ 2 / 2) (div_nonneg (sq_nonneg r) (by norm_num))
  have hr : 0 < r := by dsimp [r]; positivity
  have hv : 0 < v := by
    change (0 : ℝ) < r ^ 2 / 2
    exact div_pos (sq_pos_of_pos hr) (by norm_num)
  have hav : 2 * (v : ℝ) = (N : ℝ)⁻¹ := by
    change 2 * (r ^ 2 / 2) = (N : ℝ)⁻¹
    dsimp only [r]
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  have hreal : (gaussianReal 0 (1 / 2)).map (fun x => r * x) = gaussianReal 0 v := by
    have hvar : NNReal.mk (r ^ 2) (sq_nonneg r) * (1 / 2) = v := by
      apply NNReal.coe_injective
      change r ^ 2 * (1 / 2 : ℝ) = r ^ 2 / 2
      ring
    have h := (gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 (1 / 2))) r).map_eq
    simpa only [id_eq, mul_zero, hvar] using h
  rw [BC12.gaussianEntryLaw_eq_realPair (by exact_mod_cast hN) hv hav,
    ← hreal, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map Complex.measurableEquivRealProd.symm.measurable (by fun_prop)]
  congr 1
  funext p
  change circularGaussianAtom p / (Real.sqrt (N : ℝ) : ℂ) =
    Complex.measurableEquivRealProd.symm (r * p.1, r * p.2)
  rw [div_eq_mul_inv, ← Complex.ofReal_inv]
  change circularGaussianAtom p * (r : ℂ) =
    Complex.measurableEquivRealProd.symm (r * p.1, r * p.2)
  simp only [circularGaussianAtom,
    Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I, Complex.ofReal_mul]
  ring

/-- The finite pair coordinates in the actual reference are independent. -/
theorem sequencePairs_measurePreserving (N : ℕ) :
    MeasurePreserving
      (fun ω : GaussianSequence => fun ij : Fin N × Fin N => ω (squareAtomIndex ij.1 ij.2))
      gaussianSequenceLaw (Measure.pi fun _ : Fin N × Fin N => circularGaussianPairLaw) := by
  refine ⟨by fun_prop, ?_⟩
  simpa only [Measure.infinitePi_eq_pi] using
    (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => circularGaussianPairLaw) (squareAtomIndex_injective N))

/-- The literal Section 10 reference has the proved independent-entry Gaussian law. -/
theorem ginibreOnSequence_hasEntryLaw {N : ℕ} (hN : 0 < N) :
    HasLaw (fun sample (ij : Fin N × Fin N) => ginibreOnSequence N sample ij.1 ij.2)
      (Ginibre.gaussianMatrixLaw N N) gaussianSequenceLaw := by
  let := Ginibre.gaussianEntryLaw_isProbability (by exact_mod_cast hN : (0 : ℝ) < N)
  let f : ℝ × ℝ → ℂ := fun p => circularGaussianAtom p / (Real.sqrt (N : ℝ) : ℂ)
  have hf : MeasurePreserving f circularGaussianPairLaw (Ginibre.gaussianEntryLaw N) :=
    ⟨measurable_circularGaussianAtom.div_const _, normalizedGaussianPair_map hN⟩
  have hi := measurePreserving_pi
    (fun _ : Fin N × Fin N => circularGaussianPairLaw)
    (fun _ : Fin N × Fin N => Ginibre.gaussianEntryLaw N) (fun _ => hf)
  exact ⟨(hi.comp (sequencePairs_measurePreserving N)).measurable.aemeasurable,
    (hi.comp (sequencePairs_measurePreserving N)).map_eq⟩

def gaussianMatrixEntriesEquiv (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ ≃ᵐ (Fin N × Fin N → ℂ) where
  toFun A ij := A ij.1 ij.2
  invFun x i j := x (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := BC12.measurable_matrixEntries N
  measurable_invFun := by
    apply Continuous.measurable
    exact continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)

/-- The Gaussian-entry and Gaussian-column reference laws agree on actual matrices. -/
theorem ginibreOnSequence_hasLaw {N : ℕ} (hN : 0 < N) :
    HasLaw (ginibreOnSequence N) (BC12.normalizedGinibreLaw N) gaussianSequenceLaw := by
  have hm : Measurable (ginibreOnSequence N) := by
    apply Continuous.measurable
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    unfold ginibreOnSequence circularGaussianAtom
    fun_prop
  refine ⟨hm.aemeasurable, ?_⟩
  apply (gaussianMatrixEntriesEquiv N).measurableEmbedding.map_injective
  rw [Measure.map_map (gaussianMatrixEntriesEquiv N).measurable hm]
  exact (ginibreOnSequence_hasEntryLaw hN).map_eq.trans
    (BC12.normalizedGinibreLaw_flatten hN).symm

def sequenceDenseModel (N : ℕ) (hN : 0 < N) :
    RandomMatrixModelV3 N GaussianSequence (ℝ × ℝ) gaussianSequenceLaw circularGaussianPairLaw :=
  denseV3Model hN (fun ω i j => circularGaussianAtom (ω (squareAtomIndex i j)))
    circularGaussianAtom gaussianAtomMoments
    (copies_of_product_sampling _ (sequencePairs_measurePreserving N)
      circularGaussianAtom measurable_circularGaussianAtom)

/-- Proposition 3.6 Gaussian negative moment, obtained from BBV and proved small-ball bounds. -/
theorem ginibre_negative_on_sequence_of_bbv
    (hBBV : BBVComparisonInput) (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop) (z : ℂ) :
    BC12GinibreNegativeMomentTightness gaussianSequenceLaw (1 / 128)
      (shiftedSingularValueProcess (fun n => ginibreOnSequence (N n)) z) := by
  obtain ⟨C, _hC, hcomp⟩ := hBBV
  let D := max C (max 8 ((∫ x, ‖circularGaussianAtom x‖ ^ 3 ∂circularGaussianPairLaw) +
    BVH.complexGaussianThirdMomentConstant))
  apply BC12.negativeMomentTightness_of_ginibreLaw_and_v3 hNpos hN
    (fun n => sequenceDenseModel (N n) (hNpos n))
    (fun n => ginibreOnSequence_hasLaw (hNpos n))
    (fun n => denseVarianceProfile_isBandwidth (hNpos n)) z
    (C := D) ((le_max_left _ _).trans (le_max_right _ _))
  · intro n
    exact (le_max_right _ _).trans (le_max_right _ _)
  · intro n v hv
    have hη : 0 < (spectralParameter 0 v).im := by simpa [spectralParameter] using hv
    exact canonicalBBVAt_mono
      (hcomp GaussianSequence (ℝ × ℝ) gaussianSequenceLaw circularGaussianPairLaw
        (N n) (hNpos n) (sequenceDenseModel (N n) (hNpos n)) (N n : ℝ)
        (denseVarianceProfile_isBandwidth (hNpos n)) z _ hη)
      (by exact_mod_cast hNpos n) hη (le_max_left _ _)

/-- Section 10's actual Ginibre full-log limit has no external Gaussian premise. -/
theorem ginibre_logPotential_on_sequence
    (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop) (z : ℂ) :
    ConvergesInProbability gaussianSequenceLaw
      (fun n ω => normalizedShiftLogDet (ginibreOnSequence (N n) ω) z)
      (circularLogPotential z) :=
  BC12.ginibre_logdet_convergesInProbability_of_ginibreLaw hNpos hN
    (fun n => ginibreOnSequence (N n)) (fun n => ginibreOnSequence_hasLaw (hNpos n)) z

/-- The former BC12 source is constructed; BBV is the only premise of this adapter. -/
theorem provedGinibreInput (hBBV : BBVComparisonInput) : BC12GinibreInput := by
  intro N hNpos hN z
  exact ⟨1 / 128, by norm_num,
    ginibre_negative_on_sequence_of_bbv hBBV N hNpos hN z,
    ginibre_logPotential_on_sequence N hNpos hN z⟩

end BernoulliSection10Source
