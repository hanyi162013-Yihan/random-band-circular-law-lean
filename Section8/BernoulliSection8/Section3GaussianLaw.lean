import BernoulliSection8.Section3Model
import ShortRingAnchor.BC12.GaussianMatrixLawBridge

/-!
# The Section 8 reference has the proved Section 3 Ginibre law

The reference is the existing infinite IID sequence of real Gaussian pairs.
Finite-coordinate extraction and the exact `1/sqrt(N)` normalization prove
its matrix law. No spectral, correlation, density or tail estimate is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace BernoulliSection8.Section3Bridge
open BernoulliSection10 BernoulliSection10.SourceInputs ShortRingAnchor

local instance section8GaussianMatrixMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _
local instance section8GaussianMatrixBorelSpace (n : ℕ) :
    BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩

/-- Section 3.8 reference normalization: each real coordinate has variance `1/(2N)`. -/
theorem normalizedGaussianPair_map {N : ℕ} (hN : 0 < N) :
    circularGaussianPairLaw.map (fun p => gaussianAtom p / (Real.sqrt (N : ℝ) : ℂ)) =
      Ginibre.gaussianEntryLaw N := by
  let r : ℝ := (Real.sqrt (N : ℝ))⁻¹
  let v : ℝ≥0 := ⟨r ^ 2, sq_nonneg _⟩ * (1 / 2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hv : 0 < v := by
    change (0 : ℝ) < (v : ℝ)
    dsimp [v]
    positivity
  have hav : 2 * (v : ℝ) = (N : ℝ)⁻¹ := by
    simp only [v, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat]
    dsimp only [r]
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  have hreal : (gaussianReal 0 (1 / 2)).map (fun x => r * x) = gaussianReal 0 v := by
    have h := (gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 (1 / 2))) r).map_eq
    simpa only [id_eq, mul_zero] using h
  rw [BC12.gaussianEntryLaw_eq_realPair (by exact_mod_cast hN) hv hav,
    ← hreal, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map Complex.measurableEquivRealProd.symm.measurable (by fun_prop)]
  congr 1
  funext p
  apply Complex.ext <;>
    simp [Function.comp_def, gaussianAtom, r, div_eq_mul_inv,
      Complex.measurableEquivRealProd_symm_apply, mul_comm]

/-- Section 8's finite Gaussian array has independent entries of the exact planar law. -/
theorem circularGinibre_hasEntryLaw (A : Proposition38.Atom) {N : ℕ} (hN : 0 < N) :
    HasLaw (fun sample (ij : Fin N × Fin N) => circularGinibreMatrix N sample ij.1 ij.2)
      (Ginibre.gaussianMatrixLaw N N) (inputLaw A.law) := by
  letI := Ginibre.gaussianEntryLaw_isProbability (by exact_mod_cast hN : (0 : ℝ) < N)
  let pairs : InputSpace → Fin N × Fin N → ℝ × ℝ :=
    fun sample ij => sample.2 (squareAtomIndex ij.1 ij.2)
  have hp : MeasurePreserving pairs (inputLaw A.law)
      (Measure.pi fun _ : Fin N × Fin N => circularGaussianPairLaw) :=
    ((measurePreserving_iid_reindex circularGaussianPairLaw
      (finProdFinEquiv : Fin N × Fin N ≃ Fin (N * N))).comp
      (measurePreserving_initialIIDCoordinates circularGaussianPairLaw (N * N))).comp
        measurePreserving_snd
  let f : ℝ × ℝ → ℂ := fun p => gaussianAtom p / (Real.sqrt (N : ℝ) : ℂ)
  have hf : MeasurePreserving f circularGaussianPairLaw (Ginibre.gaussianEntryLaw N) :=
    ⟨gaussianAtom_measurable.div_const _, normalizedGaussianPair_map hN⟩
  have hi := measurePreserving_pi
    (fun _ : Fin N × Fin N => circularGaussianPairLaw)
    (fun _ : Fin N × Fin N => Ginibre.gaussianEntryLaw N) (fun _ => hf)
  have he : (fun sample (ij : Fin N × Fin N) => circularGinibreMatrix N sample ij.1 ij.2) =
      (fun x ij => f (x ij)) ∘ pairs := by
    funext sample ij
    simp [circularGinibreMatrix, f, pairs, gaussianAtom, Function.comp_def,
      Complex.equivRealProdCLM_symm_apply]
  rw [he]
  exact ⟨(hi.comp hp).measurable.aemeasurable, (hi.comp hp).map_eq⟩

/-- Flattening matrix coordinates is a measurable equivalence, not a distribution assumption. -/
def gaussianMatrixEntriesEquiv (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ ≃ᵐ (Fin N × Fin N → ℂ) where
  toFun A ij := A ij.1 ij.2
  invFun x i j := x (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := BC12.measurable_matrixEntries N
  measurable_invFun := (continuous_pi fun i =>
    continuous_pi fun j => continuous_apply (i, j)).measurable

/-- The actual Section 8 comparison matrix has the Section 3 Gaussian-column law. -/
theorem circularGinibre_hasLaw (A : Proposition38.Atom) {N : ℕ} (hN : 0 < N) :
    HasLaw (circularGinibreMatrix N) (BC12.normalizedGinibreLaw N) (inputLaw A.law) := by
  have hm : Measurable (circularGinibreMatrix N) := by
    apply Continuous.measurable
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    unfold circularGinibreMatrix
    fun_prop
  refine ⟨hm.aemeasurable, ?_⟩
  apply (gaussianMatrixEntriesEquiv N).measurableEmbedding.map_injective
  rw [Measure.map_map (gaussianMatrixEntriesEquiv N).measurable hm]
  exact (circularGinibre_hasEntryLaw A hN).map_eq.trans
    (BC12.normalizedGinibreLaw_flatten hN).symm

/-- The normalized dense process in the Proposition 3.8 call has the proved Ginibre law. -/
theorem normalizedDense_hasGinibreLaw (A : Proposition38.Atom) (N : ℕ → ℕ)
    (k : ℕ) (hN : 0 < N k) :
    HasLaw (normalizedDenseMatrixProcess (fun n => denseAtom (N n)) k)
      (BC12.normalizedGinibreLaw (N k)) (inputLaw A.law) := by
  have he : normalizedDenseMatrixProcess (fun n => denseAtom (N n)) k =
      circularGinibreMatrix (N k) := funext (normalizedDense_eq_circularGinibre N k)
  rw [he]
  exact circularGinibre_hasLaw A hN

end BernoulliSection8.Section3Bridge
