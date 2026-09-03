import BernoulliSection8.Section3Gaussian
import BernoulliSection10.PhysicalInputLaw
import ShortRingAnchor.Proposition38.Model

/-! Exact coordinates, laws and matrices for the Section 3.8 / Section 8 bridge. -/

open MeasureTheory ProbabilityTheory
noncomputable section
namespace BernoulliSection8.Section3Bridge
open BernoulliSection10 BernoulliSection10.SourceInputs ShortRingAnchor

def ringArray (A : Proposition38.Atom) (N : ℕ) :
    Proposition38.AtomArray (inputLaw A.law) A (Fin N × Fin N) := by
  let G : InputSpace → Fin N × Fin N → ℝ := fun sample => squareIIDFromSequence N sample.1
  have hG : MeasurePreserving G (inputLaw A.law) (Measure.pi fun _ : Fin N × Fin N => A.law) :=
    (squareIIDFromSequence_measurePreserving A.law N).comp measurePreserving_fst
  have hc (i : Fin N × Fin N) : MeasurePreserving (fun sample => G sample i)
      (inputLaw A.law) A.law := (measurePreserving_eval (fun _ => A.law) i).comp hG
  refine { entry := fun i sample => G sample i
           measurable := fun i => (hc i).measurable
           independent := ?_
           law := ?_ }
  · apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hc i).measurable.aemeasurable)).2
    change (inputLaw A.law).map G = Measure.pi (fun i => (inputLaw A.law).map (fun sample => G sample i))
    simp only [(hc _).map_eq, hG.map_eq]
  · intro i
    exact ⟨(hc i).measurable.aemeasurable, measurable_id.aemeasurable,
      by simpa using (hc i).map_eq⟩

theorem cyclicSiteSucc_eq_finRotate (s : ℕ) :
    BernoulliLinearAlgebra.cyclicSiteSucc (m := s + 2) = finRotate (s + 3) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · rw [BernoulliLinearAlgebra.cyclicSiteSucc_castSucc]
    exact (finRotate_of_lt j.isLt).symm

theorem coefficient_eq_physicalProfile (W s : ℕ) :
    Proposition38.coefficient W s = physicalProfile W s := by
  funext i j
  simp only [Proposition38.coefficient, physicalProfile, Proposition38.siteAdjacent,
    physicalSiteAdjacent, cyclicSiteSucc_eq_finRotate, blockNormalization]

theorem fullBlockMatrix_eq_physical (A : Proposition38.Atom) (W s : ℕ) (sample : InputSpace) :
    Proposition38.fullBlockMatrix (ringArray A ((s + 3) * W)) sample =
      densityCyclicMatrix W s (physicalRowsFromSequence W s sample.1) := by
  ext i j
  rw [densityCyclicMatrix_from_sequence]
  simp only [Proposition38.fullBlockMatrix, ringArray, squareIIDFromSequence,
    coefficient_eq_physicalProfile, Complex.ofReal_mul]

def denseAtom (N : ℕ) (sample : InputSpace) (i j : Fin N) : ℂ :=
  gaussianAtom (sample.2 (squareAtomIndex i j))

theorem denseAtom_copies (A : Proposition38.Atom) (N : ℕ) :
    IndependentAtomCopies21 (inputLaw A.law) circularGaussianPairLaw gaussianAtom
      (fun ij : Fin N × Fin N => fun sample => denseAtom N sample ij.1 ij.2) := by
  let G : InputSpace → Fin N × Fin N → ℝ × ℝ :=
    fun sample ij => sample.2 (squareAtomIndex ij.1 ij.2)
  have hG : MeasurePreserving G (inputLaw A.law)
      (Measure.pi fun _ : Fin N × Fin N => circularGaussianPairLaw) :=
    ((measurePreserving_iid_reindex circularGaussianPairLaw
      (finProdFinEquiv : Fin N × Fin N ≃ Fin (N * N))).comp
      (measurePreserving_initialIIDCoordinates circularGaussianPairLaw (N * N))).comp
        measurePreserving_snd
  have hc (i : Fin N × Fin N) : MeasurePreserving (fun sample => G sample i)
      (inputLaw A.law) circularGaussianPairLaw :=
    (measurePreserving_eval (fun _ => circularGaussianPairLaw) i).comp hG
  have hi : iIndepFun (fun i sample => G sample i) (inputLaw A.law) := by
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hc i).measurable.aemeasurable)).2
    change (inputLaw A.law).map G = Measure.pi (fun i => (inputLaw A.law).map (fun sample => G sample i))
    simp only [(hc _).map_eq, hG.map_eq]
  refine ⟨fun i => gaussianAtom_measurable.comp (hc i).measurable,
    hi.comp (fun _ => gaussianAtom) (fun _ => gaussianAtom_measurable), ?_⟩
  intro i
  have hid : IdentDistrib (fun sample => G sample i) id
      (inputLaw A.law) circularGaussianPairLaw :=
    ⟨(hc i).measurable.aemeasurable, measurable_id.aemeasurable,
      by simpa using (hc i).map_eq⟩
  exact hid.comp gaussianAtom_measurable

def denseModel (A : Proposition38.Atom) (N : ℕ) (hN : 0 < N) :=
  denseV3Model hN (denseAtom N) gaussianAtom gaussianAtom_moments (denseAtom_copies A N)

theorem normalizedDense_eq_circularGinibre (N : ℕ → ℕ) (k : ℕ) (sample : InputSpace) :
    normalizedDenseMatrixProcess (fun n => denseAtom (N n)) k sample =
      circularGinibreMatrix (N k) sample := by
  ext i j
  simp [normalizedDenseMatrixProcess, denseAtom, gaussianAtom, circularGinibreMatrix]

end BernoulliSection8.Section3Bridge
