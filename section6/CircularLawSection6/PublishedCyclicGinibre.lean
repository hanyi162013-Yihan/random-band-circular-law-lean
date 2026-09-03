import CircularLawSection6.PublishedLocalBulkTri
import CircularLawSection6.GinibreLimitingHardEdge
import CircularLawSection6.RoutedBandIdentification
import CircularLawSections56.Section5.PublishedSection3Model

/-! # Actual routed Gaussian cyclic matrices in the checked local comparison

Both matrices use precisely the finite product law in CyclicGinibreCdfInput.
Their independent atom records, dense normalization, signed cyclic columns,
ordered singular values and CDF transport are derived, not assumed.
-/

open MeasureTheory Set Filter Topology ShortRingAnchor Arxiv2410V3
open CircularLawSections56.Section5
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace CircularLawSection6

theorem matrixSquaredSingularCdf_eq_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (t : ℝ) :
    empiricalCdf
      (fun i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)) => A.toEuclideanLin.singularValues i ^ 2) t =
      matrixSquaredSingularAverage A (fun x => if x ≤ t then 1 else 0) := by
  classical
  simp only [empiricalCdf, matrixSquaredSingularAverage, Finset.sum_boole, Fintype.card_fin]

theorem matrixSquaredSingularCdfDistanceOn_shifted_reindex_right
    {ι κ λ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype λ] [DecidableEq λ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (e : κ ≃ λ) (z : ℂ) (R : ℝ) :
    matrixSquaredSingularCdfDistanceOn A (B.submatrix e.symm e.symm - z • 1) R =
      matrixSquaredSingularCdfDistanceOn A (B - z • 1) R := by
  unfold matrixSquaredSingularCdfDistanceOn empiricalCdfDistanceOn
  simp_rw [matrixSquaredSingularCdf_eq_average, matrixSquaredSingularAverage_shifted_reindex]

abbrev cyclicGinibreJointSample (M H : ℕ) :=
  (Fin M × Fin (2 * H + 1) → ℂ) × (ZMod M × ZMod M → ℂ)

def cyclicGinibreJointLaw (M H : ℕ) : Measure (cyclicGinibreJointSample M H) :=
  (Measure.pi (fun _ : Fin M × Fin (2 * H + 1) => circularComplexGaussian)).prod
    (cyclicAtomLaw M circularComplexGaussian)

instance cyclicGinibreJointLaw_isProbability (M H : ℕ) [NeZero M] :
    IsProbabilityMeasure (cyclicGinibreJointLaw M H) := by
  unfold cyclicGinibreJointLaw
  infer_instance

theorem cyclicColumn_eq_cyclicFinSlot {M H : ℕ} [NeZero M]
    (hfit : 2 * H + 1 ≤ M) (i : Fin M) (s : Fin (2 * H + 1)) :
    cyclicColumn hfit i s = cyclicFinSlot H i s := by
  apply (ZMod.finEquiv M).injective
  rw [section3_cyclicColumn_finEquiv, finEquiv_cyclicFinSlot]

def publishedJointCyclicModel {M H : ℕ} [NeZero M] {c₀ C₀ : ℝ}
    (weights : AdmissibleWeights H c₀ C₀) (hfit : 2 * H + 1 ≤ M) :
    RandomMatrixModelV3 M (cyclicGinibreJointSample M H) ℂ
      (cyclicGinibreJointLaw M H) circularComplexGaussian :=
  cyclicV3Model weights hfit (fun ω i s => ω.1 (i, s)) id
    circularComplexGaussian_publishedMoments
    (independentAtomCopies21_of_jointLaw _ _ _ measurePreserving_fst)

theorem publishedJointCyclicModel_matrix {M H : ℕ} [NeZero M] {c₀ C₀ : ℝ}
    (weights : AdmissibleWeights H c₀ C₀) (hfit : 2 * H + 1 ≤ M)
    (ω : cyclicGinibreJointSample M H) :
    (publishedJointCyclicModel weights hfit).matrix ω =
      routedBandMatrix (cyclicFinSlot H) (fun s => (Real.sqrt (weights.q s) : ℂ)) ω.1 := by
  ext i j
  change (∑ s, if cyclicColumn hfit i s = j then
    (Real.sqrt (weights.q s) : ℂ) * ω.1 (i, s) else 0) = _
  simp only [routedBandMatrix, cyclicColumn_eq_cyclicFinSlot, eq_comm]

def publishedJointDenseModel (M H : ℕ) [NeZero M] :
    RandomMatrixModelV3 M (cyclicGinibreJointSample M H) ℂ
      (cyclicGinibreJointLaw M H) circularComplexGaussian :=
  denseV3Model (NeZero.pos M) (fun ω i j => denseFinAtoms M ω.2 (i, j)) id
    circularComplexGaussian_publishedMoments
    (independentAtomCopies21_of_jointLaw _ _ _
      ((denseFinAtoms_measurePreserving M).comp measurePreserving_snd))

theorem publishedJointDenseModel_matrix (M H : ℕ) [NeZero M]
    (ω : cyclicGinibreJointSample M H) :
    (publishedJointDenseModel M H).matrix ω =
      (ginibreMatrix M ω.2).submatrix (ZMod.finEquiv M) (ZMod.finEquiv M) := by
  change (publishedGinibreModel M).matrix ω.2 = _
  exact publishedGinibreModel_matrix M ω.2

theorem cyclicGinibreCdfInput_of_published_models
    (M : ℕ → ℕ+) (H : ℕ → ℕ) {c₀ C₀ : ℝ}
    (weights : ∀ n, AdmissibleWeights (H n) c₀ C₀)
    (hfit : ∀ n, 2 * H n + 1 ≤ (M n : ℕ))
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop)
    (z : ℂ) (comparisonConstant : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hscaleA : ∀ᶠ n in atTop, (M n : ℝ) ^ epsilon ≤ (weights n).bandwidthParameter)
    (hscaleG : ∀ᶠ n in atTop, (M n : ℝ) ^ epsilon ≤ M n)
    (bbvA : ∀ n u, CanonicalBBVAt (publishedJointCyclicModel (weights n) (hfit n)) z
      (spectralParameter u (localBulkHeight epsilon (M n))) (weights n).bandwidthParameter
      (gaussianSection3ComparisonConstant comparisonConstant))
    (bbvG : ∀ n u, CanonicalBBVAt (publishedJointDenseModel (M n) (H n)) z
      (spectralParameter u (localBulkHeight epsilon (M n))) (M n)
      (gaussianSection3ComparisonConstant comparisonConstant)) :
    CyclicGinibreCdfInput M H (fun n s => (Real.sqrt ((weights n).q s) : ℂ)) z := by
  intro R hR
  have h := published_localBulk_tri_of_v3_models
    (fun n => cyclicGinibreJointLaw (M n) (H n)) circularComplexGaussian circularComplexGaussian
    hM (fun n => publishedJointCyclicModel (weights n) (hfit n))
    (fun n => publishedJointDenseModel (M n) (H n)) z (zero_le_one.trans hR)
    (gaussianSection3ComparisonConstant_ge_eight comparisonConstant) hepsilon
    (fun n => (weights n).bandwidthParameter) (fun n => (M n : ℝ))
    (fun n => cyclicVarianceProfile_isBandwidth (weights n) (hfit n))
    (fun n => denseVarianceProfile_isBandwidth (M n).pos) hscaleA hscaleG
    (fun _ => (le_max_right _ _).trans (le_max_right _ _))
    (fun _ => (le_max_right _ _).trans (le_max_right _ _)) bbvA bbvG
  apply tendstoInProbabilityTri_congr_ae _ _ _ _ _ h
  intro n
  filter_upwards with ω
  rw [publishedJointCyclicModel_matrix, publishedJointDenseModel_matrix]
  exact matrixSquaredSingularCdfDistanceOn_shifted_reindex_right _ _
    (ZMod.finEquiv (M n)).symm z R

end CircularLawSection6
