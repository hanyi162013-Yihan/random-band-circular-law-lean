import CircularLawSection6.DenseProfileLSV
import CircularLawSection6.DenseProfileScales
import CircularLawSections56.Section5.PublishedSection3Literature
import ShortRingAnchor.HermitizationCountingFromV3
import ShortRingAnchor.Lemma35FromV3
import ShortRingAnchor.DensityNonsingularity
import ShortRingAnchor.Proposition36

/-! # General Proposition 3.6 for the actual dense profile

The target is the full profile matrix, not a short-ring surrogate. Its
least-value estimate, all-cutoff count, bulk comparison, exact moments and
Ginibre nonsingularity are constructed. Only uniform BBV and the classical
BC12 statements for actual Ginibre remain external sources.
-/

open MeasureTheory ProbabilityTheory Filter Topology ShortRingAnchor Arxiv2410V3
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete
  (Sample BBVComparisonInput BC12GinibreInput canonicalBBVAt_mono bc12_on_sampleLaw
    denseSamples denseSamples_measurePreserving actualGinibre)
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

namespace CircularLawSection6.DenseProfile

theorem referenceCopies (N : ℕ) :
    IndependentAtomCopies21 law circularComplexGaussian id
      (fun ij : Fin N × Fin N => fun ω => denseSamples N ω ij) :=
  independentAtomCopies21_of_jointLaw law circularComplexGaussian _
    (denseSamples_measurePreserving circularComplexGaussian N)

def referenceModel (N : ℕ) [NeZero N] :
    RandomMatrixModelV3 N Sample ℂ law circularComplexGaussian :=
  denseV3Model (NeZero.pos N) (fun ω i j => denseSamples N ω (i, j)) id
    circularComplexGaussian_publishedMoments (referenceCopies N)

theorem referenceModel_matrix (N : ℕ) [NeZero N] :
    (referenceModel N).matrix = actualGinibre N := rfl

theorem reference_rowMoments (M : ℕ → ℕ) [∀ n, NeZero (M n)] :
    CenteredMatrixRowSecondMomentInputs law (fun n => actualGinibre (M n)) 1 :=
  DenseAtomMomentCopies21.centeredMatrixRowSecondMomentInputs
    (fun n ω i j => denseSamples (M n) ω (i, j))
    (denseAtomMomentCopies21_of_independentAtomCopies
      (fun n ω i j => denseSamples (M n) ω (i, j))
      circularComplexGaussian_publishedMoments (fun n => referenceCopies (M n)))

theorem reference_nonsingular (M : ℕ → ℕ) [∀ n, NeZero (M n)] (z : ℂ) :
    ShiftedNonsingularInProbability law (fun n => actualGinibre (M n)) z :=
  normalizedDense_shiftedNonsingularInProbability_of_independent_density
    (fun n ω i j => denseSamples (M n) ω (i, j)) (fun n => NeZero.pos (M n))
    (fun n i j => ((referenceCopies (M n)).measurable (i, j)).aemeasurable)
    (fun n => (referenceCopies (M n)).independent)
    (fun n i j => AtomDensityAlternative21.of_identDistrib
      ((referenceCopies (M n)).law (i, j)) circularComplexGaussian_publishedDensityAlternative) z

theorem actualMatrix_conclusion
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    (M : ℕ → ℕ) [∀ n, NeZero (M n)]
    (q : ∀ n, ZMod (M n) → ℝ) (hq : ∀ n s, 0 < q n s)
    (hsum : ∀ n, ∑ s, q n s = 1) {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ n s, c / (M n : ℝ) ≤ q n s)
    (hupper : ∀ n s, q n s ≤ C / (M n : ℝ))
    (hM : Tendsto M atTop atTop) (z : ℂ) :
    Proposition36SequenceConclusion law M (fun n => actualMatrix (M n) (q n)) z := by
  obtain ⟨C₀, _hC₀, hBBV₀⟩ := hBBV
  let modelA (n : ℕ) := v3Model (M n) (q n) (hq n) (hsum n)
  let modelG (n : ℕ) := referenceModel (M n)
  let B (n : ℕ) := bandwidth (M n) (q n)
  let K : ℝ := C ^ (1 / 8 : ℝ)
  let R (r : ℕ) : ℝ := (r : ℝ) + (Real.sqrt (Real.exp 1) + 1)
  have hK : 0 < K := Real.rpow_pos_of_pos hC _
  have hMpos (n : ℕ) : 0 < M n := NeZero.pos (M n)
  have hBA (n : ℕ) : IsBandwidth (modelA n).profile (B n) :=
    isBandwidth (M n) (q n) (hq n) (hsum n)
  have hBG (n : ℕ) : IsBandwidth (modelG n).profile (M n : ℝ) :=
    denseVarianceProfile_isBandwidth (hMpos n)
  have hBlower (n : ℕ) : (M n : ℝ) / C ≤ B n :=
    bandwidth_lower (M n) (q n) (hq n) hC (hupper n)
  have hthirdA (n : ℕ) : BVH.atomThirdMoment (modelA n) + BVH.complexGaussianThirdMomentConstant ≤
      gaussianSection3ComparisonConstant C₀ :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hthirdG (n : ℕ) : BVH.atomThirdMoment (modelG n) + BVH.complexGaussianThirdMomentConstant ≤
      gaussianSection3ComparisonConstant C₀ :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hbbvA (n : ℕ) (η : ℂ) (hη : 0 < η.im) :
      CanonicalBBVAt (modelA n) z η (B n) (gaussianSection3ComparisonConstant C₀) :=
    canonicalBBVAt_mono
      (hBBV₀ Sample ℂ law circularComplexGaussian (M n) (hMpos n) (modelA n) (B n) (hBA n) z η hη)
      (hBA n).pos hη (le_max_left _ _)
  have hbbvG (n : ℕ) (η : ℂ) (hη : 0 < η.im) :
      CanonicalBBVAt (modelG n) z η (M n : ℝ) (gaussianSection3ComparisonConstant C₀) :=
    canonicalBBVAt_mono
      (hBBV₀ Sample ℂ law circularComplexGaussian (M n) (hMpos n) (modelG n) (M n) (hBG n) z η hη)
      (hBG n).pos hη (le_max_left _ _)
  obtain ⟨goodHerm, hHerm⟩ := hermitizationAllCutoffsCountingInput_of_v3_model
    hMpos hM modelA z (gaussianSection3ComparisonConstant_ge_eight C₀)
    (by norm_num [denseTau] : 0 < denseTau) B hBA hthirdA
    (fun n v hv => hbbvA n (spectralParameter 0 v) (by simpa [spectralParameter] using hv))
  have hAllCount := proposition34AllCutoffsInput_of_hermitization
    (fun n => actualMatrix (M n) (q n)) z
    (fun n => B n ^ (-(1 / 8 : ℝ)) * (M n : ℝ) ^ denseTau)
    (fun _ => 6) goodHerm hHerm
  obtain ⟨goodCount, hCount⟩ := hAllCount.specialize_eventually
    (bandwidth_cutoff_le_source_eventually M B hMpos hM hC hBlower)
  obtain ⟨goodLSV, hLSV⟩ := actualMatrix_minimumInput M q hq hsum hc hlower hupper hM z
    (by norm_num [denseKappa] : 0 < denseKappa)
  have hLSVAll := theorem31LeastSingularValueInput_of_minimum hMpos
    (fun n => actualMatrix (M n) (q n)) z (sourceHardEdgeScale M M denseKappa) goodLSV hLSV
  obtain ⟨p, hp, hBC12Negative, hBC12Full⟩ :=
    bc12_on_sampleLaw hBC12 circularComplexGaussian M hMpos hM z
  have hscaleA := eventually_bandwidth_ge_half_power M B hM hC hBlower
  have hscaleG : ∀ᶠ n in atTop, (M n : ℝ) ^ (1 / 2 : ℝ) ≤ (M n : ℝ) :=
    eventually_bandwidth_ge_half_power M (fun n => (M n : ℝ)) hM zero_lt_one
      (fun n => by rw [div_one])
  have hheight (n : ℕ) (u : ℝ) :
      0 < (spectralParameter u (localBulkHeight (1 / 2) (M n))).im := by
    have hh : 0 < localBulkHeight (1 / 2) (M n) := by
      unfold localBulkHeight
      exact Real.rpow_pos_of_pos (by exact_mod_cast hMpos n) _
    simpa [spectralParameter] using hh
  have hR (r : ℕ) : Real.sqrt (Real.exp 1) < R r := by
    have hr := Nat.cast_nonneg (α := ℝ) r
    dsimp [R]
    linarith
  have hBulk (r : ℕ) : Lemma35LocalBulkComparisonInput law
      (shiftedSingularValueProcess (fun n => actualMatrix (M n) (q n)) z)
      (shiftedSingularValueProcess (fun n => actualGinibre (M n)) z)
      (R r) (fun n => (M n : ℝ) ^ (-localBulkRateExponent (1 / 2))) :=
    lemma35LocalBulkComparisonInput_of_v3_models hM modelA modelG z
      ((Real.sqrt_nonneg _).trans (hR r).le)
      (gaussianSection3ComparisonConstant_ge_eight C₀) (by norm_num : (0 : ℝ) < 1 / 2)
      B (fun n => (M n : ℝ)) hBA hBG hscaleA hscaleG hthirdA hthirdG
      (fun n u => hbbvA n _ (hheight n u)) (fun n u => hbbvG n _ (hheight n u))
  exact proposition36_matrix_form_highProbability
    (fun n => actualMatrix (M n) (q n)) (fun n => actualGinibre (M n)) z
    (sourceCutoff M K 1 denseTau) (fun _ => 2 * 6)
    (sourceHardEdgeScale M M denseKappa) R
    (fun _ n => (M n : ℝ) ^ (-localBulkRateExponent (1 / 2)))
    p (1 + ‖z‖ ^ 2) (1 + ‖z‖ ^ 2)
    (fun n => sourceCutoff_pos hK (hMpos n)) (fun _ => sourceCutoff_le_one)
    (dense_cutoff_tendsto_zero M hM K)
    (fun n => sourceHardEdgeScale_nonneg (hMpos n) (hMpos n))
    (reference_nonsingular M z) goodLSV goodCount hLSVAll hCount
    (dense_hardEdge_error_tendsto_zero M hM hK (by norm_num)) hBulk
    (fun r => dense_bulk_cutoff_tendsto_zero M hM hK
      ((Real.sqrt_nonneg _).trans_lt (hR r))
      (localBulkRateExponent_pos (by norm_num : (0 : ℝ) < 1 / 2)))
    hp hBC12Negative hBC12Full
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop) hR
    (upperSecondMomentInputs_of_centered_matrix_entries
      (fun n => actualMatrix (M n) (q n)) (fun n => actualGinibre (M n)) z 1 1
      (actualMatrix_rowMoments M q hq hsum) (reference_rowMoments M))

theorem profile_conclusion
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    (p : NoncompactProfile) (M : ℕ → ℕ) [∀ n, NeZero (M n)]
    (W : ℕ → ℝ) (hM : Tendsto M atTop atTop) {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ n, δ * (M n : ℝ) ≤ W n) (z : ℂ) :
    Proposition36SequenceConclusion law M (fun n => actualMatrix (M n) (p.weight (M n) (W n))) z := by
  obtain ⟨c, C, hc, hC, hb⟩ := p.dense_weights_comparable hδ
  exact actualMatrix_conclusion hBBV hBC12 M (fun n => p.weight (M n) (W n))
    (fun n s => p.weight_pos _ _ s) (fun n => p.sum_weight _ _) hc hC
    (fun n s => (hb (M n) (W n) (hdense n) s).1)
    (fun n s => (hb (M n) (W n) (hdense n) s).2) hM z

end CircularLawSection6.DenseProfile
