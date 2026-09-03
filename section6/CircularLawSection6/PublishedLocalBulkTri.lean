import ShortRingAnchor.Lemma35FromV3
import CircularLawSection6.FiniteCdfCutoffComparison

/-! # The checked Section 3 local comparison on varying probability spaces

The finite good-event estimate and finite CDF bound are called directly from
Section 3. This permits the actual finite-dimensional product space at each
matrix size. No common infinite product, local CDF conclusion, or independence
between the two ensembles is assumed.
-/

open MeasureTheory Set Filter Topology ShortRingAnchor Arxiv2410V3
open CircularLawSections56.Section5
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem tendstoInProbabilityTri_of_good_bound
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (good : ∀ n, Set (Ω n)) (b : ℕ → ℝ)
    (hbad : Tendsto (fun n => μ n (good n)ᶜ) atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ ω ∈ good n, |X n ω| ≤ b n) :
    TendstoInProbabilityTri μ X 0 := by
  have hbadReal : Tendsto (fun n => (μ n).real (good n)ᶜ) atTop (𝓝 0) := by
    simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_apply] using
      (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ∞)).comp hbad
  intro ε hε
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hbadReal
  filter_upwards [hbound, hb.eventually (gt_mem_nhds hε)] with n hn hbε
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  change ε ≤ |X n ω - 0| at hω
  rw [sub_zero] at hω
  change ω ∉ good n
  intro hg
  exact (not_le.mpr ((hn ω hg).trans_lt hbε)) hω

theorem published_localBulk_tri_of_v3_models
    {Ω : ℕ → Type*} {ΞA ΞG : Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace ΞA] [MeasurableSpace ΞG]
    (μ : ∀ n, Measure (Ω n)) (νA : Measure ΞA) (νG : Measure ΞG)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure νA] [IsProbabilityMeasure νG]
    {M : ℕ → ℕ} (hM : Tendsto M atTop atTop)
    (modelA : ∀ n, RandomMatrixModelV3 (M n) (Ω n) ΞA (μ n) νA)
    (modelG : ∀ n, RandomMatrixModelV3 (M n) (Ω n) ΞG (μ n) νG)
    (z : ℂ) {R C epsilon : ℝ} (hR : 0 ≤ R) (hC : 8 ≤ C) (hepsilon : 0 < epsilon)
    (BA BG : ℕ → ℝ)
    (hBA : ∀ n, IsBandwidth (modelA n).profile (BA n))
    (hBG : ∀ n, IsBandwidth (modelG n).profile (BG n))
    (hscaleA : ∀ᶠ n in atTop, (M n : ℝ) ^ epsilon ≤ BA n)
    (hscaleG : ∀ᶠ n in atTop, (M n : ℝ) ^ epsilon ≤ BG n)
    (hthirdA : ∀ n, BVH.atomThirdMoment (modelA n) + BVH.complexGaussianThirdMomentConstant ≤ C)
    (hthirdG : ∀ n, BVH.atomThirdMoment (modelG n) + BVH.complexGaussianThirdMomentConstant ≤ C)
    (bbvA : ∀ n u, CanonicalBBVAt (modelA n) z
      (spectralParameter u (localBulkHeight epsilon (M n))) (BA n) C)
    (bbvG : ∀ n u, CanonicalBBVAt (modelG n) z
      (spectralParameter u (localBulkHeight epsilon (M n))) (BG n) C) :
    TendstoInProbabilityTri μ (fun n ω => matrixSquaredSingularCdfDistanceOn
      ((modelA n).matrix ω - z • 1) ((modelG n).matrix ω - z • 1) R) 0 := by
  let d := localBulkRateExponent epsilon
  let v := fun n => localBulkHeight epsilon (M n)
  let good := fun n => matrixLocalBulkGood (modelA n).matrix (modelG n).matrix z (v n) R d
  have hd0 : 0 < d := localBulkRateExponent_pos hepsilon
  have hd1 : d ≤ 1 := by
    have he : localBulkEffectiveExponent epsilon ≤ 1 := min_le_right _ _
    dsimp [d, localBulkRateExponent]
    linarith
  have hn2 : ∀ᶠ n in atTop, 2 ≤ M n := hM.eventually (eventually_ge_atTop 2)
  have herr := hM.eventually (eventually_formula311Error_localBulkHeight
    (show 0 ≤ C by linarith) hepsilon)
  have hscales : ∀ᶠ n in atTop,
      2 ≤ M n ∧ 0 < v n ∧
      formula311Error (M n : ℝ) (BA n) (v n) C 32 ≤ (M n : ℝ) ^ (-d) ∧
      formula311Error (M n : ℝ) (BG n) (v n) C 32 ≤ (M n : ℝ) ^ (-d) := by
    filter_upwards [hn2, herr, hscaleA, hscaleG] with n hn he ha hg
    let : NeZero (M n) := ⟨by omega⟩
    have hpos : (0 : ℝ) < M n := by exact_mod_cast (show 0 < M n by omega)
    refine ⟨hn, Real.rpow_pos_of_pos hpos _, ?_, ?_⟩
    · exact he (BA n) (one_le_bandwidth _ (hBA n))
        (by simpa using bandwidth_le_card _ (hBA n)) ha
    · exact he (BG n) (one_le_bandwidth _ (hBG n))
        (by simpa using bandwidth_le_card _ (hBG n)) hg
  have hbad : Tendsto (fun n => μ n (good n)ᶜ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds (matrixLocalBulk_failure_budget_tendsto_zero R hM)
      (Eventually.of_forall fun _ => (show (0 : ENNReal) ≤ _ from zero_le))
    filter_upwards [hscales] with n hn
    exact matrixLocalBulkGood_bad_le hn.1 (modelA n) (modelG n) z hn.2.1 hR
      (hBA n) (hBG n) hC (hthirdA n) (hthirdG n) (bbvA n) (bbvG n)
      hn.2.2.1 hn.2.2.2
  have hrate := localBulk_rate_tendsto_zero hepsilon hM
  have hsmall : ∀ᶠ n in atTop, 3 * Real.sqrt (v n) ≤ 1 := by
    filter_upwards [hn2, hrate.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))]
      with n hn hr
    have hnR : (1 : ℝ) ≤ M n := by exact_mod_cast (show 1 ≤ M n by omega)
    have hs := sqrt_localBulkHeight_le_rate hepsilon hnR
    dsimp [v]
    linarith
  apply tendstoInProbabilityTri_of_good_bound μ _ good
    (fun n => ((8 * R + 72) / Real.pi) * (M n : ℝ) ^ (-d)) hbad
    (by simpa only [mul_zero] using hrate.const_mul ((8 * R + 72) / Real.pi))
  filter_upwards [hn2, hsmall] with n hn hs
  intro ω hω
  let : NeZero (M n) := ⟨by omega⟩
  have hnR : (1 : ℝ) ≤ M n := by exact_mod_cast (show 1 ≤ M n by omega)
  have h := matrixLocalBulkGood_cdf_bound hn (modelA n).matrix (modelG n).matrix z
    hR hd0.le hd1 (localBulkHeight_lower hnR) hs hω
  have hroot := sqrt_localBulkHeight_le_rate hepsilon hnR
  have hid : matrixSquaredSingularCdfDistanceOn
      ((modelA n).matrix ω - z • 1) ((modelG n).matrix ω - z • 1) R =
      empiricalCdfDistanceOn 0 (R ^ 2)
        (fun i => shiftedSingularValueFamily ((modelA n).matrix ω) z i ^ 2)
        (fun i => shiftedSingularValueFamily ((modelG n).matrix ω) z i ^ 2) := by
    simp only [matrixSquaredSingularCdfDistanceOn, finrank_euclideanSpace,
      Fintype.card_fin, shiftedSingularValueFamily, shiftedSingularValue, matrixSingularValue]
  rw [hid, abs_of_nonneg (empiricalCdfDistanceOn_nonneg (sq_nonneg R) _ _)]
  refine h.trans ?_
  calc
    _ ≤ ((8 * R + 40) * (M n : ℝ) ^ (-d) + 32 * (M n : ℝ) ^ (-d)) / Real.pi :=
      div_le_div_of_nonneg_right
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hroot (by norm_num))) Real.pi_pos.le
    _ = _ := by ring

end CircularLawSection6
