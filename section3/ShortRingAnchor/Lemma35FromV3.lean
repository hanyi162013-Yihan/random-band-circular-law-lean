import ShortRingAnchor.V3MatrixLocalBulk
import ShortRingAnchor.LocalBulkPolynomialScales
import ShortRingAnchor.PoissonSmoothingProbability

/-!
# Lemma 3.5 from actual v3 random-matrix models

This discharges the named local CDF interface for two ensembles satisfying
the v3 entry laws and a positive polynomial bandwidth lower bound. The
only external theorem premise is the named canonical BBV comparison.
The proof uses a common explicit exponent, not a point-dependent choice.
-/

open Filter Set MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace ShortRingAnchor
open Arxiv2410V3

/-- Lemma 3.5: the finite-grid failure budget tends to zero along growing dimensions. -/
theorem matrixLocalBulk_failure_budget_tendsto_zero (R : ℝ)
    {M : ℕ → ℕ} (hM : Tendsto M atTop atTop) :
    Tendsto (fun k => 2 * ENNReal.ofReal ((2 * R + 4) *
      (M k : ℝ) ^ (-(8 : ℝ)))) atTop (nhds 0) := by
  have hp : Tendsto (fun k => (M k : ℝ) ^ (-(8 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_atTop_zero_of_neg (by norm_num : -(8 : ℝ) < 0)).comp
      (tendsto_natCast_atTop_atTop.comp hM)
  have hr := ENNReal.tendsto_ofReal (hp.const_mul (2 * R + 4))
  have h := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hr
    (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
  simpa using h

/-- Manuscript Lemma 3.5 / (3.11), with actual shifted singular values.

All matrix trace identities, smoothing, uniformization, McDiarmid, BVH,
Gaussian realization and scale arithmetic are internal. The explicitly
named BBV hypotheses are the sole external comparison conclusions.
There is no restriction `|z| ≤ 2.5`, no radius-five restriction, and no
nonsingularity premise. No independence between the two ensembles is used.
-/
theorem lemma35LocalBulkComparisonInput_of_v3_models
    {Omega OmegaXiA OmegaXiG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXiA] [MeasurableSpace OmegaXiG]
    {mu : Measure Omega} {nuA : Measure OmegaXiA} {nuG : Measure OmegaXiG}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nuA] [IsProbabilityMeasure nuG]
    {M : ℕ → ℕ} (hM : Tendsto M atTop atTop)
    (modelA : ∀ k, RandomMatrixModelV3 (M k) Omega OmegaXiA mu nuA)
    (modelG : ∀ k, RandomMatrixModelV3 (M k) Omega OmegaXiG mu nuG)
    (z : ℂ) {R C epsilon : ℝ} (hR : 0 ≤ R) (hC : 8 ≤ C)
    (hepsilon : 0 < epsilon) (BA BG : ℕ → ℝ)
    (hBA : ∀ k, IsBandwidth (modelA k).profile (BA k))
    (hBG : ∀ k, IsBandwidth (modelG k).profile (BG k))
    (hscaleA : ∀ᶠ k in atTop, (M k : ℝ) ^ epsilon ≤ BA k)
    (hscaleG : ∀ᶠ k in atTop, (M k : ℝ) ^ epsilon ≤ BG k)
    (hthirdA : ∀ k, BVH.atomThirdMoment (modelA k) + BVH.complexGaussianThirdMomentConstant ≤ C)
    (hthirdG : ∀ k, BVH.atomThirdMoment (modelG k) + BVH.complexGaussianThirdMomentConstant ≤ C)
    (bbvA : ∀ k u, CanonicalBBVAt (modelA k) z
      (spectralParameter u (localBulkHeight epsilon (M k))) (BA k) C)
    (bbvG : ∀ k u, CanonicalBBVAt (modelG k) z
      (spectralParameter u (localBulkHeight epsilon (M k))) (BG k) C) :
    Lemma35LocalBulkComparisonInput mu
      (shiftedSingularValueProcess (fun k => (modelA k).matrix) z)
      (shiftedSingularValueProcess (fun k => (modelG k).matrix) z)
      R (fun k => (M k : ℝ) ^ (-localBulkRateExponent epsilon)) := by
  let d := localBulkRateExponent epsilon
  let v := fun k => localBulkHeight epsilon (M k)
  let good := fun k => matrixLocalBulkGood (modelA k).matrix (modelG k).matrix z (v k) R d
  have hd0 : 0 < d := localBulkRateExponent_pos hepsilon
  have hd1 : d ≤ 1 := by
    have he : localBulkEffectiveExponent epsilon ≤ 1 := min_le_right _ _
    dsimp [d, localBulkRateExponent]
    linarith
  have hn2 : ∀ᶠ k in atTop, 2 ≤ M k := hM.eventually (eventually_ge_atTop 2)
  have herr := hM.eventually (eventually_formula311Error_localBulkHeight
    (show 0 ≤ C by linarith) hepsilon)
  have hscales : ∀ᶠ k in atTop,
      2 ≤ M k ∧ 0 < v k ∧
      formula311Error (M k : ℝ) (BA k) (v k) C 32 ≤ (M k : ℝ) ^ (-d) ∧
      formula311Error (M k : ℝ) (BG k) (v k) C 32 ≤ (M k : ℝ) ^ (-d) := by
    filter_upwards [hn2, herr, hscaleA, hscaleG] with k hk he ha hg
    let _ : NeZero (M k) := ⟨by omega⟩
    have hpos : (0 : ℝ) < M k := by exact_mod_cast (show 0 < M k by omega)
    refine ⟨hk, Real.rpow_pos_of_pos hpos _, ?_, ?_⟩
    · exact he (BA k) (one_le_bandwidth _ (hBA k))
        (by simpa using bandwidth_le_card _ (hBA k)) ha
    · exact he (BG k) (one_le_bandwidth _ (hBG k))
        (by simpa using bandwidth_le_card _ (hBG k)) hg
  have hbad : Tendsto (fun k => mu (good k)ᶜ) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds (matrixLocalBulk_failure_budget_tendsto_zero R hM)
      (Eventually.of_forall (fun k => (show (0 : ℝ≥0∞) ≤ mu (good k)ᶜ from zero_le)))
    filter_upwards [hscales] with k hk
    exact matrixLocalBulkGood_bad_le hk.1 (modelA k) (modelG k) z hk.2.1 hR
      (hBA k) (hBG k) hC (hthirdA k) (hthirdG k) (bbvA k) (bbvG k)
      hk.2.2.1 hk.2.2.2
  have hrate := localBulk_rate_tendsto_zero hepsilon hM
  have hsmall : ∀ᶠ k in atTop, 3 * Real.sqrt (v k) ≤ 1 := by
    filter_upwards [hn2, hrate.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))]
      with k hk hr
    have hnR : (1 : ℝ) ≤ M k := by exact_mod_cast (show 1 ≤ M k by omega)
    have hs := sqrt_localBulkHeight_le_rate hepsilon hnR
    dsimp [v]
    linarith
  apply isBigOInProbability_of_bound_on_good
    (good := good) (K := (8 * R + 72) / Real.pi) (by positivity) hbad
  filter_upwards [hn2, hsmall] with k hk hs
  intro sample hsample
  let _ : NeZero (M k) := ⟨by omega⟩
  have hnR : (1 : ℝ) ≤ M k := by exact_mod_cast (show 1 ≤ M k by omega)
  change ‖empiricalCdfDistanceOn 0 (R ^ 2)
    (fun i => shiftedSingularValueFamily ((modelA k).matrix sample) z i ^ 2)
    (fun i => shiftedSingularValueFamily ((modelG k).matrix sample) z i ^ 2)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (empiricalCdfDistanceOn_nonneg (sq_nonneg R) _ _)]
  have h := matrixLocalBulkGood_cdf_bound hk (modelA k).matrix (modelG k).matrix z
    hR hd0.le hd1 (localBulkHeight_lower hnR) hs hsample
  refine h.trans ?_
  have hroot := sqrt_localBulkHeight_le_rate hepsilon hnR
  have hpow : 0 ≤ (M k : ℝ) ^ (-d) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [abs_of_nonneg hpow]
  calc
    ((8 * R + 40) * (M k : ℝ) ^ (-d) + 32 * Real.sqrt (localBulkHeight epsilon (M k))) /
        Real.pi ≤ ((8 * R + 40) * (M k : ℝ) ^ (-d) + 32 * (M k : ℝ) ^ (-d)) / Real.pi :=
      div_le_div_of_nonneg_right
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 32)))
        Real.pi_pos.le
    _ = _ := by ring

end ShortRingAnchor
