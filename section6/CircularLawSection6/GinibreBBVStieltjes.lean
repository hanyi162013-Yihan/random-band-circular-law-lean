import CircularLawSection6.GinibreGaussianLaw
import CircularLawSection6.PublishedStieltjesMean
import ShortRingAnchor.V3PointwiseProbability

/-! # Actual Ginibre Stieltjes limits from BBV alone

Both the mean and the random transform converge at every fixed positive
height. The actual Gaussian model, its moment constant, and concentration
are constructed internally. Neither a Ginibre spectral limit nor a
logarithmic-potential limit is an input. This is only the Stieltjes step of
the further logarithmic-potential argument.
-/

open MeasureTheory Filter Topology ShortRingAnchor Arxiv2410V3
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete
  (BBVComparisonInput gaussianSequenceLaw ginibreOnSequence)
open CircularLawSection6.GinibreReferenceSources (sequenceDenseModel)
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.GinibreBBV

theorem sequenceDenseModel_bbv_data (hBBV : BBVComparisonInput) :
    ∃ D : ℝ, 8 ≤ D ∧
      (∀ (N : ℕ) (hN : 0 < N),
        BVH.atomThirdMoment (sequenceDenseModel N hN) +
          BVH.complexGaussianThirdMomentConstant ≤ D) ∧
      (∀ (N : ℕ) (hN : 0 < N) (z eta : ℂ), 0 < eta.im →
        CanonicalBBVAt (sequenceDenseModel N hN) z eta (N : ℝ) D) := by
  obtain ⟨C, _hC, hcomp⟩ := hBBV
  refine ⟨gaussianSection3ComparisonConstant C,
    gaussianSection3ComparisonConstant_ge_eight C, ?_, ?_⟩
  · intro N hN
    change (∫ x : ℂ, ‖id x‖ ^ 3 ∂circularComplexGaussian) +
      BVH.complexGaussianThirdMomentConstant ≤ gaussianSection3ComparisonConstant C
    exact (le_max_right _ _).trans (le_max_right _ _)
  · intro N hN z eta heta
    exact CircularLawSections56.Section5.PublishedSection3Concrete.canonicalBBVAt_mono
      (hcomp (ℕ → ℂ) ℂ gaussianSequenceLaw circularComplexGaussian N hN
        (sequenceDenseModel N hN) (N : ℝ) (denseVarianceProfile_isBandwidth hN)
        z eta heta)
      (by exact_mod_cast hN) heta (le_max_left _ _)

theorem ginibre_meanStieltjes_tendsto_of_bbv
    (hBBV : BBVComparisonInput) (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop) (z eta : ℂ) (heta : 0 < eta.im) :
    Tendsto (fun n => ∫ ω, stieltjesTrace (ginibreOnSequence (N n) ω) z eta
      ∂gaussianSequenceLaw) atTop (𝓝 (freeDysonStieltjes z eta)) := by
  obtain ⟨D, hD, hthird, hcomp⟩ := sequenceDenseModel_bbv_data hBBV
  exact published_dense_meanStieltjes_tendsto (fun _ => gaussianSequenceLaw)
    circularComplexGaussian N hN (fun n => sequenceDenseModel (N n) (hNpos n))
    z heta hD (fun n => denseVarianceProfile_isBandwidth (hNpos n))
    (fun n => hthird (N n) (hNpos n))
    (fun n => hcomp (N n) (hNpos n) z eta heta)

theorem ginibre_stieltjes_inMeasure_of_bbv
    (hBBV : BBVComparisonInput) (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop) (z eta : ℂ) (heta : 0 < eta.im) :
    TendstoInMeasure gaussianSequenceLaw
      (fun n ω => stieltjesTrace (ginibreOnSequence (N n) ω) z eta)
      atTop (fun _ => freeDysonStieltjes z eta) := by
  obtain ⟨D, hD, hthird, hcomp⟩ := sequenceDenseModel_bbv_data hBBV
  let model := fun n => sequenceDenseModel (N n) (hNpos n)
  let good := fun n => v3TraceConcentrationGood (model n) z eta
  have hn2 : ∀ᶠ n in atTop, 2 ≤ N n := hN.eventually (eventually_ge_atTop 2)
  have hbadRate : Tendsto (fun n => ENNReal.ofReal ((N n : ℝ) ^ (-(10 : ℝ))))
      atTop (𝓝 0) := by
    have hreal : Tendsto (fun n => (N n : ℝ) ^ (-(10 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp
        (tendsto_natCast_atTop_atTop.comp hN)
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hbad : Tendsto (fun n => gaussianSequenceLaw (good n)ᶜ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbadRate
      (Eventually.of_forall fun _ => zero_le)
    filter_upwards [hn2] with n hn
    exact v3_concentration_bad_le hn (model n) z heta
  have hrates := hN.eventually (eventually_formula311Error_le_explicit_nat_allEta
    (show 0 ≤ D by linarith) (by norm_num : (0 : ℝ) ≤ 32)
    (by norm_num : (0 : ℝ) < 1 / 2))
  have hscale := dense_fixedHeight_scale_eventually N hN heta
  have hrate : Tendsto (fun n => (N n : ℝ) ^ (-((1 / 2 : ℝ) / 32)))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp
      (tendsto_natCast_atTop_atTop.comp hN)
  change ConvergesInProbability gaussianSequenceLaw
    (fun n ω => stieltjesTrace (ginibreOnSequence (N n) ω) z eta)
    (freeDysonStieltjes z eta)
  rw [convergesInProbability_iff_norm]
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad
    (Eventually.of_forall fun _ => zero_le)
  filter_upwards [hn2, hrates, hscale, hrate.eventually (gt_mem_nhds hε)]
    with n hn hr hs hsmall
  apply measure_mono
  intro ω hω hgood
  have hnR : (1 : ℝ) ≤ N n := by exact_mod_cast (show 1 ≤ N n by omega)
  have hb := (v3_formula311_canonical_on_good hn (model n) z heta
    (denseVarianceProfile_isBandwidth (hNpos n)) hD
    (hthird (N n) (hNpos n)) (hcomp (N n) (hNpos n) z eta heta) hgood).trans
      (hr (N n) eta.im hnR le_rfl heta hs)
  exact (not_le_of_gt (hb.trans_lt hsmall)) hω

theorem ginibre_stieltjes_error_tri_of_bbv
    (hBBV : BBVComparisonInput) (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop) (z eta : ℂ) (heta : 0 < eta.im) :
    TendstoInProbabilityTri (fun _ => gaussianSequenceLaw)
      (fun n ω => ‖stieltjesTrace (ginibreOnSequence (N n) ω) z eta -
        freeDysonStieltjes z eta‖) 0 := by
  have h := (convergesInProbability_iff_norm).1
    (ginibre_stieltjes_inMeasure_of_bbv hBBV N hNpos hN z eta heta)
  have hnorm : ConvergesInProbability gaussianSequenceLaw
      (fun n ω => ‖stieltjesTrace (ginibreOnSequence (N n) ω) z eta -
        freeDysonStieltjes z eta‖) 0 := by
    rw [convergesInProbability_iff_norm]
    intro ε hε
    simpa only [sub_zero, Real.norm_eq_abs, abs_norm] using h ε hε
  exact (tendstoInMeasure_iff_tri gaussianSequenceLaw _ 0).1 hnorm

end CircularLawSection6.GinibreBBV
