import ShortRingAnchor.MatrixLocalBulk
import ShortRingAnchor.V3PointwiseProbability

/-!
# Lemma 3.5: the compact matrix good event has high probability

The two v3 ensembles need not be independent of each other. The only
external comparison conclusion is the centralized named BBV hypothesis.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace ShortRingAnchor
open Arxiv2410V3

variable {Omega OmegaXiA OmegaXiG : Type*}
  [MeasurableSpace Omega] [MeasurableSpace OmegaXiA] [MeasurableSpace OmegaXiG]
  {mu : Measure Omega} {nuA : Measure OmegaXiA} {nuG : Measure OmegaXiG}
  [IsProbabilityMeasure mu] [IsProbabilityMeasure nuA] [IsProbabilityMeasure nuG]

/-- v3 (3.11) and the Lemma 3.5 finite net: the concrete event has
failure probability at most `2 (2R+4) n^(-8)`. The only assumed
comparison conclusion is BBV for each canonical circularized ensemble. -/
theorem matrixLocalBulkGood_bad_le {n : ℕ} (hn : 2 ≤ n)
    (modelA : RandomMatrixModelV3 n Omega OmegaXiA mu nuA)
    (modelG : RandomMatrixModelV3 n Omega OmegaXiG mu nuG)
    (z : ℂ) {v R d BA BG C : ℝ} (hv : 0 < v) (hR : 0 ≤ R)
    (hBA : IsBandwidth modelA.profile BA) (hBG : IsBandwidth modelG.profile BG)
    (hC : 8 ≤ C)
    (hthirdA : BVH.atomThirdMoment modelA + BVH.complexGaussianThirdMomentConstant ≤ C)
    (hthirdG : BVH.atomThirdMoment modelG + BVH.complexGaussianThirdMomentConstant ≤ C)
    (bbvA : ∀ u, CanonicalBBVAt modelA z (spectralParameter u v) BA C)
    (bbvG : ∀ u, CanonicalBBVAt modelG z (spectralParameter u v) BG C)
    (herrorA : formula311Error (n : ℝ) BA v C 32 ≤ (n : ℝ) ^ (-d))
    (herrorG : formula311Error (n : ℝ) BG v C 32 ≤ (n : ℝ) ^ (-d)) :
    mu (matrixLocalBulkGood modelA.matrix modelG.matrix z v R d)ᶜ ≤
      2 * ENNReal.ofReal ((2 * R + 4) * (n : ℝ) ^ (-(8 : ℝ))) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have heta (u : ℝ) : 0 < (spectralParameter u v).im := by
    simpa [spectralParameter] using hv
  have h := measure_compactStieltjesGridGood_compl_le mu
    (fun sample u => stieltjesTrace (modelA.matrix sample) z (spectralParameter u v))
    (fun sample u => stieltjesTrace (modelG.matrix sample) z (spectralParameter u v))
    (fun u => freeDysonStieltjes z (spectralParameter u v)) hnR
    (show 0 ≤ R + 1 by positivity)
    (fun i => v3_pointwise_comparison_bad_le hn modelA z (heta _) hBA hC hthirdA
      (bbvA _) (by simpa [spectralParameter] using herrorA))
    (fun i => v3_pointwise_comparison_bad_le hn modelG z (heta _) hBG hC hthirdG
      (bbvG _) (by simpa [spectralParameter] using herrorG))
  convert h using 1 <;> congr 2 <;> ring

end ShortRingAnchor
