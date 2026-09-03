/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34Canonical.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.BVH.GaussianConstruction
import Vendor.Arxiv2410.V3.Proposition34OnlyBBV

/-!
# Canonical realization of v3 Proposition 3.4 and Corollary 3.5

`BVH/GaussianConstruction.lean` constructs the matching Gaussian companion and its
independent diagonal circularization directly from the actual random-matrix model.  The
public theorems in this file therefore have no Gaussian sample space, realization, coupling,
Gaussian-law, or moment assumptions among their parameters.

The sole external mathematical conclusion below is the explicitly named instance of
Bandeira--Boedihardjo--van Handel, Theorem 2.8, applied to the canonical circularized matrix.
-/

namespace Arxiv2410V3

open MeasureTheory ProbabilityTheory

noncomputable section

/-! ## Fixed imaginary part: v3 formula (3.9) -/

/-- arXiv:2410.16457v3, Proposition 3.4, formula (3.9), at one fixed `eta`.

The good event, its probability, McDiarmid concentration, the BVH Remark 6.13 comparison,
the Gaussian companion, and diagonal circularization are all constructed internally.  The
only external premise is BBV Theorem 2.8 for `BVH.canonicalCircularizedMatrix model`. -/
theorem proposition34_formula39_complete_canonical
    {Omega OmegaXi : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {n : ℕ} (hn : 2 ≤ n)
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im)
    {B C cPrime : ℝ}
    (hbandwidth : IsBandwidth model.profile B)
    (hC : 8 ≤ C)
    (hCThird : BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant ≤ C)
    (hcPrime : 0 < cPrime)
    (hnLarge : proposition34CompleteAllEtaRateThreshold C cPrime ≤ n)
    (hscale : Real.rpow (n : ℝ) cPrime ≤ B * eta.im ^ 8)
    (bbv : External.BBVTheorem28GaussianFreeHypothesis
      (∫ omega, stieltjesTrace (BVH.canonicalCircularizedMatrix model omega) z eta
        ∂BVH.canonicalGaussianMeasure model)
      (freeDysonStieltjes z eta) B eta.im C) :
    Proposition34Formula39Conclusion mu
      (ComplexConcentrationGood
        (fun omega ↦ stieltjesTrace (model.matrix omega) z eta)
        (∫ omega, stieltjesTrace (model.matrix omega) z eta ∂mu)
        (32 * Real.sqrt (Real.log (n : ℝ)) /
          (Real.sqrt (n : ℝ) * eta.im)))
      (fun omega ↦ stieltjesTrace (model.matrix omega) z eta)
      (freeDysonStieltjes z eta) (n : ℝ) := by
  let _ : NeZero n := ⟨by omega⟩
  exact proposition34_formula39_complete_from_only_bbv
    hn model (BVH.canonicalGaussianCompanion model)
      (BVH.canonicalCircularizedMatrix model)
      (BVH.canonicalDiagonalDifference model) z heta
      hbandwidth hC hCThird hcPrime hnLarge hscale
      (BVH.canonicalCircularizedMatrix_entry_measurable model)
      (BVH.canonicalGaussianMatrix_sub_circularized model)
      (BVH.canonicalDiagonalDifference_re_hasGaussianLaw model)
      (BVH.canonicalDiagonalDifference_im_hasGaussianLaw model)
      (BVH.canonicalDiagonalDifference_re_mean_zero model)
      (BVH.canonicalDiagonalDifference_im_mean_zero model)
      (BVH.canonicalDiagonalDifference_re_variance_le_two_div_bandwidth
        model hbandwidth)
      (BVH.canonicalDiagonalDifference_im_variance_le_two_div_bandwidth
        model hbandwidth)
      bbv

/-! ## Uniform v3 Proposition 3.4 -/

/-- arXiv:2410.16457v3, Proposition 3.4, uniform formula (3.9) and bound (3.10).

All centers in the paper's finite `eta`-net use the same canonically constructed Gaussian
probability space and circularized matrix.  Thus the quantified `bbv` argument is precisely
the remaining centrewise BBV Theorem 2.8 input. -/
theorem proposition34_uniform_complete_canonical
    {Omega OmegaXi : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {n : ℕ} (hn : 2 ≤ n)
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (z : ℂ)
    {B C cPrime : ℝ}
    (hbandwidth : IsBandwidth model.profile B)
    (hC : 8 ≤ C)
    (hCThird : BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant ≤ C)
    (hcPrime : 0 < cPrime)
    (hnLarge : proposition34CompleteRateThreshold C cPrime ≤ n)
    (bbv : ∀ k : Proposition34EtaGridIndex n B cPrime,
      External.BBVTheorem28GaussianFreeHypothesis
        (∫ omega, stieltjesTrace (BVH.canonicalCircularizedMatrix model omega) z
          ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k)
          ∂BVH.canonicalGaussianMeasure model)
        (freeDysonStieltjes z
          ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k))
        B
        ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k).im C) :
    ProbabilityAtLeast mu
      (Proposition34UniformTraceGood
        (fun omega eta ↦ stieltjesTrace (model.matrix omega) z eta)
        n B cPrime (5 / 2))
      (1 - (n : ℝ) ^ (-10 : ℤ)) := by
  let _ : NeZero n := ⟨by omega⟩
  exact proposition34_uniform_complete_from_only_bbv
    hn model (BVH.canonicalGaussianCompanion model)
      (BVH.canonicalCircularizedMatrix model)
      (BVH.canonicalDiagonalDifference model) z
      hbandwidth hC hCThird hcPrime hnLarge
      (BVH.canonicalCircularizedMatrix_entry_measurable model)
      (BVH.canonicalGaussianMatrix_sub_circularized model)
      (BVH.canonicalDiagonalDifference_re_hasGaussianLaw model)
      (BVH.canonicalDiagonalDifference_im_hasGaussianLaw model)
      (BVH.canonicalDiagonalDifference_re_mean_zero model)
      (BVH.canonicalDiagonalDifference_im_mean_zero model)
      (BVH.canonicalDiagonalDifference_re_variance_le_two_div_bandwidth
        model hbandwidth)
      (BVH.canonicalDiagonalDifference_im_variance_le_two_div_bandwidth
        model hbandwidth)
      bbv

/-! ## v3 Corollary 3.5 -/

/-- arXiv:2410.16457v3, Corollary 3.5, including its constant `11`.

The Poisson-kernel/counting deduction and every probabilistic construction preceding BBV
Theorem 2.8 are verified internally.  The sole external premise is the displayed family of
BBV comparisons for the canonical circularized companion. -/
theorem corollary35_complete_canonical
    {Omega OmegaXi : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {n : ℕ} (hn : 2 ≤ n)
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (z : ℂ)
    {B C cPrime : ℝ}
    (hbandwidth : IsBandwidth model.profile B)
    (hC : 8 ≤ C)
    (hCThird : BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant ≤ C)
    (hcPrime : 0 < cPrime)
    (hnLarge : proposition34CompleteRateThreshold C cPrime ≤ n)
    (bbv : ∀ k : Proposition34EtaGridIndex n B cPrime,
      External.BBVTheorem28GaussianFreeHypothesis
        (∫ omega, stieltjesTrace (BVH.canonicalCircularizedMatrix model omega) z
          ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k)
          ∂BVH.canonicalGaussianMeasure model)
        (freeDysonStieltjes z
          ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k))
        B
        ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k).im C) :
    ProbabilityAtLeast mu
      (@Corollary35CountGood Omega n ⟨by omega⟩ model.matrix z
        (Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n cPrime) 11)
      (1 - (n : ℝ) ^ (-10 : ℤ)) := by
  let _ : NeZero n := ⟨by omega⟩
  exact corollary35_complete_from_only_bbv
    hn model (BVH.canonicalGaussianCompanion model)
      (BVH.canonicalCircularizedMatrix model)
      (BVH.canonicalDiagonalDifference model) z
      hbandwidth hC hCThird hcPrime hnLarge
      (BVH.canonicalCircularizedMatrix_entry_measurable model)
      (BVH.canonicalGaussianMatrix_sub_circularized model)
      (BVH.canonicalDiagonalDifference_re_hasGaussianLaw model)
      (BVH.canonicalDiagonalDifference_im_hasGaussianLaw model)
      (BVH.canonicalDiagonalDifference_re_mean_zero model)
      (BVH.canonicalDiagonalDifference_im_mean_zero model)
      (BVH.canonicalDiagonalDifference_re_variance_le_two_div_bandwidth
        model hbandwidth)
      (BVH.canonicalDiagonalDifference_im_variance_le_two_div_bandwidth
        model hbandwidth)
      bbv

end

end Arxiv2410V3

