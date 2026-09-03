import Vendor.Arxiv2410.V3.BVH.GaussianConstruction
import Vendor.Arxiv2410.V3.Proposition34OnlyBBV
import ShortRingAnchor.ExplicitStieltjesRate

/-!
# Lemma 3.5: actual v3 pointwise probability estimates, with one explicit rate

The canonical Gaussian companion, BVH comparison, diagonal correction,
and McDiarmid probability are proved in the vendored v3 development.
Only the explicitly named BBV Theorem 2.8 comparison is external.
Unlike the existential fixed-eta endpoint, this module keeps the error
in formula (3.11) visible so that one rate works on a growing grid.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace ShortRingAnchor
open Arxiv2410V3

variable {Omega OmegaXi : Type*}
  [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
  {mu : Measure Omega} {nu : Measure OmegaXi}
  [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]

/-- v3 proof step (3): the actual row-McDiarmid concentration event. -/
def v3TraceConcentrationGood {n : ℕ}
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (z eta : ℂ) : Set Omega :=
  ComplexConcentrationGood
    (fun sample => stieltjesTrace (model.matrix sample) z eta)
    (∫ sample, stieltjesTrace (model.matrix sample) z eta ∂mu)
    (32 * Real.sqrt (Real.log (n : ℝ)) / (Real.sqrt (n : ℝ) * eta.im))

/-- A transparent specialization of the centralized external BBV interface.
This is a hypothesis type, not an asserted theorem or a new comparison input. -/
abbrev CanonicalBBVAt {n : ℕ}
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (z eta : ℂ) (B C : ℝ) : Prop :=
  External.BBVTheorem28GaussianFreeHypothesis
    (∫ sample, stieltjesTrace (BVH.canonicalCircularizedMatrix model sample) z eta
      ∂BVH.canonicalGaussianMeasure model)
    (freeDysonStieltjes z eta) B eta.im C

/-- v3 (3.11), with every construction except BBV supplied by checked code.
There is no restriction on `Re eta` or on the fixed shift `z`. -/
theorem v3_formula311_canonical_on_good {n : ℕ} (hn : 2 ≤ n)
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) {B C : ℝ}
    (hB : IsBandwidth model.profile B) (hC : 8 ≤ C)
    (hthird : BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant ≤ C)
    (bbv : CanonicalBBVAt model z eta B C)
    {sample : Omega} (hgood : sample ∈ v3TraceConcentrationGood model z eta) :
    ‖stieltjesTrace (model.matrix sample) z eta - freeDysonStieltjes z eta‖ ≤
      formula311Error (n : ℝ) B eta.im C 32 := by
  let _ : NeZero n := ⟨by omega⟩
  exact proposition34_formula311_fixedEta_from_only_bbv
    model (BVH.canonicalGaussianCompanion model)
    (BVH.canonicalCircularizedMatrix model) (BVH.canonicalDiagonalDifference model)
    z eta (stieltjesTrace (model.matrix sample) z eta) heta hn hB hC hthird
    (BVH.canonicalCircularizedMatrix_entry_measurable model)
    (BVH.canonicalGaussianMatrix_sub_circularized model)
    (BVH.canonicalDiagonalDifference_re_hasGaussianLaw model)
    (BVH.canonicalDiagonalDifference_im_hasGaussianLaw model)
    (BVH.canonicalDiagonalDifference_re_mean_zero model)
    (BVH.canonicalDiagonalDifference_im_mean_zero model)
    (BVH.canonicalDiagonalDifference_re_variance_le_two_div_bandwidth model hB)
    (BVH.canonicalDiagonalDifference_im_variance_le_two_div_bandwidth model hB)
    hgood bbv

/-- v3 proof step (3): the actual concentration event has failure at most
`n^(-10)`, with its measurability derived from the matrix entries. -/
theorem v3_concentration_bad_le {n : ℕ} (hn : 2 ≤ n)
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) :
    mu (v3TraceConcentrationGood model z eta)ᶜ ≤
      ENNReal.ofReal ((n : ℝ) ^ (-(10 : ℝ))) := by
  let _ : NeZero n := ⟨by omega⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hq : (n : ℝ) ^ (-10 : ℤ) = (n : ℝ) ^ (-(10 : ℝ)) := by
    norm_cast
  have hq1 : (n : ℝ) ^ (-10 : ℤ) ≤ 1 := by
    rw [hq]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have h := measure_compl_le_of_probabilityAtLeast_one_sub
    (measurableSet_complexConcentrationGood
      (measurable_stieltjesTrace model.entry_measurable z eta) _ _)
    (show 0 ≤ (n : ℝ) ^ (-10 : ℤ) by positivity) hq1
    (probabilityAtLeast_stieltjesTrace_complexConcentrationGood_v3_thirtytwo
      model z heta hn)
  simpa only [v3TraceConcentrationGood, hq] using h

/-- v3 (3.11) with the genuine pointwise probability bound. The error
majorant is deterministic and can be supplied by the common-rate lemma. -/
theorem v3_pointwise_comparison_bad_le {n : ℕ} (hn : 2 ≤ n)
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) {B C E : ℝ}
    (hB : IsBandwidth model.profile B) (hC : 8 ≤ C)
    (hthird : BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant ≤ C)
    (bbv : CanonicalBBVAt model z eta B C)
    (herror : formula311Error (n : ℝ) B eta.im C 32 ≤ E) :
    mu {sample | E < ‖stieltjesTrace (model.matrix sample) z eta -
      freeDysonStieltjes z eta‖} ≤ ENNReal.ofReal ((n : ℝ) ^ (-(10 : ℝ))) := by
  apply (measure_mono ?_).trans (v3_concentration_bad_le hn model z heta)
  intro sample hsample hgood
  exact not_lt_of_ge ((v3_formula311_canonical_on_good hn model z heta hB hC hthird
    bbv hgood).trans herror) hsample

end ShortRingAnchor
