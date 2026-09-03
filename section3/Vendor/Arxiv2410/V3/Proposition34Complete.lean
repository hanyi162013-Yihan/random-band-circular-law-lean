/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34Complete.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.Corollary35
import Vendor.Arxiv2410.V3.GaussianDiagonal
import Vendor.Arxiv2410.V3.ModelMcDiarmidBridge
import Vendor.Arxiv2410.V3.Proposition34Dyson
import Vendor.Arxiv2410.V3.Proposition34Uniform
import Vendor.Arxiv2410.V3.RateArithmetic

/-!
# Proposition 3.4 with only the two van Handel comparisons left external

This file composes the fixed-`eta` proof of arXiv:2410.16457v3, Proposition 3.4.
The Gaussian diagonal correction is reconstructed from concrete Gaussian coordinate laws by
`GaussianDiagonal.lean`, and the free transform is the internally constructed
`freeDysonStieltjes`.  Consequently the only cited mathematical results that occur as
hypotheses below are

* `External.BVHRemark613UnboundedExtensionHypothesis`, for v3 proof step (2); and
* `External.BBVTheorem28GaussianFreeHypothesis`, for v3 proof step (3).

Scalar concentration is stated as the pointwise inequality on its good event in this
fixed-parameter file.  It can be supplied by the proved McDiarmid development without adding
another external interface.  The finite-`n` rate is represented by the already checked
`PolynomialRateCertificate`; `RateArithmetic.lean` constructs this certificate from the scale
assumptions for every sufficiently large dimension.

No restriction on `z` is used: the free Dyson bound is uniform in every finite `z : ℂ`.
-/

namespace Arxiv2410V3

open MeasureTheory ProbabilityTheory

noncomputable section

/-- v3 Proposition 3.4, proof step (4), in the exact normalization needed by formula (3.11).

The direct theorem in `GaussianDiagonal.lean` gives the displayed estimate with constant `8`.
The paper uses a generic constant `C`, so `8 ≤ C` is the only bookkeeping needed here.
This is a proved inequality, not an input interface. -/
theorem gaussianDiagonal_formula311_term_le
    {OmegaG : Type*} [MeasurableSpace OmegaG]
    {muG : Measure OmegaG} [IsProbabilityMeasure muG]
    {n : ℕ}
    (XG XGo : OmegaG → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → OmegaG → ℂ) (z : ℂ) {eta : ℂ}
    (heta : 0 < eta.im) (hn : 2 ≤ n)
    {B C : ℝ} (hB : 0 < B) (hC : 8 ≤ C)
    (hXG : ∀ i j, Measurable (fun omega ↦ XG omega i j))
    (hXGo : ∀ i j, Measurable (fun omega ↦ XGo omega i j))
    (hdiag : ∀ omega,
      XG omega - XGo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) muG)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) muG)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂muG = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂muG = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; muG] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; muG] ≤ 2 / B) :
    ‖(∫ omega, stieltjesTrace (XG omega) z eta ∂muG) -
        ∫ omega, stieltjesTrace (XGo omega) z eta ∂muG‖ ≤
      C * Real.sqrt (Real.log (n : ℝ)) /
        (Real.sqrt B * eta.im ^ 2) := by
  have hEight := norm_expected_stieltjesTrace_sub_le_of_gaussianDiagonal_v3
    (mu := muG) XG XGo d z heta hn hB hXG hXGo hdiag
      hreG himG hreMean himMean hreVar himVar
  let q : ℝ := Real.sqrt (Real.log (n : ℝ)) /
    (Real.sqrt B * eta.im ^ 2)
  have hq : 0 ≤ q := by
    dsimp only [q]
    exact div_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
  calc
    ‖(∫ omega, stieltjesTrace (XG omega) z eta ∂muG) -
        ∫ omega, stieltjesTrace (XGo omega) z eta ∂muG‖ ≤
        8 * Real.sqrt (Real.log (n : ℝ)) /
          (Real.sqrt B * eta.im ^ 2) := hEight
    _ = 8 * q := by dsimp only [q]; ring
    _ ≤ C * q := mul_le_mul_of_nonneg_right hC hq
    _ = C * Real.sqrt (Real.log (n : ℝ)) /
          (Real.sqrt B * eta.im ^ 2) := by dsimp only [q]; ring

/-- v3 Proposition 3.4, formula (3.11), at a fixed `eta`.

The four terms are, in the paper's order: BVH universality, BBV Gaussian-to-free,
McDiarmid scalar concentration, and the now internally proved Gaussian diagonal correction.
The free trace is exactly `freeDysonStieltjes z eta`.  Thus the two displayed named external
hypotheses are the complete list of unformalized mathematical conclusions in this theorem. -/
theorem proposition34_formula311_fixedEta_from_two_vanHandel
    {OmegaG : Type*} [MeasurableSpace OmegaG]
    {muG : Measure OmegaG} [IsProbabilityMeasure muG]
    {n : ℕ}
    (XG XGo : OmegaG → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → OmegaG → ℂ) (z eta m expectedTrace : ℂ)
    (heta : 0 < eta.im) (hn : 2 ≤ n)
    {B C CD : ℝ} (hB : 0 < B) (hC : 8 ≤ C)
    (hXG : ∀ i j, Measurable (fun omega ↦ XG omega i j))
    (hXGo : ∀ i j, Measurable (fun omega ↦ XGo omega i j))
    (hdiag : ∀ omega,
      XG omega - XGo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) muG)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) muG)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂muG = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂muG = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; muG] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; muG] ≤ 2 / B)
    (hconcentration :
      ‖m - expectedTrace‖ ≤
        CD * Real.sqrt (Real.log (n : ℝ)) /
          (Real.sqrt (n : ℝ) * eta.im))
    (bvh : External.BVHRemark613UnboundedExtensionHypothesis
      expectedTrace
      (∫ omega, stieltjesTrace (XG omega) z eta ∂muG)
      eta.im (1 / Real.sqrt B) C)
    (bbv : External.BBVTheorem28GaussianFreeHypothesis
      (∫ omega, stieltjesTrace (XGo omega) z eta ∂muG)
      (freeDysonStieltjes z eta) B eta.im C) :
    ‖m - freeDysonStieltjes z eta‖ ≤
      formula311Error (n : ℝ) B eta.im C CD := by
  have hUniversality :
      ‖expectedTrace -
          ∫ omega, stieltjesTrace (XG omega) z eta ∂muG‖ ≤
        C / (Real.sqrt B * eta.im ^ 4) := by
    have h := bvh.estimate
    simpa only [div_eq_mul_inv, one_mul, mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  have hDiagonal := gaussianDiagonal_formula311_term_le
    (muG := muG) XG XGo d z heta hn hB hC hXG hXGo hdiag
      hreG himG hreMean himMean hreVar himVar
  exact formula311_of_four_inputs m expectedTrace
    (∫ omega, stieltjesTrace (XG omega) z eta ∂muG)
    (∫ omega, stieltjesTrace (XGo omega) z eta ∂muG)
    (freeDysonStieltjes z eta)
    hconcentration hUniversality hDiagonal bbv.estimate

/-- v3 Proposition 3.4, `(3.11) ⇒ (3.9)`, at fixed `eta`, with only the two
van Handel comparison conclusions external.

The scalar concentration premise is an ordinary pointwise inequality on the stated good event;
it is not a result interface.  The probability premise records the same event.  The conclusion
uses the explicit rate exponent stored in a certificate built by `RateArithmetic.lean`. -/
theorem proposition34_formula39_fixedEta_from_two_vanHandel
    {Omega OmegaG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaG]
    {mu : Measure Omega} {muG : Measure OmegaG} [IsProbabilityMeasure muG]
    {n : ℕ}
    (trace : Omega → ℂ)
    (XG XGo : OmegaG → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → OmegaG → ℂ) (z eta : ℂ)
    (heta : 0 < eta.im) (hn : 2 ≤ n)
    {B C CD : ℝ} (hB : 0 < B) (hC : 8 ≤ C)
    {good : Set Omega}
    (hprob : ProbabilityAtLeast mu good (1 - (n : ℝ) ^ (-10 : ℤ)))
    (hconcentration : ∀ omega ∈ good,
      ‖trace omega - ∫ omega, trace omega ∂mu‖ ≤
        CD * Real.sqrt (Real.log (n : ℝ)) /
          (Real.sqrt (n : ℝ) * eta.im))
    (hXG : ∀ i j, Measurable (fun omega ↦ XG omega i j))
    (hXGo : ∀ i j, Measurable (fun omega ↦ XGo omega i j))
    (hdiag : ∀ omega,
      XG omega - XGo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) muG)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) muG)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂muG = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂muG = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; muG] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; muG] ≤ 2 / B)
    (bvh : External.BVHRemark613UnboundedExtensionHypothesis
      (∫ omega, trace omega ∂mu)
      (∫ omega, stieltjesTrace (XG omega) z eta ∂muG)
      eta.im (1 / Real.sqrt B) C)
    (bbv : External.BBVTheorem28GaussianFreeHypothesis
      (∫ omega, stieltjesTrace (XGo omega) z eta ∂muG)
      (freeDysonStieltjes z eta) B eta.im C)
    (rate : PolynomialRateCertificate (n : ℝ)
      (formula311Error (n : ℝ) B eta.im C CD)) :
    Proposition34Formula39Conclusion mu good trace
      (freeDysonStieltjes z eta) (n : ℝ) := by
  refine ⟨rate.exponent, rate.exponent_pos, hprob, ?_⟩
  intro omega homega
  exact (proposition34_formula311_fixedEta_from_two_vanHandel
    (muG := muG) XG XGo d z eta (trace omega) (∫ omega, trace omega ∂mu)
    heta hn hB hC hXG hXGo hdiag hreG himG hreMean himMean hreVar himVar
    (hconcentration omega homega) bvh bbv).trans rate.error_le

/-- v3 Proposition 3.4, formula (3.10), at fixed `eta`.

This closes the deterministic final step with the internally proved estimate
`|freeDysonStieltjes z eta| < 1`.  Hence the explicit bound is `2`, uniformly in `z`.
All comparison assumptions are exactly those of the preceding fixed-`eta` formula (3.11). -/
theorem proposition34_formula310_fixedEta_from_two_vanHandel
    {Omega OmegaG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaG]
    {mu : Measure Omega} {muG : Measure OmegaG} [IsProbabilityMeasure muG]
    {n : ℕ}
    (trace : Omega → ℂ)
    (XG XGo : OmegaG → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → OmegaG → ℂ) (z eta : ℂ)
    (heta : 0 < eta.im) (hn : 2 ≤ n)
    {B C CD : ℝ} (hB : 0 < B) (hC : 8 ≤ C)
    {good : Set Omega}
    (hconcentration : ∀ omega ∈ good,
      ‖trace omega - ∫ omega, trace omega ∂mu‖ ≤
        CD * Real.sqrt (Real.log (n : ℝ)) /
          (Real.sqrt (n : ℝ) * eta.im))
    (hXG : ∀ i j, Measurable (fun omega ↦ XG omega i j))
    (hXGo : ∀ i j, Measurable (fun omega ↦ XGo omega i j))
    (hdiag : ∀ omega,
      XG omega - XGo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) muG)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) muG)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂muG = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂muG = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; muG] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; muG] ≤ 2 / B)
    (bvh : External.BVHRemark613UnboundedExtensionHypothesis
      (∫ omega, trace omega ∂mu)
      (∫ omega, stieltjesTrace (XG omega) z eta ∂muG)
      eta.im (1 / Real.sqrt B) C)
    (bbv : External.BBVTheorem28GaussianFreeHypothesis
      (∫ omega, stieltjesTrace (XGo omega) z eta ∂muG)
      (freeDysonStieltjes z eta) B eta.im C)
    (rate : PolynomialRateCertificate (n : ℝ)
      (formula311Error (n : ℝ) B eta.im C CD))
    {omega : Omega} (homega : omega ∈ good) :
    ‖trace omega‖ ≤ 2 := by
  have hcomparison :
      ‖trace omega - freeDysonStieltjes z eta‖ ≤
        Real.rpow (n : ℝ) (-rate.exponent) :=
    (proposition34_formula311_fixedEta_from_two_vanHandel
      (muG := muG) XG XGo d z eta (trace omega) (∫ omega, trace omega ∂mu)
      heta hn hB hC hXG hXGo hdiag hreG himG hreMean himMean hreVar himVar
      (hconcentration omega homega) bvh bbv).trans rate.error_le
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hrateOne : Real.rpow (n : ℝ) (-rate.exponent) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnOne (neg_nonpos.mpr rate.exponent_pos.le)
  exact proposition34_formula310_at_point_freeDyson heta
    (good := good) (trace := trace) (n := (n : ℝ))
    (exponent := rate.exponent)
    (fun omega homega ↦
      (proposition34_formula311_fixedEta_from_two_vanHandel
        (muG := muG) XG XGo d z eta (trace omega) (∫ omega, trace omega ∂mu)
        heta hn hB hC hXG hXGo hdiag hreG himG hreMean himMean hreVar himVar
        (hconcentration omega homega) bvh bbv).trans rate.error_le)
    hrateOne homega

/-- An internal sufficiently-large-dimension threshold for the v3 rate ledger with the
direct-product McDiarmid constant `C_D = 32`.

This is a definition by choice from the proved threshold theorem in `RateArithmetic.lean`;
it is not a hypothesis or an external certificate. -/
noncomputable def proposition34CompleteRateThreshold (C c : ℝ) : ℕ :=
  if h : 0 ≤ C ∧ 0 < c then
    Classical.choose
      (exists_threshold_formula311_polynomialRateCertificate_nat
        (C := C) (CD := 32) (c := c) h.1 (by norm_num) h.2)
  else 0

/-- The defining threshold supplies a checked rate certificate for every admissible `B,v`.
This is the finite-`n` rate step from v3 formula (3.11) to formula (3.9), with no certificate
left for the caller to construct. -/
theorem proposition34CompleteRateThreshold_spec
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {n : ℕ} (hnLarge : proposition34CompleteRateThreshold C c ≤ n)
    {B v : ℝ} (hv : 0 < v) (hv5 : v ≤ 5) (hBn : B ≤ (n : ℝ))
    (hscale : Real.rpow (n : ℝ) c ≤ B * v ^ 8) :
    Nonempty (PolynomialRateCertificate (n : ℝ)
      (formula311Error (n : ℝ) B v C 32)) := by
  rw [proposition34CompleteRateThreshold, dif_pos ⟨hC, hc⟩] at hnLarge
  exact (Classical.choose_spec
    (exists_threshold_formula311_polynomialRateCertificate_nat
      (C := C) (CD := 32) (c := c) hC (by norm_num) hc))
    n hnLarge B v hv hv5 hBn hscale

/-- The v3 uniform-domain cutoff implies the scale inequality used by the rate ledger:

`B⁻¹/⁸ nᶜ ≤ v  ⟹  nᶜ ≤ B v⁸`.

In fact the eighth power of the left side gives `n^(8c)`; the weaker exponent `c` is enough
for Proposition 3.4.  This calculation is entirely uniform in `z`. -/
theorem proposition34EtaScale_implies_rate_scale
    {n : ℕ} (hn : 1 ≤ n) {B c v : ℝ}
    (hB : 0 < B) (hc : 0 ≤ c)
    (hcutoff : proposition34EtaScale n B c ≤ v) :
    Real.rpow (n : ℝ) c ≤ B * v ^ 8 := by
  have hnR : (0 : ℝ) < n := by positivity
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hv0 : 0 < proposition34EtaScale n B c := by
    exact corollary35_scale_pos hB hnR
  have hv : 0 < v := hv0.trans_le hcutoff
  have hpow : (proposition34EtaScale n B c) ^ 8 ≤ v ^ 8 :=
    pow_le_pow_left₀ hv0.le hcutoff 8
  have hBpow : (Real.rpow B (-(1 / 8 : ℝ))) ^ 8 = B⁻¹ := by
    calc
      (Real.rpow B (-(1 / 8 : ℝ))) ^ 8 =
          Real.rpow B ((-(1 / 8 : ℝ)) * (8 : ℕ)) :=
        (Real.rpow_mul_natCast hB.le (-(1 / 8 : ℝ)) 8).symm
      _ = Real.rpow B (-1 : ℝ) := by norm_num
      _ = B⁻¹ := Real.rpow_neg_one B
  have hnpow : (Real.rpow (n : ℝ) c) ^ 8 =
      Real.rpow (n : ℝ) (c * (8 : ℝ)) := by
    simpa using (Real.rpow_mul_natCast hnR.le c 8).symm
  have hscaleEq : B * (proposition34EtaScale n B c) ^ 8 =
      Real.rpow (n : ℝ) (c * 8) := by
    rw [proposition34EtaScale, mul_pow, hBpow, hnpow]
    field_simp [hB.ne']
  calc
    Real.rpow (n : ℝ) c ≤ Real.rpow (n : ℝ) (c * 8) :=
      Real.rpow_le_rpow_of_exponent_le hnOne (by nlinarith)
    _ = B * (proposition34EtaScale n B c) ^ 8 := hscaleEq.symm
    _ ≤ B * v ^ 8 := mul_le_mul_of_nonneg_left hpow hB.le

/-- End-to-end uniform form of arXiv:2410.16457v3, Proposition 3.4, leaving exactly the
two cited van Handel comparison conclusions external.

Everything else is connected here:

* actual-model scalar concentration comes from the proved direct finite-product McDiarmid
  theorem, with unrelaxed centre failure `4 n⁻³²`;
* the diagonal Gaussian term comes from concrete centered Gaussian coordinate laws;
* the finite-`n` rate certificate is selected internally above once `n` exceeds the proved
  threshold;
* every centre has trace norm at most `2`, using the internally constructed
  `freeDysonStieltjes`; and
* the explicit two-dimensional net and resolvent Lipschitz estimate add only `1/2`.

The resulting common event has probability at least `1-n⁻¹⁰` and uniform trace bound `5/2`.
There is no restriction on the fixed finite parameter `z`. -/
theorem proposition34_uniform_complete_from_two_vanHandel
    {Omega OmegaXi OmegaG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi] [MeasurableSpace OmegaG]
    {mu : Measure Omega} {nu : Measure OmegaXi} {muG : Measure OmegaG}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure muG]
    {n : ℕ} (hn : 2 ≤ n)
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (XG XGo : OmegaG → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → OmegaG → ℂ) (z : ℂ)
    {B C cPrime : ℝ}
    (hbandwidth : IsBandwidth model.profile B)
    (hC : 8 ≤ C) (hcPrime : 0 < cPrime)
    (hnLarge : proposition34CompleteRateThreshold C cPrime ≤ n)
    (hXG : ∀ i j, Measurable (fun omega ↦ XG omega i j))
    (hXGo : ∀ i j, Measurable (fun omega ↦ XGo omega i j))
    (hdiag : ∀ omega,
      XG omega - XGo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) muG)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) muG)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂muG = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂muG = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; muG] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; muG] ≤ 2 / B)
    (bvh : ∀ k : Proposition34EtaGridIndex n B cPrime,
      External.BVHRemark613UnboundedExtensionHypothesis
        (∫ omega, stieltjesTrace (model.matrix omega) z
          ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k) ∂mu)
        (∫ omega, stieltjesTrace (XG omega) z
          ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k) ∂muG)
        ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k).im
        (1 / Real.sqrt B) C)
    (bbv : ∀ k : Proposition34EtaGridIndex n B cPrime,
      External.BBVTheorem28GaussianFreeHypothesis
        (∫ omega, stieltjesTrace (XGo omega) z
          ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k) ∂muG)
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
  let net := proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)
  let trace : Omega → ℂ → ℂ :=
    fun omega eta ↦ stieltjesTrace (model.matrix omega) z eta
  let good : Proposition34EtaGridIndex n B cPrime → Set Omega := fun k ↦
    ComplexConcentrationGood (fun omega ↦ trace omega (net.center k))
      (∫ omega, trace omega (net.center k) ∂mu)
      (32 * Real.sqrt (Real.log (n : ℝ)) /
        (Real.sqrt (n : ℝ) * (net.center k).im))
  have hBn : B ≤ (n : ℝ) := by
    simpa using bandwidth_le_card model.profile hbandwidth
  have hmeas : ∀ k, MeasurableSet (good k) := by
    intro k
    apply measurableSet_complexConcentrationGood
    exact model.stieltjesTrace_measurable z (net.center k)
  have hq0 : 0 ≤ 4 * (n : ℝ) ^ (-32 : ℤ) := by positivity
  have hq10 : 4 * (n : ℝ) ^ (-32 : ℤ) ≤ (n : ℝ) ^ (-10 : ℤ) := by
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have h := card_mul_four_zpow_neg32_le_zpow_neg10 hn (K := 1)
      (by simpa using (one_le_pow₀ hnOne : (1 : ℝ) ≤ (n : ℝ) ^ 18))
    simpa using h
  have hq1 : 4 * (n : ℝ) ^ (-32 : ℤ) ≤ 1 := by
    have hnR : (0 : ℝ) < n := by positivity
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hzpow : (n : ℝ) ^ (-10 : ℤ) ≤ 1 := by
      rw [show (-10 : ℤ) = -(10 : ℤ) by norm_num, zpow_neg]
      exact (inv_le_one₀ (pow_pos hnR 10)).2 (one_le_pow₀ hnOne)
    exact hq10.trans hzpow
  have hpoint : ∀ k,
      mu (good k)ᶜ ≤ ENNReal.ofReal (4 * (n : ℝ) ^ (-32 : ℤ)) := by
    intro k
    have hprob :=
      probabilityAtLeast_stieltjesTrace_complexConcentrationGood_v3_thirtytwo_n32
        model z (net.center_mem k).1 hn
    apply measure_compl_le_of_probabilityAtLeast_one_sub (hmeas k) hq0 hq1
    simpa only [good, trace, net] using hprob
  have hcenter : ∀ k omega, omega ∈ good k →
      ‖trace omega (net.center k)‖ ≤ 2 := by
    intro k omega homega
    have heta := net.center_mem k
    have hetaPos : 0 < (net.center k).im := heta.1
    have heta5 : (net.center k).im ≤ 5 :=
      (Complex.im_le_norm (net.center k)).trans heta.2.1
    have hscale : Real.rpow (n : ℝ) cPrime ≤ B * (net.center k).im ^ 8 :=
      proposition34EtaScale_implies_rate_scale (show 1 ≤ n by omega)
        hbandwidth.pos hcPrime.le heta.2.2
    obtain ⟨rate⟩ := proposition34CompleteRateThreshold_spec
      (show 0 ≤ C by linarith) hcPrime hnLarge hetaPos heta5 hBn hscale
    exact proposition34_formula310_fixedEta_from_two_vanHandel
      (muG := muG) (mu := mu)
      (trace := fun omega ↦ trace omega (net.center k))
      XG XGo d z (net.center k) hetaPos hn hbandwidth.pos hC
      (good := good k)
      (hconcentration := by
        intro omega homega
        exact homega)
      (hXG := hXG) (hXGo := hXGo) (hdiag := hdiag)
      (hreG := hreG) (himG := himG)
      (hreMean := hreMean) (himMean := himMean)
      (hreVar := hreVar) (himVar := himVar)
      (bvh := by simpa only [net, trace] using bvh k)
      (bbv := by simpa only [net] using bbv k)
      (rate := rate) homega
  have huniform := proposition34_uniformTrace_probability_from_center_failures
    mu hn hbandwidth.pos hBn hcPrime.le model.matrix z good hmeas hpoint
    (by
      intro k omega homega
      simpa only [trace, net] using hcenter k omega homega)
  convert huniform using 1
  all_goals norm_num

/-- End-to-end arXiv:2410.16457v3, Corollary 3.5, for an arbitrary fixed finite `z`.

This theorem does not accept a uniform trace event, its probability, or a counting estimate.
It first invokes `proposition34_uniform_complete_from_two_vanHandel` on the actual random-matrix
model and then applies the fully formalized Poisson-kernel argument.  Since Proposition 3.4 now
has trace constant `5/2`, the explicit counting constant is `4 * (5/2) + 1 = 11`.
The only external mathematical conclusions are again the two displayed centrewise BVH and BBV
hypotheses. -/
theorem corollary35_complete_from_two_vanHandel
    {Omega OmegaXi OmegaG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi] [MeasurableSpace OmegaG]
    {mu : Measure Omega} {nu : Measure OmegaXi} {muG : Measure OmegaG}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure muG]
    {n : ℕ} (hn : 2 ≤ n)
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (XG XGo : OmegaG → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → OmegaG → ℂ) (z : ℂ)
    {B C cPrime : ℝ}
    (hbandwidth : IsBandwidth model.profile B)
    (hC : 8 ≤ C) (hcPrime : 0 < cPrime)
    (hnLarge : proposition34CompleteRateThreshold C cPrime ≤ n)
    (hXG : ∀ i j, Measurable (fun omega ↦ XG omega i j))
    (hXGo : ∀ i j, Measurable (fun omega ↦ XGo omega i j))
    (hdiag : ∀ omega,
      XG omega - XGo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) muG)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) muG)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂muG = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂muG = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; muG] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; muG] ≤ 2 / B)
    (bvh : ∀ k : Proposition34EtaGridIndex n B cPrime,
      External.BVHRemark613UnboundedExtensionHypothesis
        (∫ omega, stieltjesTrace (model.matrix omega) z
          ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k) ∂mu)
        (∫ omega, stieltjesTrace (XG omega) z
          ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k) ∂muG)
        ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k).im
        (1 / Real.sqrt B) C)
    (bbv : ∀ k : Proposition34EtaGridIndex n B cPrime,
      External.BBVTheorem28GaussianFreeHypothesis
        (∫ omega, stieltjesTrace (XGo omega) z
          ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k) ∂muG)
        (freeDysonStieltjes z
          ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k))
        B
        ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center k).im C) :
    ProbabilityAtLeast mu
      (@Corollary35CountGood Omega n ⟨by omega⟩ model.matrix z
        (Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n cPrime) 11)
      (1 - (n : ℝ) ^ (-10 : ℤ)) := by
  let _ : NeZero n := ⟨by omega⟩
  let good : Set Omega :=
    Proposition34UniformTraceGood
      (fun omega eta ↦ stieltjesTrace (model.matrix omega) z eta)
      n B cPrime (5 / 2)
  have hprob : ProbabilityAtLeast mu good (1 - (n : ℝ) ^ (-10 : ℤ)) := by
    exact proposition34_uniform_complete_from_two_vanHandel
      hn model XG XGo d z hbandwidth hC hcPrime hnLarge
      hXG hXGo hdiag hreG himG hreMean himMean hreVar himVar bvh bbv
  have htrace : ∀ omega ∈ good, ∀ eta,
      InUpperHalfPlane eta → ‖eta‖ ≤ 5 →
        Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n cPrime ≤ eta.im →
          ‖stieltjesTrace (model.matrix omega) z eta‖ ≤ (5 / 2 : ℝ) := by
    intro omega homega eta heta hnorm hcutoff
    exact homega eta ⟨heta, hnorm, hcutoff⟩
  have hcount := corollary35_probability_v3_scale
    mu model.matrix z hbandwidth.pos hcPrime (by norm_num : (0 : ℝ) ≤ 5 / 2)
    good hprob htrace
  simpa only [show (4 : ℝ) * (5 / 2) + 1 = 11 by norm_num] using hcount

end

end Arxiv2410V3

