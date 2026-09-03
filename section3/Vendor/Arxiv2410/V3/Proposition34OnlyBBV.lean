/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34OnlyBBV.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.BVH.Remark613
import Vendor.Arxiv2410.V3.Proposition34Complete
import Vendor.Arxiv2410.V3.RateArithmeticAllEta

/-!
# Proposition 3.4 and Corollary 3.5 with only BBV Theorem 2.8 external

The specialized finite-third-moment content of BVH Remark 6.13 is now proved in
`BVH/Remark613.lean`.  This file plugs that theorem into the earlier compatibility wrapper.
Consequently the public end-to-end theorems below expose only the Gaussian-to-free comparison
from Bandeira--Boedihardjo--van Handel, Theorem 2.8.
-/

namespace Arxiv2410V3

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The internally proved specialized BVH theorem inhabits the old explicit compatibility
interface.  This theorem is a discharge lemma, not an additional assumption. -/
theorem bvhRemark613Hypothesis_of_gaussianCompanion
    {Omega OmegaXi OmegaG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi] [MeasurableSpace OmegaG]
    {mu : Measure Omega} {nu : Measure OmegaXi} {muG : Measure OmegaG}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure muG]
    {n : ℕ} [NeZero n]
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (gaussian : BVH.GaussianCompanionModelV3
      n Omega OmegaXi OmegaG mu nu muG model)
    {B C : ℝ} (hB : IsBandwidth model.profile B)
    (hC : BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant ≤ C)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) :
    External.BVHRemark613UnboundedExtensionHypothesis
      (∫ omega, stieltjesTrace (model.matrix omega) z eta ∂mu)
      (∫ omega, stieltjesTrace (gaussian.matrix omega) z eta ∂muG)
      eta.im (1 / Real.sqrt B) C := by
  refine ⟨?_⟩
  have hint := BVH.bvh_remark613_specialized_v3 model gaussian hB z heta
  calc
    ‖(∫ omega, stieltjesTrace (model.matrix omega) z eta ∂mu) -
        ∫ omega, stieltjesTrace (gaussian.matrix omega) z eta ∂muG‖ ≤
        (BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant) /
          (Real.sqrt B * eta.im ^ 4) := hint
    _ ≤ C / (Real.sqrt B * eta.im ^ 4) := by
      exact div_le_div_of_nonneg_right hC
        (mul_nonneg (Real.sqrt_nonneg B) (pow_nonneg (le_of_lt heta) 4))
    _ = C / eta.im ^ 4 * (1 / Real.sqrt B) := by ring

/-- A sufficiently-large-dimension threshold for formula (3.9), valid for every positive
imaginary part.  The McDiarmid constant is fixed to `32`, exactly as in the complete v3 route.
This definition merely chooses the threshold supplied by the proved all-`eta` rate theorem. -/
noncomputable def proposition34CompleteAllEtaRateThreshold (C c : ℝ) : ℕ :=
  if h : 0 ≤ C ∧ 0 < c then
    Classical.choose
      (exists_threshold_formula311_polynomialRateCertificate_nat_allEta
        (C := C) (CD := 32) (c := c) h.1 (by norm_num) h.2)
  else 0

/-- The chosen all-`eta` threshold supplies the polynomial rate certificate without an upper
bound on `v = Im eta`. -/
theorem proposition34CompleteAllEtaRateThreshold_spec
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {n : ℕ} (hnLarge : proposition34CompleteAllEtaRateThreshold C c ≤ n)
    {B v : ℝ} (hB : 1 ≤ B) (hBn : B ≤ (n : ℝ)) (hv : 0 < v)
    (hscale : Real.rpow (n : ℝ) c ≤ B * v ^ 8) :
    Nonempty (PolynomialRateCertificate (n : ℝ)
      (formula311Error (n : ℝ) B v C 32)) := by
  rw [proposition34CompleteAllEtaRateThreshold, dif_pos ⟨hC, hc⟩] at hnLarge
  exact (Classical.choose_spec
    (exists_threshold_formula311_polynomialRateCertificate_nat_allEta
      (C := C) (CD := 32) (c := c) hC (by norm_num) hc))
    n hnLarge B v hB hBn hv hscale

/-! ## Fixed-`eta` chain with the BVH premise discharged internally -/

/-- v3 Proposition 3.4, formula (3.11), at fixed `eta`, after discharging the
BVH Remark 6.13 comparison by the specialized theorem proved in `BVH/Remark613.lean`.

The Gaussian companion and diagonal-correction data remain explicit mathematical inputs.
The only remaining *external comparison conclusion* is BBV Theorem 2.8. -/
theorem proposition34_formula311_fixedEta_from_only_bbv
    {Omega OmegaXi OmegaG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi] [MeasurableSpace OmegaG]
    {mu : Measure Omega} {nu : Measure OmegaXi} {muG : Measure OmegaG}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure muG]
    {n : ℕ}
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (gaussian : BVH.GaussianCompanionModelV3
      n Omega OmegaXi OmegaG mu nu muG model)
    (XGo : OmegaG → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → OmegaG → ℂ) (z eta m : ℂ)
    (heta : 0 < eta.im) (hn : 2 ≤ n)
    {B C CD : ℝ} (hbandwidth : IsBandwidth model.profile B)
    (hC : 8 ≤ C)
    (hCThird : BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant ≤ C)
    (hXGo : ∀ i j, Measurable (fun omega ↦ XGo omega i j))
    (hdiag : ∀ omega,
      gaussian.matrix omega - XGo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) muG)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) muG)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂muG = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂muG = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; muG] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; muG] ≤ 2 / B)
    (hconcentration :
      ‖m - ∫ omega, stieltjesTrace (model.matrix omega) z eta ∂mu‖ ≤
        CD * Real.sqrt (Real.log (n : ℝ)) /
          (Real.sqrt (n : ℝ) * eta.im))
    (bbv : External.BBVTheorem28GaussianFreeHypothesis
      (∫ omega, stieltjesTrace (XGo omega) z eta ∂muG)
      (freeDysonStieltjes z eta) B eta.im C) :
    ‖m - freeDysonStieltjes z eta‖ ≤
      formula311Error (n : ℝ) B eta.im C CD := by
  let _ : NeZero n := ⟨by omega⟩
  apply proposition34_formula311_fixedEta_from_two_vanHandel
    (muG := muG) gaussian.matrix XGo d z eta m
      (∫ omega, stieltjesTrace (model.matrix omega) z eta ∂mu)
      heta hn hbandwidth.pos hC gaussian.entry_measurable hXGo hdiag
      hreG himG hreMean himMean hreVar himVar hconcentration
  · exact bvhRemark613Hypothesis_of_gaussianCompanion
      model gaussian hbandwidth hCThird z heta
  · exact bbv

/-- v3 Proposition 3.4, `(3.11) ⇒ (3.9)`, at fixed `eta`, with the specialized
BVH comparison discharged internally.  Besides realization, moment, concentration, and rate
data, the only remaining external comparison conclusion is BBV Theorem 2.8. -/
theorem proposition34_formula39_fixedEta_from_only_bbv
    {Omega OmegaXi OmegaG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi] [MeasurableSpace OmegaG]
    {mu : Measure Omega} {nu : Measure OmegaXi} {muG : Measure OmegaG}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure muG]
    {n : ℕ}
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (gaussian : BVH.GaussianCompanionModelV3
      n Omega OmegaXi OmegaG mu nu muG model)
    (XGo : OmegaG → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → OmegaG → ℂ) (z eta : ℂ)
    (heta : 0 < eta.im) (hn : 2 ≤ n)
    {B C CD : ℝ} (hbandwidth : IsBandwidth model.profile B)
    (hC : 8 ≤ C)
    (hCThird : BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant ≤ C)
    {good : Set Omega}
    (hprob : ProbabilityAtLeast mu good (1 - (n : ℝ) ^ (-10 : ℤ)))
    (hconcentration : ∀ omega ∈ good,
      ‖stieltjesTrace (model.matrix omega) z eta -
          ∫ omega', stieltjesTrace (model.matrix omega') z eta ∂mu‖ ≤
        CD * Real.sqrt (Real.log (n : ℝ)) /
          (Real.sqrt (n : ℝ) * eta.im))
    (hXGo : ∀ i j, Measurable (fun omega ↦ XGo omega i j))
    (hdiag : ∀ omega,
      gaussian.matrix omega - XGo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) muG)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) muG)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂muG = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂muG = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; muG] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; muG] ≤ 2 / B)
    (bbv : External.BBVTheorem28GaussianFreeHypothesis
      (∫ omega, stieltjesTrace (XGo omega) z eta ∂muG)
      (freeDysonStieltjes z eta) B eta.im C)
    (rate : PolynomialRateCertificate (n : ℝ)
      (formula311Error (n : ℝ) B eta.im C CD)) :
    Proposition34Formula39Conclusion mu good
      (fun omega ↦ stieltjesTrace (model.matrix omega) z eta)
      (freeDysonStieltjes z eta) (n : ℝ) := by
  let _ : NeZero n := ⟨by omega⟩
  apply proposition34_formula39_fixedEta_from_two_vanHandel
    (muG := muG)
    (fun omega ↦ stieltjesTrace (model.matrix omega) z eta)
      gaussian.matrix XGo d z eta heta hn hbandwidth.pos hC
      hprob hconcentration gaussian.entry_measurable hXGo hdiag
      hreG himG hreMean himMean hreVar himVar
  · exact bvhRemark613Hypothesis_of_gaussianCompanion
      model gaussian hbandwidth hCThird z heta
  · exact bbv
  · exact rate

/-- Complete fixed-`eta` form of v3 Proposition 3.4, formula (3.9).

Unlike the compositional helper above, this theorem constructs the good event and its
`1 - n⁻¹⁰` probability from the proved direct-product McDiarmid theorem, and obtains the
polynomial rate certificate from `proposition34CompleteAllEtaRateThreshold_spec`.  Thus no
concentration, event-probability, or rate-certificate premise remains.  The only external
comparison conclusion is the single fixed-`eta` BBV Theorem 2.8 hypothesis. -/
theorem proposition34_formula39_complete_from_only_bbv
    {Omega OmegaXi OmegaG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi] [MeasurableSpace OmegaG]
    {mu : Measure Omega} {nu : Measure OmegaXi} {muG : Measure OmegaG}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure muG]
    {n : ℕ} (hn : 2 ≤ n)
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (gaussian : BVH.GaussianCompanionModelV3
      n Omega OmegaXi OmegaG mu nu muG model)
    (XGo : OmegaG → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → OmegaG → ℂ) (z : ℂ) {eta : ℂ}
    (heta : 0 < eta.im)
    {B C cPrime : ℝ}
    (hbandwidth : IsBandwidth model.profile B)
    (hC : 8 ≤ C)
    (hCThird : BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant ≤ C)
    (hcPrime : 0 < cPrime)
    (hnLarge : proposition34CompleteAllEtaRateThreshold C cPrime ≤ n)
    (hscale : Real.rpow (n : ℝ) cPrime ≤ B * eta.im ^ 8)
    (hXGo : ∀ i j, Measurable (fun omega ↦ XGo omega i j))
    (hdiag : ∀ omega,
      gaussian.matrix omega - XGo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) muG)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) muG)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂muG = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂muG = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; muG] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; muG] ≤ 2 / B)
    (bbv : External.BBVTheorem28GaussianFreeHypothesis
      (∫ omega, stieltjesTrace (XGo omega) z eta ∂muG)
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
  let good : Set Omega :=
    ComplexConcentrationGood
      (fun omega ↦ stieltjesTrace (model.matrix omega) z eta)
      (∫ omega, stieltjesTrace (model.matrix omega) z eta ∂mu)
      (32 * Real.sqrt (Real.log (n : ℝ)) /
        (Real.sqrt (n : ℝ) * eta.im))
  have hprob : ProbabilityAtLeast mu good (1 - (n : ℝ) ^ (-10 : ℤ)) := by
    simpa only [good] using
      probabilityAtLeast_stieltjesTrace_complexConcentrationGood_v3_thirtytwo
        model z heta hn
  have hBn : B ≤ (n : ℝ) := by
    simpa using bandwidth_le_card model.profile hbandwidth
  obtain ⟨rate⟩ := proposition34CompleteAllEtaRateThreshold_spec
    (show 0 ≤ C by linarith) hcPrime hnLarge
      (one_le_bandwidth model.profile hbandwidth) hBn heta hscale
  have hfixed := proposition34_formula39_fixedEta_from_only_bbv
    model gaussian XGo d z eta heta hn hbandwidth hC hCThird
      (good := good) hprob
      (by
        intro omega homega
        exact homega)
      hXGo hdiag hreG himG hreMean himMean hreVar himVar bbv rate
  simpa only [good] using hfixed

/-- v3 Proposition 3.4, formula (3.10), at fixed `eta`, after the internally proved
BVH specialization and the deterministic free-Dyson bound.  The only remaining external
comparison conclusion is BBV Theorem 2.8. -/
theorem proposition34_formula310_fixedEta_from_only_bbv
    {Omega OmegaXi OmegaG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi] [MeasurableSpace OmegaG]
    {mu : Measure Omega} {nu : Measure OmegaXi} {muG : Measure OmegaG}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure muG]
    {n : ℕ}
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (gaussian : BVH.GaussianCompanionModelV3
      n Omega OmegaXi OmegaG mu nu muG model)
    (XGo : OmegaG → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → OmegaG → ℂ) (z eta : ℂ)
    (heta : 0 < eta.im) (hn : 2 ≤ n)
    {B C CD : ℝ} (hbandwidth : IsBandwidth model.profile B)
    (hC : 8 ≤ C)
    (hCThird : BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant ≤ C)
    {good : Set Omega}
    (hconcentration : ∀ omega ∈ good,
      ‖stieltjesTrace (model.matrix omega) z eta -
          ∫ omega', stieltjesTrace (model.matrix omega') z eta ∂mu‖ ≤
        CD * Real.sqrt (Real.log (n : ℝ)) /
          (Real.sqrt (n : ℝ) * eta.im))
    (hXGo : ∀ i j, Measurable (fun omega ↦ XGo omega i j))
    (hdiag : ∀ omega,
      gaussian.matrix omega - XGo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) muG)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) muG)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂muG = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂muG = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; muG] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; muG] ≤ 2 / B)
    (bbv : External.BBVTheorem28GaussianFreeHypothesis
      (∫ omega, stieltjesTrace (XGo omega) z eta ∂muG)
      (freeDysonStieltjes z eta) B eta.im C)
    (rate : PolynomialRateCertificate (n : ℝ)
      (formula311Error (n : ℝ) B eta.im C CD))
    {omega : Omega} (homega : omega ∈ good) :
    ‖stieltjesTrace (model.matrix omega) z eta‖ ≤ 2 := by
  let _ : NeZero n := ⟨by omega⟩
  apply proposition34_formula310_fixedEta_from_two_vanHandel
    (muG := muG)
    (fun omega ↦ stieltjesTrace (model.matrix omega) z eta)
      gaussian.matrix XGo d z eta heta hn hbandwidth.pos hC
      hconcentration gaussian.entry_measurable hXGo hdiag
      hreG himG hreMean himMean hreVar himVar
  · exact bvhRemark613Hypothesis_of_gaussianCompanion
      model gaussian hbandwidth hCThird z heta
  · exact bbv
  · exact rate
  · exact homega

/-- End-to-end arXiv:2410.16457v3, Proposition 3.4, with the specialized BVH comparison
fully formalized.  The only remaining external mathematical conclusion is the displayed
centrewise BBV Theorem 2.8 Gaussian-to-free hypothesis. -/
theorem proposition34_uniform_complete_from_only_bbv
    {Omega OmegaXi OmegaG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi] [MeasurableSpace OmegaG]
    {mu : Measure Omega} {nu : Measure OmegaXi} {muG : Measure OmegaG}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure muG]
    {n : ℕ} (hn : 2 ≤ n)
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (gaussian : BVH.GaussianCompanionModelV3
      n Omega OmegaXi OmegaG mu nu muG model)
    (XGo : OmegaG → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → OmegaG → ℂ) (z : ℂ)
    {B C cPrime : ℝ}
    (hbandwidth : IsBandwidth model.profile B)
    (hC : 8 ≤ C)
    (hCThird : BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant ≤ C)
    (hcPrime : 0 < cPrime)
    (hnLarge : proposition34CompleteRateThreshold C cPrime ≤ n)
    (hXGo : ∀ i j, Measurable (fun omega ↦ XGo omega i j))
    (hdiag : ∀ omega,
      gaussian.matrix omega - XGo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) muG)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) muG)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂muG = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂muG = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; muG] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; muG] ≤ 2 / B)
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
  apply proposition34_uniform_complete_from_two_vanHandel
    hn model gaussian.matrix XGo d z hbandwidth hC hcPrime hnLarge
      gaussian.entry_measurable hXGo hdiag hreG himG hreMean himMean hreVar himVar
  · intro k
    exact bvhRemark613Hypothesis_of_gaussianCompanion
      model gaussian hbandwidth hCThird z
        ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center_mem k).1
  · exact bbv

/-- End-to-end arXiv:2410.16457v3, Corollary 3.5, with only BBV Theorem 2.8 external.
The Poisson-kernel and counting argument, including the explicit constant `11`, remains fully
internal. -/
theorem corollary35_complete_from_only_bbv
    {Omega OmegaXi OmegaG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi] [MeasurableSpace OmegaG]
    {mu : Measure Omega} {nu : Measure OmegaXi} {muG : Measure OmegaG}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure muG]
    {n : ℕ} (hn : 2 ≤ n)
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (gaussian : BVH.GaussianCompanionModelV3
      n Omega OmegaXi OmegaG mu nu muG model)
    (XGo : OmegaG → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → OmegaG → ℂ) (z : ℂ)
    {B C cPrime : ℝ}
    (hbandwidth : IsBandwidth model.profile B)
    (hC : 8 ≤ C)
    (hCThird : BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant ≤ C)
    (hcPrime : 0 < cPrime)
    (hnLarge : proposition34CompleteRateThreshold C cPrime ≤ n)
    (hXGo : ∀ i j, Measurable (fun omega ↦ XGo omega i j))
    (hdiag : ∀ omega,
      gaussian.matrix omega - XGo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) muG)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) muG)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂muG = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂muG = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; muG] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; muG] ≤ 2 / B)
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
  apply corollary35_complete_from_two_vanHandel
    hn model gaussian.matrix XGo d z hbandwidth hC hcPrime hnLarge
      gaussian.entry_measurable hXGo hdiag hreG himG hreMean himMean hreVar himVar
  · intro k
    exact bvhRemark613Hypothesis_of_gaussianCompanion
      model gaussian hbandwidth hCThird z
        ((proposition34PaperEtaNet n B cPrime hbandwidth.pos (by omega)).center_mem k).1
  · exact bbv

end

end Arxiv2410V3

