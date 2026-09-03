import ShortRingAnchor.TruncationAssembly
import ShortRingAnchor.UpperEdge

/-!
# Uniform fixed-cutoff form of formula (3.13)

`UpperEdge.lean` proves the pointwise estimate and Markov's inequality.  This
file packages them with the exact quantifier order needed by the final
`M -> infinity`, then `R -> infinity` argument.
-/

open Filter Set
open scoped ENNReal Topology

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Fixed-cutoff Markov bound obtained from source formula (3.13). -/
theorem measure_empiricalUpperLogCorrection_ge_le
    {I : Type*} [Fintype I]
    {mu : Measure Omega} {x : Omega -> I -> Real}
    {R C epsilon : Real}
    (hR : Real.sqrt (Real.exp 1) < R)
    (hsecondInt : Integrable
      (fun omega => empiricalAverage (x omega) (fun t => t ^ 2)) mu)
    (hsecondMean :
      ∫ omega, empiricalAverage (x omega) (fun t => t ^ 2) ∂mu <= C)
    (_hC : 0 <= C) (hepsilon : 0 < epsilon) :
    mu {omega | epsilon <= empiricalUpperLogCorrection R (x omega)} <=
      ENNReal.ofReal
        (((Real.log R / R ^ 2) * C) / epsilon) := by
  let c : Real := Real.log R / R ^ 2
  let S : Omega -> Real := fun omega =>
    empiricalAverage (x omega) (fun t => t ^ 2)
  let Z : Omega -> Real := fun omega => c * S omega
  have hc : 0 <= c := by
    dsimp only [c]
    have hlog : 0 <= Real.log R := by
      linarith [half_lt_log_of_sqrt_exp_one_lt hR]
    exact div_nonneg hlog (sq_nonneg R)
  have hSnonneg : forall omega, 0 <= S omega := by
    intro omega
    unfold S empiricalAverage
    exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (x omega i))
      (Nat.cast_nonneg _)
  have hZint : Integrable Z mu := by
    exact hsecondInt.const_mul c
  have hZnonneg : forall omega, 0 <= Z omega := fun omega =>
    mul_nonneg hc (hSnonneg omega)
  have hZmean : (∫ omega, Z omega ∂mu) <= c * C := by
    rw [show (∫ omega, Z omega ∂mu) =
        c * ∫ omega, S omega ∂mu by
      simp only [Z, integral_const_mul]]
    exact mul_le_mul_of_nonneg_left hsecondMean hc
  calc
    mu {omega | epsilon <= empiricalUpperLogCorrection R (x omega)} <=
        mu {omega | epsilon <= Z omega} := by
          apply measure_mono
          intro omega homega
          exact homega.trans
            (empiricalUpperLogCorrection_le_log_div_sq_mul_secondMoment hR)
    _ <= ENNReal.ofReal ((c * C) / epsilon) :=
      measure_ge_le_of_integral_le hZint hZnonneg hZmean hepsilon
    _ = ENNReal.ofReal (((Real.log R / R ^ 2) * C) / epsilon) := rfl

/-- **Uniform fixed-`R` probability conclusion of (3.13).**

Uniform expectation bounds for the empirical second moments of both matrix
families imply `UpperCorrectionsUniformlyNegligible`.  This is stronger than
merely proving convergence along one diagonal sequence of cutoffs and is
exactly what the paper's iterated-limit argument needs. -/
theorem upperCorrectionsUniformlyNegligible_of_secondMomentBounds
    {I J : Nat -> Type*}
    [forall n, Fintype (I n)] [forall n, Fintype (J n)]
    {mu : Measure Omega}
    {h : forall n, Omega -> I n -> Real}
    {g : forall n, Omega -> J n -> Real}
    {R : Nat -> Real} {CH CG : Real}
    (hRtop : Tendsto R atTop atTop)
    (hR : forall r, Real.sqrt (Real.exp 1) < R r)
    (hCH : 0 <= CH) (hCG : 0 <= CG)
    (hHsecondInt : forall n, Integrable
      (fun omega => empiricalAverage (h n omega) (fun t => t ^ 2)) mu)
    (hGsecondInt : forall n, Integrable
      (fun omega => empiricalAverage (g n omega) (fun t => t ^ 2)) mu)
    (hHsecondMean : forall n,
      ∫ omega, empiricalAverage (h n omega) (fun t => t ^ 2) ∂mu <= CH)
    (hGsecondMean : forall n,
      ∫ omega, empiricalAverage (g n omega) (fun t => t ^ 2) ∂mu <= CG) :
    UpperCorrectionsUniformlyNegligible mu h g R := by
  intro epsilon hepsilon delta hdelta
  have hepsilonHalf : 0 < epsilon / 2 := half_pos hepsilon
  let c : Nat -> Real := fun r => Real.log (R r) / (R r) ^ 2
  have hc : Tendsto c atTop (nhds 0) :=
    tendsto_log_div_sq_atTop.comp hRtop
  have hrealH : Tendsto (fun r => (c r * CH) / (epsilon / 2))
      atTop (nhds 0) := by
    simpa only [zero_mul, zero_div] using (hc.mul_const CH).div_const (epsilon / 2)
  have hrealG : Tendsto (fun r => (c r * CG) / (epsilon / 2))
      atTop (nhds 0) := by
    simpa only [zero_mul, zero_div] using (hc.mul_const CG).div_const (epsilon / 2)
  have hboundTendsto : Tendsto
      (fun r =>
        ENNReal.ofReal ((c r * CH) / (epsilon / 2)) +
          ENNReal.ofReal ((c r * CG) / (epsilon / 2)))
      atTop (nhds 0) := by
    have hH := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hrealH
    have hG := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hrealG
    simpa only [Function.comp_apply, ENNReal.ofReal_zero, add_zero] using hH.add hG
  have hsmall : ∀ᶠ r in atTop,
      ENNReal.ofReal ((c r * CH) / (epsilon / 2)) +
        ENNReal.ofReal ((c r * CG) / (epsilon / 2)) < delta :=
    hboundTendsto.eventually (Iio_mem_nhds hdelta)
  obtain ⟨r, hr⟩ := hsmall.exists
  refine ⟨r, Filter.Eventually.of_forall fun n => ?_⟩
  calc
    mu {omega | epsilon / 2 <=
          empiricalUpperLogCorrection (R r) (h n omega)} +
        mu {omega | epsilon / 2 <=
          empiricalUpperLogCorrection (R r) (g n omega)} <=
      ENNReal.ofReal ((c r * CH) / (epsilon / 2)) +
        ENNReal.ofReal ((c r * CG) / (epsilon / 2)) := by
          exact add_le_add
            (measure_empiricalUpperLogCorrection_ge_le
              (mu := mu) (x := h n) (R := R r) (C := CH)
              (epsilon := epsilon / 2)
              (hR r) (hHsecondInt n) (hHsecondMean n) hCH hepsilonHalf)
            (measure_empiricalUpperLogCorrection_ge_le
              (mu := mu) (x := g n) (R := R r) (C := CG)
              (epsilon := epsilon / 2)
              (hR r) (hGsecondInt n) (hGsecondMean n) hCG hepsilonHalf)
    _ < delta := hr

end ShortRingAnchor
