import ShortRingAnchor.LogDecomposition
import ShortRingAnchor.ProbabilityModes
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The upper singular-value edge in Proposition 3.6

This file formalizes the elementary upper-edge argument labeled (3.13) in
the source.  The only probabilistic input of the final theorem is an
explicitly supplied uniform bound on the expectation of the empirical
second moment.  In the random-matrix application that input is the elementary
Hilbert--Schmidt identity

`E[M⁻¹ ‖A - z I‖_HS²] = 1 + ‖z‖²`.

It is deliberately a theorem parameter below, rather than an axiom or a
hidden random-matrix theorem.
-/

open Filter Set
open scoped ENNReal Topology BigOperators

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## The pointwise inequality in (3.13) -/

/-- The uncentered logarithmic upper tail occurring literally on the
left-hand side of manuscript formula (3.13). -/
def upperRawLogTail (R x : Real) : Real :=
  if R < x then Real.log x else 0

/-- The numerical threshold appearing in (3.13) has logarithm `1 / 2`.
This small lemma keeps all uses of `R > sqrt(e)` explicit. -/
theorem half_lt_log_of_sqrt_exp_one_lt {R : Real}
    (hR : Real.sqrt (Real.exp 1) < R) :
    (1 : Real) / 2 < Real.log R := by
  have hsqrt_pos : 0 < Real.sqrt (Real.exp 1) := Real.sqrt_pos.2 (Real.exp_pos 1)
  have hlog := Real.strictMonoOn_log (Set.mem_Ioi.mpr hsqrt_pos)
    (Set.mem_Ioi.mpr (hsqrt_pos.trans hR)) hR
  rw [Real.log_sqrt (Real.exp_pos 1).le, Real.log_exp] at hlog
  exact hlog

/-- The correction form needed by the exact clipped-log decomposition.  For
`R > sqrt(e)`, `1_{x>R} (log x-log R)` is bounded by
`(log R / R²) x²`.

The proof is derivative-free: for `y = x / R ≥ 1`,
`log y ≤ y - 1 ≤ y²/2`, while `log R > 1/2`. -/
theorem upperLogCorrection_le_log_div_sq_mul_sq
    {R x : Real} (hR : Real.sqrt (Real.exp 1) < R) :
    upperLogCorrection R x <= (Real.log R / R ^ 2) * x ^ 2 := by
  have hsqrt_pos : 0 < Real.sqrt (Real.exp 1) := Real.sqrt_pos.2 (Real.exp_pos 1)
  have hRpos : 0 < R := hsqrt_pos.trans hR
  have hlogR : (1 : Real) / 2 < Real.log R := half_lt_log_of_sqrt_exp_one_lt hR
  by_cases hRx : R < x
  · rw [upperLogCorrection, if_pos hRx]
    have hx : 0 < x := hRpos.trans hRx
    let y : Real := x / R
    have hypos : 0 < y := div_pos hx hRpos
    have hyone : 1 <= y := by
      exact (le_div_iff₀ hRpos).2 (by simpa using hRx.le)
    have hlogy : Real.log y <= y - 1 := Real.log_le_sub_one_of_pos hypos
    have hyquad : y - 1 <= y ^ 2 / 2 := by
      nlinarith [sq_nonneg (y - 1)]
    have hhalf : y ^ 2 / 2 <= Real.log R * y ^ 2 := by
      have := mul_le_mul_of_nonneg_right hlogR.le (sq_nonneg y)
      nlinarith
    calc
      Real.log x - Real.log R = Real.log y := by
        simp only [y]
        exact (Real.log_div hx.ne' hRpos.ne').symm
      _ <= y ^ 2 / 2 := hlogy.trans hyquad
      _ <= Real.log R * y ^ 2 := hhalf
      _ = (Real.log R / R ^ 2) * x ^ 2 := by
        simp only [y]
        field_simp [hRpos.ne']
  · rw [upperLogCorrection, if_neg hRx]
    exact mul_nonneg (div_nonneg (by linarith) (sq_nonneg R)) (sq_nonneg x)

/-- **Manuscript formula (3.13), literal pointwise form.**  For
`R > sqrt(e)`,

`1_{x>R} log x ≤ (log R / R²) x²`.

The proof uses that `log x / x²` is decreasing beyond `sqrt(e)`, encoded
without differentiation by writing `x=Ry` and using
`log y ≤ y-1 ≤ (y²-1)/2` for `y≥1`. -/
theorem upperRawLogTail_le_log_div_sq_mul_sq
    {R x : Real} (hR : Real.sqrt (Real.exp 1) < R) :
    upperRawLogTail R x <= (Real.log R / R ^ 2) * x ^ 2 := by
  have hsqrt_pos : 0 < Real.sqrt (Real.exp 1) :=
    Real.sqrt_pos.2 (Real.exp_pos 1)
  have hRpos : 0 < R := hsqrt_pos.trans hR
  have hlogR : (1 : Real) / 2 < Real.log R :=
    half_lt_log_of_sqrt_exp_one_lt hR
  by_cases hRx : R < x
  · rw [upperRawLogTail, if_pos hRx]
    have hx : 0 < x := hRpos.trans hRx
    let y : Real := x / R
    have hypos : 0 < y := div_pos hx hRpos
    have hyone : 1 <= y := by
      exact (le_div_iff₀ hRpos).2 (by simpa using hRx.le)
    have hlogy : Real.log y <= y - 1 :=
      Real.log_le_sub_one_of_pos hypos
    have hyquad : y - 1 <= (y ^ 2 - 1) / 2 := by
      nlinarith [sq_nonneg (y - 1)]
    have hquadNonneg : 0 <= y ^ 2 - 1 := by nlinarith
    have hscale : (y ^ 2 - 1) / 2 <=
        Real.log R * (y ^ 2 - 1) := by
      have hmul := mul_le_mul_of_nonneg_right hlogR.le hquadNonneg
      nlinarith
    have hlogxy : Real.log x = Real.log R + Real.log y := by
      dsimp only [y]
      rw [Real.log_div hx.ne' hRpos.ne']
      ring
    calc
      Real.log x = Real.log R + Real.log y := hlogxy
      _ <= Real.log R + (y ^ 2 - 1) / 2 :=
        by linarith
      _ <= Real.log R + Real.log R * (y ^ 2 - 1) :=
        by linarith
      _ = Real.log R * y ^ 2 := by ring
      _ = (Real.log R / R ^ 2) * x ^ 2 := by
        dsimp only [y]
        field_simp [hRpos.ne']
  · rw [upperRawLogTail, if_neg hRx]
    exact mul_nonneg (div_nonneg (by linarith) (sq_nonneg R)) (sq_nonneg x)

/-- Literal finite-family form of (3.13). -/
theorem empiricalUpperRawLogTail_le_log_div_sq_mul_secondMoment
    {I : Type*} [Fintype I] {R : Real} {x : I -> Real}
    (hR : Real.sqrt (Real.exp 1) < R) :
    empiricalAverage x (upperRawLogTail R) <=
      (Real.log R / R ^ 2) * empiricalAverage x (fun t => t ^ 2) := by
  unfold empiricalAverage
  calc
    (∑ i, upperRawLogTail R (x i)) / (Fintype.card I : Real)
        <= (∑ i, (Real.log R / R ^ 2) * x i ^ 2) /
            (Fintype.card I : Real) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact Finset.sum_le_sum fun i _ =>
            upperRawLogTail_le_log_div_sq_mul_sq hR
    _ = (Real.log R / R ^ 2) *
        ((∑ i, x i ^ 2) / (Fintype.card I : Real)) := by
          rw [← Finset.mul_sum]
          ring

/-- Empirical correction form used by the clipped-log proof.  It follows
from the same numerical argument as (3.13). -/
theorem empiricalUpperLogCorrection_le_log_div_sq_mul_secondMoment
    {I : Type*} [Fintype I] {R : Real} {x : I -> Real}
    (hR : Real.sqrt (Real.exp 1) < R) :
    empiricalUpperLogCorrection R x <=
      (Real.log R / R ^ 2) * empiricalAverage x (fun t => t ^ 2) := by
  unfold empiricalUpperLogCorrection empiricalAverage
  calc
    (∑ i, upperLogCorrection R (x i)) / (Fintype.card I : Real)
        <= (∑ i, (Real.log R / R ^ 2) * x i ^ 2) /
            (Fintype.card I : Real) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          apply Finset.sum_le_sum
          intro i hi
          exact upperLogCorrection_le_log_div_sq_mul_sq hR
    _ = (Real.log R / R ^ 2) *
        ((∑ i, x i ^ 2) / (Fintype.card I : Real)) := by
          rw [← Finset.mul_sum]
          ring

/-- Positivity of the cutoff alone makes the upper correction nonnegative;
no positivity or invertibility assumption on `x` is needed. -/
theorem upperLogCorrection_nonneg_of_pos_cutoff
    {R x : Real} (hR : 0 < R) : 0 <= upperLogCorrection R x := by
  by_cases hRx : R < x
  · rw [upperLogCorrection, if_pos hRx]
    exact sub_nonneg.mpr (Real.log_le_log hR hRx.le)
  · simp [upperLogCorrection, hRx]

/-- The empirical upper correction is nonnegative, including when some
singular values vanish. -/
theorem empiricalUpperLogCorrection_nonneg
    {I : Type*} [Fintype I] {R : Real} {x : I -> Real}
    (hR : 0 < R) :
    0 <= empiricalUpperLogCorrection R x := by
  unfold empiricalUpperLogCorrection empiricalAverage
  exact div_nonneg (Finset.sum_nonneg fun i hi =>
    upperLogCorrection_nonneg_of_pos_cutoff hR) (Nat.cast_nonneg _)

/-- A deterministic, measure-free consequence of (3.13): a uniform
empirical second-moment bound gives the displayed deterministic error bound. -/
theorem empiricalUpperLogCorrection_le_of_secondMoment_le
    {I : Type*} [Fintype I] {R C : Real} {x : I -> Real}
    (hR : Real.sqrt (Real.exp 1) < R)
    (hC : empiricalAverage x (fun t => t ^ 2) <= C) :
    empiricalUpperLogCorrection R x <= (Real.log R / R ^ 2) * C := by
  have hcoeff : 0 <= Real.log R / R ^ 2 := by
    have hlog := (half_lt_log_of_sqrt_exp_one_lt hR).le
    exact div_nonneg (by linarith) (sq_nonneg R)
  exact (empiricalUpperLogCorrection_le_log_div_sq_mul_secondMoment hR).trans
    (mul_le_mul_of_nonneg_left hC hcoeff)

/-- A coarser measure-free backup, obtained directly from
`LogDecomposition.empiricalUpperLogCorrection_le_secondMoment_div`.
It is not needed for the source-exact `(log R) / R²` proof, but records that
even the elementary `1 / R` estimate suffices under a deterministic moment
bound. -/
theorem empiricalUpperLogCorrection_le_of_secondMoment_le_coarse
    {I : Type*} [Fintype I] {R C : Real} {x : I -> Real}
    (hR : 1 <= R) (hx : forall i, 0 < x i)
    (hC : empiricalAverage x (fun t => t ^ 2) <= C) :
    empiricalUpperLogCorrection R x <= C / R := by
  exact (empiricalUpperLogCorrection_le_secondMoment_div hR hx).trans
    (div_le_div_of_nonneg_right hC (zero_le_one.trans hR))

/-! ## The scalar cutoff tends to zero -/

/-- The scalar factor in (3.13) tends to zero as `R -> infinity`. -/
theorem tendsto_log_div_sq_atTop :
    Tendsto (fun R : Real => Real.log R / R ^ 2) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_inv_atTop_zero
  · filter_upwards [eventually_ge_atTop (1 : Real)] with R hR
    exact div_nonneg (Real.log_nonneg hR) (sq_nonneg R)
  · filter_upwards [eventually_gt_atTop (1 : Real)] with R hR
    have hRpos : 0 < R := zero_lt_one.trans hR
    have hlog_le : Real.log R <= R :=
      (Real.log_le_sub_one_of_pos hRpos).trans (by linarith)
    calc
      Real.log R / R ^ 2 <= R / R ^ 2 :=
        div_le_div_of_nonneg_right hlog_le (sq_nonneg R)
      _ = R⁻¹ := by field_simp [hRpos.ne']

omit [MeasurableSpace Omega] in
/-- Measure-free sequential form: if the second moments are deterministically
bounded by `C`, then the (3.13) corrections are eventually uniformly smaller
than every positive `epsilon`. -/
theorem empiricalUpperLogCorrection_eventually_uniform_small
    {I : Type*} [Fintype I] {R : Nat -> Real}
    {x : Nat -> Omega -> I -> Real} {C : Real}
    (hRtop : Tendsto R atTop atTop)
    (hR : forall n, Real.sqrt (Real.exp 1) < R n)
    (hsecond : forall n omega,
      empiricalAverage (x n omega) (fun t => t ^ 2) <= C) :
    forall epsilon : Real, 0 < epsilon ->
      ∀ᶠ n in atTop, forall omega,
        empiricalUpperLogCorrection (R n) (x n omega) < epsilon := by
  intro epsilon hepsilon
  have hfactor : Tendsto (fun n => (Real.log (R n) / (R n) ^ 2) * C)
      atTop (nhds 0) :=
    by simpa only [Function.comp_apply, zero_mul] using
      (tendsto_log_div_sq_atTop.comp hRtop).mul_const C
  have hsmall := hfactor.eventually (Iio_mem_nhds hepsilon)
  filter_upwards [hsmall] with n hn
  intro omega
  exact (empiricalUpperLogCorrection_le_of_secondMoment_le
    (hR n) (hsecond n omega)).trans_lt hn

/-! ## Markov's inequality and convergence in probability -/

/-- A real-valued form of Markov's inequality suited to an externally
supplied expectation bound. -/
theorem measure_ge_le_of_integral_le
    {mu : Measure Omega} {X : Omega -> Real} {C epsilon : Real}
    (hXint : Integrable X mu) (hXnonneg : forall omega, 0 <= X omega)
    (hmean : ∫ omega, X omega ∂mu <= C) (hepsilon : 0 < epsilon) :
    mu {omega | epsilon <= X omega} <= ENNReal.ofReal (C / epsilon) := by
  have hscaled : Integrable (fun omega => X omega / epsilon) mu :=
    hXint.div_const epsilon
  calc
    mu {omega | epsilon <= X omega}
        <= ENNReal.ofReal (∫ omega, X omega / epsilon ∂mu) := by
          apply hscaled.measure_le_integral
          · exact Filter.Eventually.of_forall fun omega =>
              div_nonneg (hXnonneg omega) hepsilon.le
          · intro omega homega
            exact (le_div_iff₀ hepsilon).2 (by simpa [mul_comm] using homega)
    _ = ENNReal.ofReal ((∫ omega, X omega ∂mu) / epsilon) := by
          rw [integral_div]
    _ <= ENNReal.ofReal (C / epsilon) := by
          exact ENNReal.ofReal_le_ofReal ((div_le_div_iff_of_pos_right hepsilon).2 hmean)

/-- A nonnegative integrable random variable whose expectation is bounded
by a deterministic `rate_n -> 0` converges to zero in probability. -/
theorem convergesInProbability_of_nonneg_integral_bound
    {mu : Measure Omega} {X : Nat -> Omega -> Real} {rate : Nat -> Real}
    (hXint : forall n, Integrable (X n) mu)
    (hXnonneg : forall n omega, 0 <= X n omega)
    (hmean : forall n, ∫ omega, X n omega ∂mu <= rate n)
    (hrate : Tendsto rate atTop (nhds 0)) :
    ConvergesInProbability mu X 0 := by
  rw [convergesInProbability_iff_norm]
  intro epsilon hepsilon
  have hupper : Tendsto (fun n => ENNReal.ofReal (rate n / epsilon))
      atTop (nhds 0) := by
    have hreal : Tendsto (fun n => rate n / epsilon) atTop (nhds 0) := by
      simpa using hrate.div_const epsilon
    have hcomp := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    change Tendsto (fun n => ENNReal.ofReal (rate n / epsilon)) atTop
      (nhds (ENNReal.ofReal 0)) at hcomp
    simpa only [ENNReal.ofReal_zero] using hcomp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro n
    exact zero_le
  · intro n
    have hmarkov := measure_ge_le_of_integral_le (hXint n) (hXnonneg n)
      (hmean n) hepsilon
    simpa [Real.norm_eq_abs, abs_of_nonneg (hXnonneg n _)] using hmarkov

/-- Scaled-domination form of the preceding Markov argument.  This isolates
exactly the probability theory needed in (3.13). -/
theorem convergesInProbability_of_nonneg_le_scaled_integrable
    {mu : Measure Omega} {Y S : Nat -> Omega -> Real}
    {c : Nat -> Real} {C : Real}
    (hYnonneg : forall n omega, 0 <= Y n omega)
    (hSnonneg : forall n omega, 0 <= S n omega)
    (hSint : forall n, Integrable (S n) mu)
    (hdom : forall n omega, Y n omega <= c n * S n omega)
    (hc_nonneg : forall n, 0 <= c n)
    (hmean : forall n, ∫ omega, S n omega ∂mu <= C)
    (hc : Tendsto c atTop (nhds 0)) :
    ConvergesInProbability mu Y 0 := by
  let Z : Nat -> Omega -> Real := fun n omega => c n * S n omega
  have hZint : forall n, Integrable (Z n) mu := fun n => (hSint n).const_mul (c n)
  have hZnonneg : forall n omega, 0 <= Z n omega := fun n omega =>
    mul_nonneg (hc_nonneg n) (hSnonneg n omega)
  have hZmean : forall n, ∫ omega, Z n omega ∂mu <= c n * C := by
    intro n
    rw [show (∫ omega, Z n omega ∂mu) =
        c n * ∫ omega, S n omega ∂mu by
      simp only [Z, integral_const_mul]]
    exact mul_le_mul_of_nonneg_left (hmean n) (hc_nonneg n)
  have hZ : ConvergesInProbability mu Z 0 :=
    convergesInProbability_of_nonneg_integral_bound hZint hZnonneg hZmean
      (by simpa only [zero_mul] using hc.mul_const C)
  apply convergesInProbability_zero_of_norm_le hZ
  intro n omega
  simpa [Real.norm_eq_abs, abs_of_nonneg (hYnonneg n omega),
    abs_of_nonneg (hZnonneg n omega)] using hdom n omega

/-- Source (3.13), probability conclusion.  A uniform expectation bound on
the empirical second singular-value moment is the sole supplied mathematical
input; all truncation and Markov steps are proved above. -/
theorem empiricalUpperLogCorrection_convergesInProbability
    {I : Type*} [Fintype I] {mu : Measure Omega}
    {R : Nat -> Real} {x : Nat -> Omega -> I -> Real} {C : Real}
    (hRtop : Tendsto R atTop atTop)
    (hR : forall n, Real.sqrt (Real.exp 1) < R n)
    (hsecondInt : forall n, Integrable
      (fun omega => empiricalAverage (x n omega) (fun t => t ^ 2)) mu)
    (hsecondMean : forall n,
      ∫ omega, empiricalAverage (x n omega) (fun t => t ^ 2) ∂mu <= C) :
    ConvergesInProbability mu
      (fun n omega => empiricalUpperLogCorrection (R n) (x n omega)) 0 := by
  let c : Nat -> Real := fun n => Real.log (R n) / (R n) ^ 2
  let S : Nat -> Omega -> Real := fun n omega =>
    empiricalAverage (x n omega) (fun t => t ^ 2)
  apply convergesInProbability_of_nonneg_le_scaled_integrable
    (Y := fun n omega => empiricalUpperLogCorrection (R n) (x n omega))
    (S := S) (c := c) (C := C)
  · intro n omega
    have hRpos : 0 < R n :=
      (Real.sqrt_pos.2 (Real.exp_pos 1)).trans (hR n)
    exact empiricalUpperLogCorrection_nonneg hRpos
  · intro n omega
    unfold S empiricalAverage
    exact div_nonneg (Finset.sum_nonneg fun i hi => sq_nonneg (x n omega i))
      (Nat.cast_nonneg _)
  · exact hsecondInt
  · intro n omega
    exact empiricalUpperLogCorrection_le_log_div_sq_mul_secondMoment
      (hR n)
  · intro n
    have hlog : 0 <= Real.log (R n) := by
      linarith [half_lt_log_of_sqrt_exp_one_lt (hR n)]
    exact div_nonneg hlog (sq_nonneg (R n))
  · exact hsecondMean
  · exact tendsto_log_div_sq_atTop.comp hRtop

end ShortRingAnchor
