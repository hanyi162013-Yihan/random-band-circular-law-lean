import ShortRingAnchor.ProbabilityModes
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The deterministic hard-edge estimate in Proposition 3.6

This file formalizes the elementary finite-family argument used in manuscript
formula (3.10).  The genuinely random-matrix input is deliberately absent:
the caller supplies a good event on which

* every singular value is at least `exp (-L)`, and
* at most `C * M * a` singular values lie below the cutoff `a`.

For `a <= 1`, each selected logarithm then has absolute value at most
`L`; summing and dividing by `M` gives `C * a * L`.  The final theorem turns
this deterministic good-event estimate into convergence in probability when
the complement of the good event and the deterministic bound both vanish.

No independence, distributional assumption, or random-matrix theorem is used
here.
-/

open Filter Set
open scoped BigOperators ENNReal Topology

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

/-- Indices of the singular values at or below the hard-edge cutoff `a`.

This is the finite counting set appearing in the deterministic part of
manuscript formula (3.10). -/
def smallSingularValueIndices {I : Type*} [Fintype I]
    (singularValue : I -> Real) (a : Real) : Finset I :=
  Finset.univ.filter fun i => singularValue i <= a

/-- The normalized absolute logarithmic mass below the cutoff `a`.

For a matrix of size `M`, take `I = Fin M`.  This is the hard-edge summand
controlled in the proof of Proposition 3.6 before the two rates displayed in
(3.10) are substituted. -/
def normalizedSmallLogMass {I : Type*} [Fintype I]
    (singularValue : I -> Real) (a : Real) : Real :=
  (∑ i ∈ smallSingularValueIndices singularValue a,
      |Real.log (singularValue i)|) / (Fintype.card I : Real)

/-- The normalized small logarithmic mass is nonnegative for every nonempty
finite family. -/
theorem normalizedSmallLogMass_nonneg
    {I : Type*} [Fintype I] [Nonempty I]
    (singularValue : I -> Real) (a : Real) :
    0 <= normalizedSmallLogMass singularValue a := by
  unfold normalizedSmallLogMass
  exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Nat.cast_nonneg _)

/-- Pointwise logarithmic step in the proof of (3.10).

If `exp (-L) <= x <= 1`, then `|log x| <= L` (these two inequalities already
force `L >= 0`).  In particular, the exponential lower bound also implies the
strict positivity needed to use monotonicity of the logarithm; nonnegativity
of the singular value need not be postulated separately. -/
theorem abs_log_le_of_exp_neg_le_of_le_one
    {x L : Real}
    (hlower : Real.exp (-L) <= x) (hupper : x <= 1) :
    |Real.log x| <= L := by
  have hx : 0 < x := (Real.exp_pos (-L)).trans_le hlower
  have hlogLower : -L <= Real.log x := by
    have h := Real.log_le_log (Real.exp_pos (-L)) hlower
    simpa using h
  have hlogUpper : Real.log x <= 0 :=
    Real.log_nonpos hx.le hupper
  rw [abs_of_nonpos hlogUpper]
  linarith

/-- **Deterministic part of Proposition 3.6, formula (3.10).**

For a nonempty finite family of singular values, assume the uniform hard-edge
bound `exp (-L) <= s_i` and the counting estimate

`#{i : s_i <= a} <= C * M * a`, where `M = #I`.

Then, for `a <= 1`, its normalized logarithmic mass below `a` is at
most `C * a * L`.  This is the complete finite-sum argument; all substantive
probabilistic singular-value estimates enter only through `hlower` and
`hcount`.  The manuscript's parameters have `a >= 0` and `C >= 0`, but those
sign assumptions are not needed for this implication once the displayed
counting inequality itself is assumed. -/
theorem normalizedSmallLogMass_le
    {I : Type*} [Fintype I] [Nonempty I]
    {singularValue : I -> Real} {a C L : Real}
    (ha1 : a <= 1) (hL : 0 <= L)
    (hlower : forall i, Real.exp (-L) <= singularValue i)
    (hcount :
      ((smallSingularValueIndices singularValue a).card : Real) <=
        C * (Fintype.card I : Real) * a) :
    normalizedSmallLogMass singularValue a <= C * a * L := by
  have hterm : ∀ i ∈ smallSingularValueIndices singularValue a,
      |Real.log (singularValue i)| <= L := by
    intro i hi
    have hismall : singularValue i <= a :=
      (Finset.mem_filter.mp hi).2
    exact abs_log_le_of_exp_neg_le_of_le_one (hlower i)
      (hismall.trans ha1)
  have hsum :
      (∑ i ∈ smallSingularValueIndices singularValue a,
          |Real.log (singularValue i)|) <=
        ((smallSingularValueIndices singularValue a).card : Real) * L := by
    calc
      (∑ i ∈ smallSingularValueIndices singularValue a,
          |Real.log (singularValue i)|)
          <= ∑ _i ∈ smallSingularValueIndices singularValue a, L := by
            exact Finset.sum_le_sum fun i hi => hterm i hi
      _ = ((smallSingularValueIndices singularValue a).card : Real) * L := by
            simp
  have hcountL :
      ((smallSingularValueIndices singularValue a).card : Real) * L <=
        (C * (Fintype.card I : Real) * a) * L :=
    mul_le_mul_of_nonneg_right hcount hL
  have hcardNat : 0 < Fintype.card I := Fintype.card_pos
  have hcard : (0 : Real) < Fintype.card I := by exact_mod_cast hcardNat
  unfold normalizedSmallLogMass
  apply (div_le_iff₀ hcard).2
  calc
    (∑ i ∈ smallSingularValueIndices singularValue a,
        |Real.log (singularValue i)|)
        <= ((smallSingularValueIndices singularValue a).card : Real) * L := hsum
    _ <= (C * (Fintype.card I : Real) * a) * L := hcountL
    _ = (C * a * L) * (Fintype.card I : Real) := by ring

/-- Good-event transfer lemma used after the estimate (3.10).

If `|X_n| <= rate_n` on `good_n`, the failure probabilities
`mu (good_n)^c` tend to zero, and `rate_n -> 0`, then `X_n -> 0` in
probability.  This elementary lemma needs neither independence nor
measurability hypotheses beyond those built into the ambient measure API. -/
theorem convergesInProbability_zero_of_goodEvent
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {X : Nat -> Omega -> Real}
    {good : Nat -> Set Omega} {rate : Nat -> Real}
    (hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0))
    (hrate : Tendsto rate atTop (nhds 0))
    (hbound : forall n omega, omega ∈ good n -> |X n omega| <= rate n) :
    ConvergesInProbability mu X 0 := by
  rw [convergesInProbability_iff_norm]
  intro epsilon hepsilon
  rw [ENNReal.tendsto_nhds_zero] at hbad ⊢
  intro delta hdelta
  have hbadSmall := hbad delta hdelta
  have hrateSmall : ∀ᶠ n in atTop, rate n < epsilon :=
    hrate.eventually (Iio_mem_nhds hepsilon)
  filter_upwards [hbadSmall, hrateSmall] with n hnBad hnRate
  calc
    mu {omega | epsilon <= ‖X n omega - 0‖}
        <= mu (good n)ᶜ := by
          apply measure_mono
          intro omega homega
          by_contra homegaBad
          have homegaGood : omega ∈ good n := by
            simpa using homegaBad
          have hX := hbound n omega homegaGood
          have homegaNorm : epsilon <= ‖X n omega - 0‖ := by
            exact homega
          have homega' : epsilon <= |X n omega| := by
            simpa only [sub_zero, Real.norm_eq_abs] using homegaNorm
          exact (not_lt_of_ge homega') (hX.trans_lt hnRate)
    _ <= delta := hnBad

/-- **Probabilistic conclusion of the hard-edge part of Proposition 3.6.**

The finite index type may vary with `n`.  On `good_n`, the two hypotheses in
the deterministic estimate above hold with parameters `a_n`, `C_n`, and
`L_n`.  If the bad-event probability tends to zero and
`C_n * a_n * L_n -> 0`, then the normalized small logarithmic mass is
`o_P(1)`.

Thus the only external input left at this stage is precisely the construction
of the good events together with their uniform lower-bound and counting
properties. -/
theorem normalizedSmallLogMass_convergesInProbability_zero
    {Omega : Type*} [MeasurableSpace Omega]
    {I : Nat -> Type*} [forall n, Fintype (I n)]
    [forall n, Nonempty (I n)]
    {mu : Measure Omega}
    {singularValue : forall n, Omega -> I n -> Real}
    {a C L : Nat -> Real} {good : Nat -> Set Omega}
    (ha1 : forall n, a n <= 1) (hL : forall n, 0 <= L n)
    (hlower : forall n omega, omega ∈ good n ->
      forall i, Real.exp (-(L n)) <= singularValue n omega i)
    (hcount : forall n omega, omega ∈ good n ->
      ((smallSingularValueIndices (singularValue n omega) (a n)).card : Real) <=
        C n * (Fintype.card (I n) : Real) * a n)
    (hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0))
    (hrate : Tendsto (fun n => C n * a n * L n) atTop (nhds 0)) :
    ConvergesInProbability mu
      (fun n omega => normalizedSmallLogMass (singularValue n omega) (a n)) 0 := by
  apply convergesInProbability_zero_of_goodEvent hbad hrate
  intro n omega homega
  rw [abs_of_nonneg
    (normalizedSmallLogMass_nonneg (singularValue n omega) (a n))]
  exact normalizedSmallLogMass_le (ha1 n) (hL n)
    (hlower n omega homega) (hcount n omega homega)

end ShortRingAnchor
