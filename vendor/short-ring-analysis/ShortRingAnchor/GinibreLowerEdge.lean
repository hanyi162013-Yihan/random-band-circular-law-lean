import ShortRingAnchor.HardEdge
import ShortRingAnchor.LogDecomposition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Ginibre lower edge in Proposition 3.6

This file formalizes the elementary and probabilistic part of manuscript
formula (3.14).  The only BC12 input is isolated as
`BC12GinibreNegativeMomentTightness`: for one fixed `p = p(z) > 0`, the
normalized empirical negative moment

`(#I)⁻¹ * ∑ i, sᵢ⁻ᵖ`

is bounded in probability.  From that input we prove in Lean that the
normalized absolute logarithmic mass below a deterministic cutoff `aₙ → 0`
converges to zero in probability.

The pointwise estimate is exactly the one displayed immediately before
(3.14): for `0 < s ≤ a ≤ 1`,

`|log s| = log (1 / s) ≤ (2 / p) * a^(p/2) * s^(-p)`.

We also record the related clipping-correction estimate
`log a - log s ≤ (a / s)^p / p`.  It is useful for the final
low/middle/high decomposition, but is weaker than the absolute-log estimate
at `s = a` and is therefore not used as a substitute for (3.14).
-/

open Filter Set
open scoped BigOperators ENNReal Topology

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

/-- The normalized empirical negative `p`-moment of a finite family.

For formula (3.14), `I = Fin M` and `s i` is the `i`-th singular value of
`G_M - z I_M`. -/
def normalizedNegativeMoment {I : Type*} [Fintype I]
    (p : Real) (s : I -> Real) : Real :=
  empiricalAverage s (fun x => x ^ (-p))

/-- Negative empirical moments are nonnegative. -/
theorem normalizedNegativeMoment_nonneg {I : Type*} [Fintype I]
    {p : Real} {s : I -> Real} (hs : forall i, 0 <= s i) :
    0 <= normalizedNegativeMoment p s := by
  unfold normalizedNegativeMoment empiricalAverage
  exact div_nonneg
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hs i) (-p))
    (Nat.cast_nonneg _)

/-- **The sole external BC12 interface used for (3.14).**

BC12 supplies this proposition for the shifted normalized circular Ginibre
singular values and for some fixed exponent `p = p(z) > 0`.  This is a
definition of the required hypothesis, not an axiom or a theorem claiming
that BC12 has been formalized. -/
def BC12GinibreNegativeMomentTightness
    {Omega : Type*} [MeasurableSpace Omega]
    {I : Nat -> Type*} [forall n, Fintype (I n)]
    (mu : Measure Omega) (p : Real)
    (singularValue : forall n, Omega -> I n -> Real) : Prop :=
  BoundedInProbability mu
    (fun n omega => normalizedNegativeMoment p (singularValue n omega))

/-- Elementary logarithm-versus-power estimate.

For `x > 0` and `q > 0`, this follows from
`log (x^q) ≤ x^q - 1 ≤ x^q` and `log (x^q) = q log x`.
This is the analytic engine behind the displayed inequality before (3.14). -/
theorem log_le_rpow_div {x q : Real} (hx : 0 < x) (hq : 0 < q) :
    Real.log x <= x ^ q / q := by
  apply (le_div_iff₀ hq).2
  calc
    Real.log x * q = Real.log (x ^ q) := by
      rw [Real.log_rpow hx]
      ring
    _ <= x ^ q - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx q)
    _ <= x ^ q := by linarith

/-- Clipping-correction estimate valid for any positive `a` and `s`.

When `s < a`, this reads
`log a - log s ≤ (a / s)^p / p`. -/
theorem log_sub_log_le_div_rpow_div
    {a s p : Real} (ha : 0 < a) (hs : 0 < s) (hp : 0 < p) :
    Real.log a - Real.log s <= (a / s) ^ p / p := by
  rw [← Real.log_div (ne_of_gt ha) (ne_of_gt hs)]
  exact log_le_rpow_div (div_pos ha hs) hp

/-- Factor the preceding bound into a deterministic cutoff power and the
negative empirical-moment integrand. -/
theorem div_rpow_div_eq_scaled_negativePower
    {a s p : Real} (ha : 0 < a) (hs : 0 < s) :
    (a / s) ^ p / p = (a ^ p / p) * s ^ (-p) := by
  rw [Real.div_rpow ha.le hs.le, Real.rpow_neg hs.le]
  ring

/-- Pointwise control of the low clipping correction by a negative moment. -/
theorem lowerLogCorrection_le_scaled_negativePower
    {a s p : Real} (ha : 0 < a) (hs : 0 < s) (hp : 0 < p) :
    lowerLogCorrection a s <= (a ^ p / p) * s ^ (-p) := by
  by_cases hsa : s < a
  · rw [lowerLogCorrection, if_pos hsa]
    rw [← div_rpow_div_eq_scaled_negativePower ha hs]
    exact log_sub_log_le_div_rpow_div ha hs hp
  · rw [lowerLogCorrection, if_neg hsa]
    exact mul_nonneg (div_nonneg (Real.rpow_nonneg ha.le p) hp.le)
      (Real.rpow_nonneg hs.le (-p))

/-- The first half of the exact paper inequality:
`log (1/s) ≤ (2/p) s^(-p/2)`. -/
theorem log_one_div_le_two_div_mul_rpow_neg_half
    {s p : Real} (hs : 0 < s) (hp : 0 < p) :
    Real.log (1 / s) <= (2 / p) * s ^ (-(p / 2)) := by
  have hbase := log_le_rpow_div (div_pos zero_lt_one hs) (half_pos hp)
  calc
    Real.log (1 / s) <= (1 / s) ^ (p / 2) / (p / 2) := hbase
    _ = (2 / p) * s ^ (-(p / 2)) := by
      rw [one_div, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le]
      field_simp [ne_of_gt hp]

/-- Power comparison used to insert the cutoff `a^(p/2)` in (3.14). -/
theorem rpow_neg_half_le_cutoff_mul_rpow_neg
    {s a p : Real} (hs : 0 < s) (hsa : s <= a) (hp : 0 < p) :
    s ^ (-(p / 2)) <= a ^ (p / 2) * s ^ (-p) := by
  have hpow : s ^ (p / 2) <= a ^ (p / 2) :=
    Real.rpow_le_rpow hs.le hsa (half_pos hp).le
  have hneg : 0 <= s ^ (-p) := Real.rpow_nonneg hs.le (-p)
  calc
    s ^ (-(p / 2)) = s ^ (p / 2) * s ^ (-p) := by
      rw [← Real.rpow_add hs]
      congr 1
      ring
    _ <= a ^ (p / 2) * s ^ (-p) :=
      mul_le_mul_of_nonneg_right hpow hneg

/-- **Elementary inequality displayed immediately before formula (3.14).**

For `0 < s ≤ a ≤ 1` and `p > 0`,
`|log s| ≤ (2/p) a^(p/2) s^(-p)`. -/
theorem abs_log_le_two_div_mul_cutoff_rpow_mul_negativePower
    {s a p : Real} (hs : 0 < s) (hsa : s <= a) (ha1 : a <= 1)
    (hp : 0 < p) :
    |Real.log s| <= (2 / p) * a ^ (p / 2) * s ^ (-p) := by
  have hs1 : s <= 1 := hsa.trans ha1
  have hlogs : Real.log s <= 0 := Real.log_nonpos hs.le hs1
  rw [abs_of_nonpos hlogs, ← Real.log_inv, ← one_div]
  calc
    Real.log (1 / s) <= (2 / p) * s ^ (-(p / 2)) :=
      log_one_div_le_two_div_mul_rpow_neg_half hs hp
    _ <= (2 / p) * (a ^ (p / 2) * s ^ (-p)) := by
      exact mul_le_mul_of_nonneg_left
        (rpow_neg_half_le_cutoff_mul_rpow_neg hs hsa hp)
        (div_nonneg (by norm_num) hp.le)
    _ = (2 / p) * a ^ (p / 2) * s ^ (-p) := by ring

/-- Finite-family version of the deterministic bound in (3.14).

The left side is exactly
`(#I)⁻¹ ∑_{sᵢ≤a} |log sᵢ|`; the right side is the paper's deterministic
factor `(2/p) a^(p/2)` times the full normalized negative moment. -/
theorem normalizedSmallLogMass_le_scaled_negativeMoment
    {I : Type*} [Fintype I] [Nonempty I]
    {singularValue : I -> Real} {a p : Real}
    (hs : forall i, 0 < singularValue i)
    (ha : 0 < a) (ha1 : a <= 1) (hp : 0 < p) :
    normalizedSmallLogMass singularValue a <=
      ((2 / p) * a ^ (p / 2)) *
        normalizedNegativeMoment p singularValue := by
  let c : Real := (2 / p) * a ^ (p / 2)
  have hc : 0 <= c := mul_nonneg (div_nonneg (by norm_num) hp.le)
    (Real.rpow_nonneg ha.le (p / 2))
  have hselected :
      (∑ i ∈ smallSingularValueIndices singularValue a,
          |Real.log (singularValue i)|) <=
        ∑ i ∈ smallSingularValueIndices singularValue a,
          c * singularValue i ^ (-p) := by
    apply Finset.sum_le_sum
    intro i hi
    exact abs_log_le_two_div_mul_cutoff_rpow_mul_negativePower
      (hs i) ((Finset.mem_filter.mp hi).2) ha1 hp
  have hsubset :
      (∑ i ∈ smallSingularValueIndices singularValue a,
          c * singularValue i ^ (-p)) <=
        ∑ i, c * singularValue i ^ (-p) := by
    apply Finset.sum_le_univ_sum_of_nonneg
    intro i
    exact mul_nonneg hc (Real.rpow_nonneg (hs i).le (-p))
  unfold normalizedSmallLogMass normalizedNegativeMoment empiricalAverage
  calc
    (∑ i ∈ smallSingularValueIndices singularValue a,
        |Real.log (singularValue i)|) / (Fintype.card I : Real)
        <= (∑ i, c * singularValue i ^ (-p)) /
          (Fintype.card I : Real) :=
            div_le_div_of_nonneg_right (hselected.trans hsubset)
              (Nat.cast_nonneg _)
    _ = c * ((∑ i, singularValue i ^ (-p)) /
          (Fintype.card I : Real)) := by
            rw [← Finset.mul_sum]
            ring
    _ = ((2 / p) * a ^ (p / 2)) *
          ((∑ i, singularValue i ^ (-p)) /
            (Fintype.card I : Real)) := rfl

/-- Finite-family bound for the related low clipping correction. -/
theorem empiricalLowerLogCorrection_le_scaled_negativeMoment
    {I : Type*} [Fintype I]
    {singularValue : I -> Real} {a p : Real}
    (hs : forall i, 0 < singularValue i) (ha : 0 < a) (hp : 0 < p) :
    empiricalLowerLogCorrection a singularValue <=
      (a ^ p / p) * normalizedNegativeMoment p singularValue := by
  unfold empiricalLowerLogCorrection normalizedNegativeMoment empiricalAverage
  calc
    (∑ i, lowerLogCorrection a (singularValue i)) /
        (Fintype.card I : Real)
        <= (∑ i, (a ^ p / p) * singularValue i ^ (-p)) /
          (Fintype.card I : Real) := by
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            apply Finset.sum_le_sum
            intro i hi
            exact lowerLogCorrection_le_scaled_negativePower ha (hs i) hp
    _ = (a ^ p / p) *
        ((∑ i, singularValue i ^ (-p)) /
          (Fintype.card I : Real)) := by
            rw [← Finset.mul_sum]
            ring

/-- A positive real power of a deterministic sequence tending to zero also
tends to zero. -/
theorem rpow_div_tendsto_zero
    {a : Nat -> Real} {q : Real} (ha : Tendsto a atTop (nhds 0))
    (hq : 0 < q) :
    Tendsto (fun n => a n ^ q / q) atTop (nhds 0) := by
  have hpow := ha.rpow_const (Or.inr hq.le)
  have hpowZero : Tendsto (fun n => a n ^ q) atTop (nhds 0) := by
    simpa [Real.zero_rpow (ne_of_gt hq)] using hpow
  simpa using hpowZero.div_const q

/-- The exact deterministic scale in (3.14) vanishes when `aₙ → 0`. -/
theorem two_div_mul_rpow_half_tendsto_zero
    {a : Nat -> Real} {p : Real} (ha : Tendsto a atTop (nhds 0))
    (hp : 0 < p) :
    Tendsto (fun n => (2 / p) * a n ^ (p / 2)) atTop (nhds 0) := by
  have hpow := ha.rpow_const (Or.inr (half_pos hp).le)
  have hpowZero :
      Tendsto (fun n => a n ^ (p / 2)) atTop (nhds 0) := by
    simpa [Real.zero_rpow (ne_of_gt (half_pos hp))] using hpow
  simpa using tendsto_const_nhds.mul hpowZero

/-- Tightness times the deterministic scale in (3.14) is `o_P(1)`.

This is the complete probability-splicing step after the BC12 input. -/
theorem bc12NegativeMoment_scaled_convergesInProbability_zero
    {Omega : Type*} [MeasurableSpace Omega]
    {I : Nat -> Type*} [forall n, Fintype (I n)]
    {mu : Measure Omega} {p : Real}
    {singularValue : forall n, Omega -> I n -> Real}
    {a : Nat -> Real}
    (hp : 0 < p) (ha : Tendsto a atTop (nhds 0))
    (hBC12 : BC12GinibreNegativeMomentTightness mu p singularValue) :
    ConvergesInProbability mu
      (fun n omega => ((2 / p) * a n ^ (p / 2)) *
        normalizedNegativeMoment p (singularValue n omega)) 0 := by
  exact boundedInProbability_mul_tendsto_zero hBC12
    (two_div_mul_rpow_half_tendsto_zero ha hp)

/-- **Formula (3.14), conditional only on the named BC12 interface.**

Assume the singular values are positive, `0 < aₙ ≤ 1`, `aₙ → 0`, and the
BC12 normalized negative moment is bounded in probability.  Then

`(#Iₙ)⁻¹ ∑_{sᵢ≤aₙ} |log sᵢ| → 0`

in probability.  All reasoning after the BC12 premise is verified here. -/
theorem ginibreSmallLogMass_convergesInProbability_zero
    {Omega : Type*} [MeasurableSpace Omega]
    {I : Nat -> Type*} [forall n, Fintype (I n)]
    [forall n, Nonempty (I n)]
    {mu : Measure Omega} {p : Real}
    {singularValue : forall n, Omega -> I n -> Real}
    {a : Nat -> Real}
    (hp : 0 < p) (ha : forall n, 0 < a n)
    (ha1 : forall n, a n <= 1)
    (haZero : Tendsto a atTop (nhds 0))
    (hs : forall n omega i, 0 < singularValue n omega i)
    (hBC12 : BC12GinibreNegativeMomentTightness mu p singularValue) :
    ConvergesInProbability mu
      (fun n omega =>
        normalizedSmallLogMass (singularValue n omega) (a n)) 0 := by
  have hscaled := bc12NegativeMoment_scaled_convergesInProbability_zero
    hp haZero hBC12
  apply convergesInProbability_zero_of_norm_le hscaled
  intro n omega
  have hmassNonneg := normalizedSmallLogMass_nonneg
    (singularValue n omega) (a n)
  have hmomentNonneg := normalizedNegativeMoment_nonneg
    (p := p) (s := singularValue n omega) fun i => (hs n omega i).le
  have hscaleNonneg : 0 <= (2 / p) * a n ^ (p / 2) :=
    mul_nonneg (div_nonneg (by norm_num) hp.le)
      (Real.rpow_nonneg (ha n).le (p / 2))
  have hproductNonneg :
      0 <= ((2 / p) * a n ^ (p / 2)) *
        normalizedNegativeMoment p (singularValue n omega) :=
    mul_nonneg hscaleNonneg hmomentNonneg
  change |normalizedSmallLogMass (singularValue n omega) (a n)| <=
    |((2 / p) * a n ^ (p / 2)) *
      normalizedNegativeMoment p (singularValue n omega)|
  rw [abs_of_nonneg hmassNonneg, abs_of_nonneg hproductNonneg]
  exact normalizedSmallLogMass_le_scaled_negativeMoment
    (fun i => hs n omega i) (ha n) (ha1 n) hp

/-- The analogous clipping-correction consequence of the same BC12 input. -/
theorem ginibreLowerLogCorrection_convergesInProbability_zero
    {Omega : Type*} [MeasurableSpace Omega]
    {I : Nat -> Type*} [forall n, Fintype (I n)]
    {mu : Measure Omega} {p : Real}
    {singularValue : forall n, Omega -> I n -> Real}
    {a : Nat -> Real}
    (hp : 0 < p) (ha : forall n, 0 < a n)
    (haZero : Tendsto a atTop (nhds 0))
    (hs : forall n omega i, 0 < singularValue n omega i)
    (hBC12 : BC12GinibreNegativeMomentTightness mu p singularValue) :
    ConvergesInProbability mu
      (fun n omega =>
        empiricalLowerLogCorrection (a n) (singularValue n omega)) 0 := by
  have hscale : Tendsto (fun n => a n ^ p / p) atTop (nhds 0) :=
    rpow_div_tendsto_zero haZero hp
  have hscaled : ConvergesInProbability mu
      (fun n omega => (a n ^ p / p) *
        normalizedNegativeMoment p (singularValue n omega)) 0 :=
    boundedInProbability_mul_tendsto_zero hBC12 hscale
  apply convergesInProbability_zero_of_norm_le hscaled
  intro n omega
  have hcorrNonneg :
      0 <= empiricalLowerLogCorrection (a n) (singularValue n omega) := by
    unfold empiricalLowerLogCorrection empiricalAverage
    exact div_nonneg
      (Finset.sum_nonneg fun i _ =>
        lowerLogCorrection_nonneg (ha n) (hs n omega i))
      (Nat.cast_nonneg _)
  have hmomentNonneg := normalizedNegativeMoment_nonneg
    (p := p) (s := singularValue n omega) fun i => (hs n omega i).le
  have hscaleNonneg : 0 <= a n ^ p / p :=
    div_nonneg (Real.rpow_nonneg (ha n).le p) hp.le
  have hproductNonneg :
      0 <= (a n ^ p / p) *
        normalizedNegativeMoment p (singularValue n omega) :=
    mul_nonneg hscaleNonneg hmomentNonneg
  change |empiricalLowerLogCorrection (a n) (singularValue n omega)| <=
    |(a n ^ p / p) *
      normalizedNegativeMoment p (singularValue n omega)|
  rw [abs_of_nonneg hcorrNonneg, abs_of_nonneg hproductNonneg]
  exact empiricalLowerLogCorrection_le_scaled_negativeMoment
    (fun i => hs n omega i) (ha n) hp

end ShortRingAnchor
