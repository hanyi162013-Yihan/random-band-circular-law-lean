import ShortRingAnchor.BulkClippedLog
import ShortRingAnchor.ProbabilityModes

/-!
# From the local CDF comparison to formula (3.12)

Lemma 3.5 is a random-matrix input: for each fixed upper cutoff `R` it
supplies an `O_P(M^{-zeta})` bound for the CDF distance on `[0,R^2]` of the
two empirical laws of squared singular values.  Everything after that input
in (3.11)--(3.12) is proved here.
-/

open Filter
open scoped ENNReal Topology

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

variable {Omega E : Type*} [MeasurableSpace Omega]

/-- Pointwise norm domination preserves an `O_P(rate)` estimate. -/
theorem isBigOInProbability_of_norm_le
    [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X Y : Nat -> Omega -> E} {rate : Nat -> Real}
    (hX : IsBigOInProbability mu X rate)
    (hYX : forall n omega, ‖Y n omega‖ <= ‖X n omega‖) :
    IsBigOInProbability mu Y rate := by
  intro delta hdelta
  obtain ⟨C, hC, htail⟩ := hX delta hdelta
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail] with n hn
  exact lt_of_le_of_lt (measure_mono (fun _ homega =>
    homega.trans_le (hYX n _))) hn

/-- Multiplication by an arbitrary deterministic scalar sequence transports
`O_P(rate_n)` to `O_P(a_n rate_n)`.  Vanishing scalar values are handled
directly, so no eventual nonzero premise is needed. -/
theorem IsBigOInProbability.deterministic_mul
    {mu : Measure Omega} {X : Nat -> Omega -> Real} {rate a : Nat -> Real}
    (hX : IsBigOInProbability mu X rate) :
    IsBigOInProbability mu
      (fun n omega => a n * X n omega)
      (fun n => a n * rate n) := by
  intro delta hdelta
  obtain ⟨C, hC, htail⟩ := hX delta hdelta
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail] with n hn
  refine lt_of_le_of_lt (measure_mono ?_) hn
  intro omega homega
  simp only [Real.norm_eq_abs, abs_mul] at homega ⊢
  by_cases ha : |a n| = 0
  · simp [ha] at homega
  · have haPos : 0 < |a n| := (abs_nonneg _).lt_of_ne' ha
    have hmul : |a n| * (C * |rate n|) < |a n| * |X n omega| := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using homega
    exact lt_of_mul_lt_mul_left hmul haPos.le

/-- **The named Lemma 3.5 input used in Proposition 3.6.**

For fixed `R`, formula (3.11) says that the empirical CDF distance is
`O_P(M^{-zeta})`.  This definition records precisely that conclusion and is
not an axiom or a claim that Lemma 3.5 has been reproved in this project. -/
def LocalBulkComparisonInput
    {I J : Nat -> Type*} [forall n, Fintype (I n)]
    [forall n, Fintype (J n)]
    (mu : Measure Omega)
    (x : forall n, Omega -> I n -> Real)
    (y : forall n, Omega -> J n -> Real)
    (R : Real)
    (rate : Nat -> Real) : Prop :=
  IsBigOInProbability mu
    (fun n omega =>
      empiricalCdfDistanceOn 0 (R ^ 2) (x n omega) (y n omega)) rate

/-- **Formula (3.11) implies formula (3.12).**

The only random-matrix premise is `hcomparison`, the named Lemma 3.5
interface.  The layer-cake bound is proved in `BulkClippedLog.lean`; the
remaining deterministic scale is
`rate_n * (log R - log a_n)`.  If this tends to zero (as it does when
`rate_n=M^{-zeta}` and `a_n` is polynomially small), the difference of the
two clipped logarithmic averages is `o_P(1)`. -/
theorem bulkClippedLog_convergesInProbability_zero
    {I J : Nat -> Type*}
    [forall n, Fintype (I n)] [forall n, Nonempty (I n)]
    [forall n, Fintype (J n)] [forall n, Nonempty (J n)]
    {mu : Measure Omega}
    {x : forall n, Omega -> I n -> Real}
    {y : forall n, Omega -> J n -> Real}
    {a rate : Nat -> Real} {R : Real}
    (ha : forall n, 0 < a n) (haR : forall n, a n <= R)
    (hcomparison : LocalBulkComparisonInput mu x y R rate)
    (hscale : Tendsto
      (fun n => rate n * (Real.log R - Real.log (a n)))
      atTop (nhds 0)) :
    ConvergesInProbability mu
      (fun n omega =>
        empiricalClippedLog (a n) R (x n omega) -
          empiricalClippedLog (a n) R (y n omega)) 0 := by
  let width : Nat -> Real := fun n => Real.log R - Real.log (a n)
  have hwidth : forall n, 0 <= width n := by
    intro n
    dsimp only [width]
    exact sub_nonneg.mpr (Real.log_le_log (ha n) (haR n))
  have hscaled : IsBigOInProbability mu
      (fun n omega => width n *
        empiricalCdfDistanceOn 0 (R ^ 2) (x n omega) (y n omega))
      (fun n => width n * rate n) :=
    hcomparison.deterministic_mul
  have hbulk : IsBigOInProbability mu
      (fun n omega =>
        empiricalClippedLog (a n) R (x n omega) -
          empiricalClippedLog (a n) R (y n omega))
      (fun n => width n * rate n) := by
    apply isBigOInProbability_of_norm_le hscaled
    intro n omega
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hwidth n)
        (empiricalCdfDistanceOn_nonneg (sq_nonneg R)
          (x n omega) (y n omega)))]
    calc
      |empiricalClippedLog (a n) R (x n omega) -
          empiricalClippedLog (a n) R (y n omega)| <=
          empiricalCdfDistanceOn 0 (R ^ 2)
            (x n omega) (y n omega) * width n :=
        abs_empiricalClippedLog_sub_le_cdfDistanceOn_zero_sq
          (ha n) (haR n) (x n omega) (y n omega)
      _ = width n * empiricalCdfDistanceOn 0 (R ^ 2)
          (x n omega) (y n omega) := by ring
  apply isBigOInProbability_tendsto_zero hbulk
  simpa [width, mul_comm] using hscale

end ShortRingAnchor
