import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Elementary probability modes for the short-ring anchor

The paper uses `o_P(1)`, `O_P(1)`, and `O_P(r_n)`.  This file records those
notions on one common probability space and proves the small amount of
probability calculus needed in Proposition 3.6.  No independence assumption
is used anywhere in this file.
-/

open Filter Set
open scoped ENNReal Topology BigOperators

namespace ShortRingAnchor

open MeasureTheory

variable {Omega E : Type*} [MeasurableSpace Omega]

/-- Convergence in probability, represented by mathlib's convergence in
measure on the underlying probability space. -/
def ConvergesInProbability [SeminormedAddCommGroup E]
    (mu : Measure Omega) (X : Nat -> Omega -> E) (x : E) : Prop :=
  TendstoInMeasure mu X atTop (fun _ => x)

/-- The threshold-event characterization of convergence in probability. -/
theorem convergesInProbability_iff_norm [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X : Nat -> Omega -> E} {x : E} :
    ConvergesInProbability mu X x <->
      forall epsilon : Real, 0 < epsilon ->
        Tendsto (fun n => mu {omega | epsilon <= ‖X n omega - x‖}) atTop (nhds 0) := by
  simp [ConvergesInProbability, MeasureTheory.tendstoInMeasure_iff_norm]

/-- A sequence is bounded in probability if one deterministic positive
cutoff controls its tails eventually, at every prescribed error level.  The
strict positivity of the cutoff is harmless and simplifies products with a
deterministic `o(1)` sequence. -/
def BoundedInProbability [SeminormedAddCommGroup E]
    (mu : Measure Omega) (X : Nat -> Omega -> E) : Prop :=
  forall delta : ENNReal, 0 < delta ->
    exists C : Real, 0 < C /\
      ∀ᶠ n in atTop, mu {omega | C < ‖X n omega‖} < delta

/-- `X_n = O_P(rate_n)`, stated without division by the rate.  This remains
meaningful even if finitely many values of `rate` vanish. -/
def IsBigOInProbability [SeminormedAddCommGroup E]
    (mu : Measure Omega) (X : Nat -> Omega -> E) (rate : Nat -> Real) : Prop :=
  forall delta : ENNReal, 0 < delta ->
    exists C : Real, 0 < C /\
      ∀ᶠ n in atTop,
        mu {omega | C * |rate n| < ‖X n omega‖} < delta

/-- Boundedness in probability is the rate-one instance of `O_P`. -/
theorem boundedInProbability_iff_isBigO_one [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X : Nat -> Omega -> E} :
    BoundedInProbability mu X <->
      IsBigOInProbability mu X (fun _ => 1) := by
  simp only [BoundedInProbability, IsBigOInProbability, abs_one, mul_one]

/-- A deterministic uniform bound implies boundedness in probability. -/
theorem boundedInProbability_of_uniform_bound [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X : Nat -> Omega -> E} {C : Real}
    (hC : forall n omega, ‖X n omega‖ <= C) :
    BoundedInProbability mu X := by
  intro delta hdelta
  refine ⟨max 1 (C + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  refine Filter.Eventually.of_forall fun n => ?_
  have hempty : {omega | max 1 (C + 1) < ‖X n omega‖} = (∅ : Set Omega) := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact not_lt_of_ge ((hC n omega).trans
      ((le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)))
  rw [hempty, measure_empty]
  exact hdelta

/-- Boundedness in probability is invariant under changing every random
variable on a null set.  This is the interface lemma used to pass from the
genuine singular values to an everywhere-positive representative. -/
theorem BoundedInProbability.congr_ae [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X Y : Nat -> Omega -> E}
    (hX : BoundedInProbability mu X)
    (hXY : forall n, X n =ᵐ[mu] Y n) :
    BoundedInProbability mu Y := by
  intro delta hdelta
  obtain ⟨C, hC, htail⟩ := hX delta hdelta
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail] with n hn
  rw [measure_congr]
  · exact hn
  · filter_upwards [hXY n] with omega homega
    apply propext
    change (C < ‖Y n omega‖ ↔ C < ‖X n omega‖)
    rw [homega]

/-- `O_P(rate)` is invariant under changing every random variable on a null
set. -/
theorem IsBigOInProbability.congr_ae [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X Y : Nat -> Omega -> E} {rate : Nat -> Real}
    (hX : IsBigOInProbability mu X rate)
    (hXY : forall n, X n =ᵐ[mu] Y n) :
    IsBigOInProbability mu Y rate := by
  intro delta hdelta
  obtain ⟨C, hC, htail⟩ := hX delta hdelta
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail] with n hn
  rw [measure_congr]
  · exact hn
  · filter_upwards [hXY n] with omega homega
    apply propext
    change (C * |rate n| < ‖Y n omega‖ ↔
      C * |rate n| < ‖X n omega‖)
    rw [homega]

/-- Multiplying an `O_P(rate_n)` observable by a rate tending to zero gives
convergence in probability to zero. -/
theorem isBigOInProbability_tendsto_zero [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X : Nat -> Omega -> E} {rate : Nat -> Real}
    (hX : IsBigOInProbability mu X rate)
    (hrate : Tendsto rate atTop (nhds 0)) :
    ConvergesInProbability mu X 0 := by
  rw [convergesInProbability_iff_norm]
  intro epsilon hepsilon
  rw [ENNReal.tendsto_nhds_zero]
  intro delta hdelta
  obtain ⟨C, hC, htail⟩ := hX delta hdelta
  have hsmall : ∀ᶠ n in atTop, C * |rate n| < epsilon := by
    have ht : Tendsto (fun n => C * |rate n|) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hrate.abs
    exact ht.eventually (Iio_mem_nhds hepsilon)
  filter_upwards [htail, hsmall] with n hn hCn
  calc
    mu {omega | epsilon <= ‖X n omega - 0‖}
        <= mu {omega | C * |rate n| < ‖X n omega‖} := by
          apply measure_mono
          intro omega homega
          simp only [sub_zero] at homega
          exact hCn.trans_le homega
    _ <= delta := hn.le

/-- A tight random observable times a deterministic scalar tending to zero
is `o_P(1)`. -/
theorem boundedInProbability_mul_tendsto_zero
    {mu : Measure Omega} {X : Nat -> Omega -> Real} {a : Nat -> Real}
    (hX : BoundedInProbability mu X)
    (ha : Tendsto a atTop (nhds 0)) :
    ConvergesInProbability mu (fun n omega => a n * X n omega) 0 := by
  apply isBigOInProbability_tendsto_zero (rate := a) _ ha
  intro delta hdelta
  obtain ⟨C, hC, htail⟩ := hX delta hdelta
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail] with n hn
  refine lt_of_le_of_lt (measure_mono ?_) hn
  intro omega homega
  simp only [Real.norm_eq_abs, abs_mul] at homega ⊢
  by_contra hnot
  have hle : |X n omega| <= C := le_of_not_gt hnot
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left hle (abs_nonneg (a n))))
    (by simpa [mul_comm] using homega)

/-- Pointwise norm domination preserves convergence in probability to zero. -/
theorem convergesInProbability_zero_of_norm_le
    [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X Y : Nat -> Omega -> E}
    (hX : ConvergesInProbability mu X 0)
    (hXY : forall n omega, ‖Y n omega‖ <= ‖X n omega‖) :
    ConvergesInProbability mu Y 0 := by
  rw [convergesInProbability_iff_norm] at hX ⊢
  intro epsilon hepsilon
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hX epsilon hepsilon) (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  intro omega homega
  simp only [sub_zero] at homega ⊢
  exact homega.trans (hXY n omega)

/-- The sum of two observables converging in probability to zero again
converges in probability to zero. -/
theorem ConvergesInProbability.add_zero
    [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X Y : Nat -> Omega -> E}
    (hX : ConvergesInProbability mu X 0)
    (hY : ConvergesInProbability mu Y 0) :
    ConvergesInProbability mu (fun n omega => X n omega + Y n omega) 0 := by
  rw [convergesInProbability_iff_norm] at hX hY ⊢
  intro epsilon hepsilon
  have hepsilon2 : 0 < epsilon / 2 := half_pos hepsilon
  have ht : Tendsto (fun n =>
      mu {omega | epsilon / 2 <= ‖X n omega - 0‖} +
        mu {omega | epsilon / 2 <= ‖Y n omega - 0‖}) atTop (nhds 0) := by
    simpa using (hX (epsilon / 2) hepsilon2).add (hY (epsilon / 2) hepsilon2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) ?_
  intro n
  calc
    mu {omega | epsilon <= ‖X n omega + Y n omega - 0‖}
        <= mu ({omega | epsilon / 2 <= ‖X n omega - 0‖} ∪
          {omega | epsilon / 2 <= ‖Y n omega - 0‖}) := by
            apply measure_mono
            intro omega homega
            simp only [sub_zero, Set.mem_union, Set.mem_ofPred_eq] at homega ⊢
            by_cases hx : epsilon / 2 <= ‖X n omega‖
            · exact Or.inl hx
            by_cases hy : epsilon / 2 <= ‖Y n omega‖
            · exact Or.inr hy
            · have hsum := norm_add_le (X n omega) (Y n omega)
              have hxlt : ‖X n omega‖ < epsilon / 2 := lt_of_not_ge hx
              have hylt : ‖Y n omega‖ < epsilon / 2 := lt_of_not_ge hy
              linarith
    _ <= mu {omega | epsilon / 2 <= ‖X n omega - 0‖} +
        mu {omega | epsilon / 2 <= ‖Y n omega - 0‖} := measure_union_le _ _

/-- Centering by the deterministic limit turns convergence in probability
into convergence to zero. -/
theorem convergesInProbability_sub_const_iff
    [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X : Nat -> Omega -> E} {x : E} :
    ConvergesInProbability mu X x <->
      ConvergesInProbability mu (fun n omega => X n omega - x) 0 := by
  rw [convergesInProbability_iff_norm, convergesInProbability_iff_norm]
  simp only [sub_zero]

/-- Addition preserves convergence in probability, with the expected sum of
the deterministic limits. -/
theorem ConvergesInProbability.add
    [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X Y : Nat -> Omega -> E} {x y : E}
    (hX : ConvergesInProbability mu X x)
    (hY : ConvergesInProbability mu Y y) :
    ConvergesInProbability mu (fun n omega => X n omega + Y n omega) (x + y) := by
  rw [convergesInProbability_sub_const_iff] at hX hY ⊢
  have hsum := hX.add_zero hY
  apply convergesInProbability_zero_of_norm_le hsum
  intro n omega
  rw [show X n omega + Y n omega - (x + y) =
      (X n omega - x) + (Y n omega - y) by abel]

/-- Negation preserves convergence in probability. -/
theorem ConvergesInProbability.neg
    [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X : Nat -> Omega -> E} {x : E}
    (hX : ConvergesInProbability mu X x) :
    ConvergesInProbability mu (fun n omega => -X n omega) (-x) := by
  rw [convergesInProbability_sub_const_iff] at hX ⊢
  apply convergesInProbability_zero_of_norm_le hX
  intro n omega
  rw [show -X n omega - -x = -(X n omega - x) by abel, norm_neg]

/-- Subtraction preserves convergence in probability. -/
theorem ConvergesInProbability.sub
    [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X Y : Nat -> Omega -> E} {x y : E}
    (hX : ConvergesInProbability mu X x)
    (hY : ConvergesInProbability mu Y y) :
    ConvergesInProbability mu (fun n omega => X n omega - Y n omega) (x - y) := by
  simpa only [sub_eq_add_neg] using hX.add hY.neg

/-- A deterministic constant sequence converges in probability to that
constant, on an arbitrary measure space. -/
theorem convergesInProbability_const
    [SeminormedAddCommGroup E]
    (mu : Measure Omega) (x : E) :
    ConvergesInProbability mu (fun _ _ => x) x := by
  rw [convergesInProbability_iff_norm]
  intro epsilon hepsilon
  simp [not_le_of_gt hepsilon]

/-- A high-probability deterministic error bound implies convergence in
probability.  This is the event-splicing step used after (3.10). -/
theorem convergesInProbability_of_good_bound
    {mu : Measure Omega} {X : Nat -> Omega -> Real}
    {good : Nat -> Set Omega} {rate : Nat -> Real}
    (hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0))
    (hrate : Tendsto rate atTop (nhds 0))
    (_hrate_nonneg : forall n, 0 <= rate n)
    (hbound : forall n omega, omega ∈ good n -> |X n omega| <= rate n) :
    ConvergesInProbability mu X 0 := by
  rw [convergesInProbability_iff_norm]
  intro epsilon hepsilon
  have hsmall : ∀ᶠ n in atTop, rate n < epsilon :=
    hrate.eventually (Iio_mem_nhds hepsilon)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hsmall] with n hn
  apply measure_mono
  intro omega homega
  simp only [sub_zero, Real.norm_eq_abs] at homega
  by_contra hgood
  have hle := hbound n omega (by simpa using hgood)
  exact (not_lt_of_ge homega) (hle.trans_lt hn)

/-- A finite sum of `o_P(1)` observables is `o_P(1)`.  This is the finite
good-event stitching used in the final proof of Proposition 3.6. -/
theorem convergesInProbability_finset_sum_zero
    {I : Type*} [DecidableEq I] [SeminormedAddCommGroup E]
    (s : Finset I) {mu : Measure Omega} (X : I -> Nat -> Omega -> E)
    (hX : ∀ i ∈ s, ConvergesInProbability mu (X i) 0) :
    ConvergesInProbability mu (fun n omega => ∑ i ∈ s, X i n omega) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [convergesInProbability_iff_norm]
      intro epsilon hepsilon
      simp [not_le_of_gt hepsilon]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hX i (Finset.mem_insert_self i s)).add_zero
        (ih (fun j hj => hX j (Finset.mem_insert_of_mem hj)))

/-- If the absolute value of a target is bounded by a finite sum of
nonnegative error observables and every error is `o_P(1)`, then the target is
`o_P(1)`. -/
theorem convergesInProbability_zero_of_abs_le_finset_sum
    {I : Type*} [DecidableEq I]
    (s : Finset I) {mu : Measure Omega}
    (X : I -> Nat -> Omega -> Real) (Y : Nat -> Omega -> Real)
    (hX : ∀ i ∈ s, ConvergesInProbability mu (X i) 0)
    (hbound : forall n omega, |Y n omega| <= ∑ i ∈ s, |X i n omega|) :
    ConvergesInProbability mu Y 0 := by
  classical
  have habs : ∀ i ∈ s,
      ConvergesInProbability mu (fun n omega => |X i n omega|) 0 := by
    intro i hi
    rw [convergesInProbability_iff_norm]
    intro epsilon hepsilon
    have hprob := (convergesInProbability_iff_norm.mp (hX i hi)) epsilon hepsilon
    simpa [Real.norm_eq_abs, abs_abs] using hprob
  have hsum := convergesInProbability_finset_sum_zero s
    (fun i n omega => |X i n omega|) habs
  apply convergesInProbability_zero_of_norm_le hsum
  intro n omega
  have hnonneg : 0 <= ∑ i ∈ s, |X i n omega| := by
    apply Finset.sum_nonneg
    intro i hi
    exact abs_nonneg _
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hbound n omega

end ShortRingAnchor
