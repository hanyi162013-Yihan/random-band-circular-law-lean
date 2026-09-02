import ShortRingAnchor.AEInputTransfer
import ShortRingAnchor.LeastSingularValueAdapter
import ShortRingAnchor.TruncationAssembly

/-!
# Transfer across events whose failure probability vanishes

For discrete atom laws, a shifted random matrix need not be nonsingular
almost surely at each fixed dimension.  Proposition 3.6 only needs the
weaker and source-natural fact that singular samples have probability
`o(1)`.  On the short-ring side this follows directly from the good event in
Theorem 3.1: a positive lower bound for the least singular value forces the
determinant to be nonzero.

This file proves the probability-theoretic replacement for the earlier
almost-everywhere transports.  It contains no random-matrix input.
-/

open Filter Set
open scoped ENNReal Topology BigOperators

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

/-- A sequence of shifted random matrices is nonsingular with probability
tending to one.  This is the exact condition needed by convergence in
probability; it is strictly weaker than almost-sure nonsingularity at every
fixed dimension. -/
def ShiftedNonsingularInProbability
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} (mu : Measure Omega)
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) Complex)
    (z : Complex) : Prop :=
  Tendsto (fun n => mu (shiftedNonsingularSet A z n)ᶜ)
    atTop (nhds 0)

/-- Per-dimension almost-sure nonsingularity implies the weaker asymptotic
condition used by the main Proposition 3.6 theorem. -/
theorem shiftedNonsingularInProbability_of_ae
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) Complex)
    (z : Complex)
    (hdet : forall n, ∀ᵐ sample ∂mu,
      (A n sample - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) Complex)).det ≠ 0) :
    ShiftedNonsingularInProbability mu A z := by
  have heq : (fun n => mu (shiftedNonsingularSet A z n)ᶜ) =
      fun _ => 0 := by
    funext n
    exact (ae_iff.mp (hdet n))
  rw [ShiftedNonsingularInProbability, heq]
  exact tendsto_const_nhds

/-! ## Generic high-probability agreement lemmas -/

/-- Convergence in probability is unchanged when two sequences agree on
events whose complements have probability tending to zero. -/
theorem ConvergesInProbability.congr_on_good
    {Omega E : Type*} [MeasurableSpace Omega]
    [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X Y : Nat -> Omega -> E} {x : E}
    {good : Nat -> Set Omega}
    (hX : ConvergesInProbability mu X x)
    (hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0))
    (heq : forall n omega, omega ∈ good n -> Y n omega = X n omega) :
    ConvergesInProbability mu Y x := by
  rw [convergesInProbability_iff_norm] at hX ⊢
  intro epsilon hepsilon
  have hsum : Tendsto
      (fun n =>
        mu {omega | epsilon <= ‖X n omega - x‖} + mu (good n)ᶜ)
      atTop (nhds 0) := by
    simpa only [zero_add] using (hX epsilon hepsilon).add hbad
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hsum (fun _ => zero_le) ?_
  intro n
  calc
    mu {omega | epsilon <= ‖Y n omega - x‖} <=
        mu ({omega | epsilon <= ‖X n omega - x‖} ∪ (good n)ᶜ) := by
      apply measure_mono
      intro omega homega
      by_cases hgood : omega ∈ good n
      · left
        change epsilon <= ‖Y n omega - x‖ at homega
        change epsilon <= ‖X n omega - x‖
        rw [heq n omega hgood] at homega
        exact homega
      · right
        exact hgood
    _ <= mu {omega | epsilon <= ‖X n omega - x‖} + mu (good n)ᶜ :=
      measure_union_le _ _

/-- `O_P(rate)` is unchanged when two sequences agree outside an `o(1)`
exceptional event. -/
theorem IsBigOInProbability.congr_on_good
    {Omega E : Type*} [MeasurableSpace Omega]
    [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X Y : Nat -> Omega -> E}
    {rate : Nat -> Real} {good : Nat -> Set Omega}
    (hX : IsBigOInProbability mu X rate)
    (hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0))
    (heq : forall n omega, omega ∈ good n -> Y n omega = X n omega) :
    IsBigOInProbability mu Y rate := by
  intro delta hdelta
  have hhalf : 0 < delta / 2 :=
    ENNReal.div_pos hdelta.ne' (by norm_num)
  obtain ⟨C, hC, htail⟩ := hX (delta / 2) hhalf
  have hbadHalf : ∀ᶠ n in atTop, mu (good n)ᶜ < delta / 2 :=
    hbad.eventually (Iio_mem_nhds hhalf)
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail, hbadHalf] with n hnTail hnBad
  calc
    mu {omega | C * |rate n| < ‖Y n omega‖} <=
        mu ({omega | C * |rate n| < ‖X n omega‖} ∪ (good n)ᶜ) := by
      apply measure_mono
      intro omega homega
      by_cases hgood : omega ∈ good n
      · left
        change C * |rate n| < ‖Y n omega‖ at homega
        change C * |rate n| < ‖X n omega‖
        rw [heq n omega hgood] at homega
        exact homega
      · right
        exact hgood
    _ <= mu {omega | C * |rate n| < ‖X n omega‖} + mu (good n)ᶜ :=
      measure_union_le _ _
    _ < delta / 2 + delta / 2 := ENNReal.add_lt_add hnTail hnBad
    _ = delta := ENNReal.add_halves delta

/-- Tightness is unchanged when two sequences agree outside an `o(1)`
exceptional event. -/
theorem BoundedInProbability.congr_on_good
    {Omega E : Type*} [MeasurableSpace Omega]
    [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X Y : Nat -> Omega -> E}
    {good : Nat -> Set Omega}
    (hX : BoundedInProbability mu X)
    (hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0))
    (heq : forall n omega, omega ∈ good n -> Y n omega = X n omega) :
    BoundedInProbability mu Y := by
  rw [boundedInProbability_iff_isBigO_one] at hX ⊢
  exact hX.congr_on_good hbad heq

/-- The iterated upper-edge estimate used in Proposition 3.6 is likewise
stable under replacing both finite families on an `o(1)` exceptional event.
The event is counted twice (once for each tail), which is why the proof uses
quarters of the requested error budget. -/
theorem UpperCorrectionsUniformlyNegligible.congr_on_good
    {Omega : Type*} [MeasurableSpace Omega]
    {I J : Nat -> Type*}
    [forall n, Fintype (I n)] [forall n, Fintype (J n)]
    {mu : Measure Omega}
    {h h' : forall n, Omega -> I n -> Real}
    {g g' : forall n, Omega -> J n -> Real}
    {R : Nat -> Real} {good : Nat -> Set Omega}
    (hUpper : UpperCorrectionsUniformlyNegligible mu h g R)
    (hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0))
    (hheq : forall n omega, omega ∈ good n -> h' n omega = h n omega)
    (hgeq : forall n omega, omega ∈ good n -> g' n omega = g n omega) :
    UpperCorrectionsUniformlyNegligible mu h' g' R := by
  intro epsilon hepsilon delta hdelta
  have hhalf : 0 < delta / 2 :=
    ENNReal.div_pos hdelta.ne' (by norm_num)
  have hquarter : 0 < delta / 2 / 2 :=
    ENNReal.div_pos hhalf.ne' (by norm_num)
  obtain ⟨r, htails⟩ := hUpper epsilon hepsilon (delta / 2) hhalf
  have hbadQuarter : ∀ᶠ n in atTop, mu (good n)ᶜ < delta / 2 / 2 :=
    hbad.eventually (Iio_mem_nhds hquarter)
  refine ⟨r, ?_⟩
  filter_upwards [htails, hbadQuarter] with n hnTails hnBad
  have hHle :
      mu {omega | epsilon / 2 <=
          empiricalUpperLogCorrection (R r) (h' n omega)} <=
        mu {omega | epsilon / 2 <=
          empiricalUpperLogCorrection (R r) (h n omega)} +
          mu (good n)ᶜ := by
    calc
      mu {omega | epsilon / 2 <=
          empiricalUpperLogCorrection (R r) (h' n omega)} <=
          mu ({omega | epsilon / 2 <=
              empiricalUpperLogCorrection (R r) (h n omega)} ∪
            (good n)ᶜ) := by
        apply measure_mono
        intro sample hsample
        by_cases hgood : sample ∈ good n
        · left
          change epsilon / 2 <=
            empiricalUpperLogCorrection (R r) (h' n sample) at hsample
          change epsilon / 2 <=
            empiricalUpperLogCorrection (R r) (h n sample)
          rw [hheq n sample hgood] at hsample
          exact hsample
        · right
          exact hgood
      _ <= _ := measure_union_le _ _
  have hGle :
      mu {omega | epsilon / 2 <=
          empiricalUpperLogCorrection (R r) (g' n omega)} <=
        mu {omega | epsilon / 2 <=
          empiricalUpperLogCorrection (R r) (g n omega)} +
          mu (good n)ᶜ := by
    calc
      mu {omega | epsilon / 2 <=
          empiricalUpperLogCorrection (R r) (g' n omega)} <=
          mu ({omega | epsilon / 2 <=
              empiricalUpperLogCorrection (R r) (g n omega)} ∪
            (good n)ᶜ) := by
        apply measure_mono
        intro sample hsample
        by_cases hgood : sample ∈ good n
        · left
          change epsilon / 2 <=
            empiricalUpperLogCorrection (R r) (g' n sample) at hsample
          change epsilon / 2 <=
            empiricalUpperLogCorrection (R r) (g n sample)
          rw [hgeq n sample hgood] at hsample
          exact hsample
        · right
          exact hgood
      _ <= _ := measure_union_le _ _
  calc
    mu {omega | epsilon / 2 <=
          empiricalUpperLogCorrection (R r) (h' n omega)} +
        mu {omega | epsilon / 2 <=
          empiricalUpperLogCorrection (R r) (g' n omega)} <=
      (mu {omega | epsilon / 2 <=
          empiricalUpperLogCorrection (R r) (h n omega)} +
        mu (good n)ᶜ) +
      (mu {omega | epsilon / 2 <=
          empiricalUpperLogCorrection (R r) (g n omega)} +
        mu (good n)ᶜ) := add_le_add hHle hGle
    _ =
      (mu {omega | epsilon / 2 <=
          empiricalUpperLogCorrection (R r) (h n omega)} +
        mu {omega | epsilon / 2 <=
          empiricalUpperLogCorrection (R r) (g n omega)}) +
      (mu (good n)ᶜ + mu (good n)ᶜ) := by ac_rfl
    _ < delta / 2 + (delta / 2 / 2 + delta / 2 / 2) :=
      ENNReal.add_lt_add hnTails (ENNReal.add_lt_add hnBad hnBad)
    _ = delta / 2 + delta / 2 := by
      rw [ENNReal.add_halves (delta / 2)]
    _ = delta := ENNReal.add_halves delta

/-! ## The Theorem 3.1 good event is nonsingular -/

/-- A positive lower bound for every shifted singular value forces the
shifted determinant to be nonzero. -/
theorem shifted_det_ne_zero_of_singularValue_lower
    {n : Nat} [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) Complex) (z : Complex) (c : Real)
    (hc : 0 < c)
    (hlower : forall i : Fin n,
      c <= shiftedSingularValueFamily A z i) :
    (A - z • (1 : Matrix (Fin n) (Fin n) Complex)).det ≠ 0 := by
  have hprod :
      (∏ j ∈ Finset.range n,
        matrixSingularValue
          (A - z • (1 : Matrix (Fin n) (Fin n) Complex)) j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hjpos : 0 < matrixSingularValue
        (A - z • (1 : Matrix (Fin n) (Fin n) Complex)) j := by
      exact hc.trans_le (hlower ⟨j, Finset.mem_range.mp hj⟩)
    exact ne_of_gt hjpos
  rw [← norm_det_eq_prod_matrixSingularValue] at hprod
  exact fun hdet => hprod (by simp [hdet])

/-- The all-singular-values form of the Theorem 3.1 input forces
nonsingularity on its good event. -/
theorem Theorem31LeastSingularValueInput.det_ne_zero_on_good
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} [forall n, Nonempty (Fin (M n))]
    {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) Complex)
    (z : Complex) (L : Nat -> Real) (good : Nat -> Set Omega)
    (hInput : Theorem31LeastSingularValueInput mu
      (shiftedSingularValueProcess A z) L good) :
    forall n omega, omega ∈ good n ->
      (A n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) Complex)).det ≠ 0 := by
  intro n omega homega
  exact shifted_det_ne_zero_of_singularValue_lower
    (A n omega) z (Real.exp (-(L n))) (Real.exp_pos _)
    (hInput.lower n omega homega)

/-- The minimum-singular-value conclusion of Theorem 3.1 implies
nonsingularity on the very same good event. -/
theorem Theorem31MinimumSingularValueInput.det_ne_zero_on_good
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} [forall n, Nonempty (Fin (M n))]
    (hM : forall n, 0 < M n) {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) Complex)
    (z : Complex) (L : Nat -> Real) (good : Nat -> Set Omega)
    (hInput : Theorem31MinimumSingularValueInput hM mu A z L good) :
    forall n omega, omega ∈ good n ->
      (A n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) Complex)).det ≠ 0 := by
  have hAll := theorem31LeastSingularValueInput_of_minimum
    hM A z L good hInput
  exact hAll.det_ne_zero_on_good A z L good

/-- Consequently, the probability of a singular shifted short-ring matrix
is `o(1)`; no per-dimension almost-sure nonsingularity premise is needed. -/
theorem Theorem31MinimumSingularValueInput.singular_probability_tendsto_zero
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} [forall n, Nonempty (Fin (M n))]
    (hM : forall n, 0 < M n) {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) Complex)
    (z : Complex) (L : Nat -> Real) (good : Nat -> Set Omega)
    (hInput : Theorem31MinimumSingularValueInput hM mu A z L good) :
    Tendsto (fun n =>
      mu {omega |
        (A n omega - z •
          (1 : Matrix (Fin (M n)) (Fin (M n)) Complex)).det = 0})
      atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hInput.badProbability (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  intro omega hsingular hgood
  exact (hInput.det_ne_zero_on_good hM A z L good n omega hgood) hsingular

/-- On a Theorem 3.1 good event, the everywhere-positive representative is
definitionally the genuine shifted singular-value family. -/
theorem positiveShiftedSingularValueProcess_eq_on_theorem31_good
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} [forall n, Nonempty (Fin (M n))]
    (hM : forall n, 0 < M n) {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) Complex)
    (z : Complex) (L : Nat -> Real) (good : Nat -> Set Omega)
    (hInput : Theorem31MinimumSingularValueInput hM mu A z L good) :
    forall n omega, omega ∈ good n ->
      positiveShiftedSingularValueProcess A z n omega =
        shiftedSingularValueProcess A z n omega := by
  intro n omega homega
  have hdet := hInput.det_ne_zero_on_good hM A z L good n omega homega
  funext i
  simp [positiveShiftedSingularValueProcess, shiftedSingularValueProcess, hdet]

end ShortRingAnchor
