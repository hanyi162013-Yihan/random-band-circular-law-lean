import ShortRingAnchor.ExternalInputs
import ShortRingAnchor.SingularValues

/-!
# From the least singular value to all singular values

Theorem 3.1 is used in Proposition 3.6 only through a lower bound on the
least singular value of the shifted matrix.  The generic interface
`Theorem31LeastSingularValueInput` is phrased as a bound for every singular
value.  This file proves that passage internally, using mathlib's ordering of
singular values; consequently the external input need only mention the last
(and hence least) singular value.
-/

open Filter Set
open scoped ENNReal Topology

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The last index of a nonempty finite singular-value family. -/
def lastSingularValueIndex (n : Nat) (hn : 0 < n) : Fin n :=
  ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩

@[simp]
theorem lastSingularValueIndex_val (n : Nat) (hn : 0 < n) :
    (lastSingularValueIndex n hn : Nat) = n - 1 :=
  rfl

/-- Pointwise form of the deterministic step following Theorem 3.1: since
mathlib lists singular values in decreasing order, every shifted singular
value is at least the last one. -/
theorem shiftedSingularValueFamily_last_le
    {n : Nat} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (j : Fin n) :
    shiftedSingularValueFamily A z (lastSingularValueIndex n hn) <=
      shiftedSingularValueFamily A z j := by
  exact
    (A - z • (1 : Matrix (Fin n) (Fin n) ℂ)).toEuclideanLin
      |>.singularValues_antitone (Nat.le_sub_one_of_lt j.isLt)

/-- A lower bound for the least shifted singular value propagates to all
shifted singular values. -/
theorem shiftedSingularValueFamily_lower_of_last
    {n : Nat} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (c : Real)
    (hlast : c <=
      shiftedSingularValueFamily A z (lastSingularValueIndex n hn)) :
    forall j, c <= shiftedSingularValueFamily A z j := by
  intro j
  exact hlast.trans (shiftedSingularValueFamily_last_le hn A z j)

/-- The exact external least-singular-value input needed from Theorem 3.1.
It asks for the same exceptional-event estimate as the original interface,
but only one scalar lower bound per matrix.  This is a structure of
hypotheses, not an axiom or an asserted random-matrix theorem. -/
structure Theorem31MinimumSingularValueInput
    {M : Nat -> Nat} (hM : forall n, 0 < M n)
    (mu : Measure Omega)
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (L : Nat -> Real) (good : Nat -> Set Omega) : Prop where
  badProbability : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0)
  leastLower : forall n omega, omega ∈ good n ->
    Real.exp (-(L n)) <= shiftedSingularValueFamily (A n omega) z
      (lastSingularValueIndex (M n) (hM n))

/-- Adapter from the genuine least-singular-value statement of Theorem 3.1
to the all-indices interface consumed by the hard-edge argument. -/
theorem theorem31LeastSingularValueInput_of_minimum
    {M : Nat -> Nat} (hM : forall n, 0 < M n)
    {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (L : Nat -> Real) (good : Nat -> Set Omega)
    (hmin : Theorem31MinimumSingularValueInput hM mu A z L good) :
    Theorem31LeastSingularValueInput mu
      (shiftedSingularValueProcess A z) L good := by
  refine
    { badProbability := hmin.badProbability
      lower := ?_ }
  intro n omega homega i
  exact shiftedSingularValueFamily_lower_of_last
    (hM n) (A n omega) z (Real.exp (-(L n)))
    (hmin.leastLower n omega homega) i

end ShortRingAnchor
