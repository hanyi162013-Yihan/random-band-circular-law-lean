import BernoulliSection9.TerminalReverse
import BernoulliSection9.ValidMatchingCardinality

/-!
# Explicit terminal reverse-loss numerics

The sharp-support reverse bound has a completely determined finite factor.
Taking `log (max 1 factor)` packages it as a nonnegative capped-log loss;
no caller-supplied counting or comparison certificate remains.
-/

open scoped BigOperators

noncomputable section

namespace BernoulliSection9

open BernoulliLinearAlgebra
open MeasureTheory

namespace TerminalAssembly

/-- The exact finite factor in the valid-matching reverse estimate. -/
def terminalReverseFactor
    (w : Type*) [Fintype w] [DecidableEq w]
    (z : Complex) (M : Real) : Real :=
  (Fintype.card (ValidThreeBlockMatching w) : Real) *
    threeBlockTranslationFactor (w := w) z *
    (M + norm z) ^ Fintype.card (ThreeBlockIndex w)

/-- A canonical nonnegative loss dominating the exact reverse factor. -/
def terminalReverseLoss
    (w : Type*) [Fintype w] [DecidableEq w]
    (z : Complex) (M : Real) : Real :=
  Real.log (max 1 (terminalReverseFactor w z M))

theorem terminalReverseLoss_nonneg
    (w : Type*) [Fintype w] [DecidableEq w]
    (z : Complex) (M : Real) :
    0 <= terminalReverseLoss w z M := by
  exact Real.log_nonneg (le_max_left _ _)

theorem terminalReverseFactor_le_exp_loss
    (w : Type*) [Fintype w] [DecidableEq w]
    (z : Complex) (M : Real) :
    terminalReverseFactor w z M <= Real.exp (terminalReverseLoss w z M) := by
  have hpos : 0 < max 1 (terminalReverseFactor w z M) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [terminalReverseLoss, Real.exp_log hpos]
  exact le_max_right _ _

/-- Equation (7.22) with all finite counting data discharged internally. -/
theorem packetTerminal_reverse
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w] [LinearOrder w]
    {mu : Measure Omega}
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable w))
    (M : Real) (hshift : 1 <= M + norm z) :
    forall omega, omega ∈ coordinatewiseBoundedEvent X M ->
      Real.posLog
        (norm (packetTerminalValue Q z X omega) /
          packetTerminalCoefficientNorm Q z) <=
        terminalReverseLoss w z M := by
  apply packetTerminal_reverse_validMatching Q z X M
    (terminalReverseLoss w z M) hshift
    (terminalReverseLoss_nonneg w z M)
  exact terminalReverseFactor_le_exp_loss w z M

/-- The diagonal translation factor is exactly one copy of `1+norm z` per
physical packet diagonal coordinate. -/
theorem threeBlockTranslationFactor_eq_power
    {w : Type*} [Fintype w] [DecidableEq w] (z : Complex) :
    threeBlockTranslationFactor (w := w) z =
      (1 + norm z) ^ Fintype.card (ThreeBlockIndex w) := by
  simp [threeBlockTranslationFactor, threeBlockDiagonalShifts,
    translationFactor]

/-- The full three-block index has exactly `3W` coordinates. -/
theorem card_threeBlockIndex
    {w : Type*} [Fintype w] :
    Fintype.card (ThreeBlockIndex w) = 3 * Fintype.card w := by
  simp [ThreeBlockIndex, ThreeBlockOuter]
  omega

/-- A paper-scale upper bound for the exact factor.  Its three bases are a
quadratic polynomial in `3W`, the diagonal translation, and the bounded
coordinate size, each raised only to `3W`. -/
theorem terminalReverseFactor_le_indexPolynomial
    (w : Type*) [Fintype w] [DecidableEq w]
    (z : Complex) (M : Real) (hshift : 0 <= M + norm z) :
    terminalReverseFactor w z M <=
      ((Fintype.card (ThreeBlockIndex w) *
          Fintype.card (ThreeBlockIndex w) + 1 : Nat) : Real) ^
          Fintype.card (ThreeBlockIndex w) *
        (1 + norm z) ^ Fintype.card (ThreeBlockIndex w) *
        (M + norm z) ^ Fintype.card (ThreeBlockIndex w) := by
  have hcardNat := card_validThreeBlockMatching_le_indexPolynomial (w := w)
  have hcardReal :
      (Fintype.card (ValidThreeBlockMatching w) : Real) <=
        ((Fintype.card (ThreeBlockIndex w) *
            Fintype.card (ThreeBlockIndex w) + 1 : Nat) : Real) ^
          Fintype.card (ThreeBlockIndex w) := by
    exact_mod_cast hcardNat
  rw [terminalReverseFactor, threeBlockTranslationFactor_eq_power]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcardReal
      (by positivity))
    (pow_nonneg hshift _)

/-- One paper-scale base containing the matching count, spectral
translation, and bounded-coordinate factors. -/
def terminalReversePolynomialBase
    (w : Type*) [Fintype w] [DecidableEq w]
    (z : Complex) (M : Real) : Real :=
  max 1
    (((Fintype.card (ThreeBlockIndex w) *
        Fintype.card (ThreeBlockIndex w) + 1 : Nat) : Real) *
      (1 + norm z) * (M + norm z))

theorem terminalReversePolynomialBase_one_le
    (w : Type*) [Fintype w] [DecidableEq w]
    (z : Complex) (M : Real) :
    1 <= terminalReversePolynomialBase w z M :=
  le_max_left _ _

/-- The exact reverse loss is bounded by `3W` times the logarithm of a
single polynomial base.  This is the literal finite-dimensional form of
`O(W log W)`. -/
theorem terminalReverseLoss_le_card_mul_log_polynomialBase
    (w : Type*) [Fintype w] [DecidableEq w]
    (z : Complex) (M : Real) (hshift : 0 <= M + norm z) :
    terminalReverseLoss w z M <=
      (Fintype.card (ThreeBlockIndex w) : Real) *
        Real.log (terminalReversePolynomialBase w z M) := by
  let N := Fintype.card (ThreeBlockIndex w)
  let A : Real :=
    ((Fintype.card (ThreeBlockIndex w) *
        Fintype.card (ThreeBlockIndex w) + 1 : Nat) : Real)
  let B : Real := 1 + norm z
  let C : Real := M + norm z
  let P : Real := terminalReversePolynomialBase w z M
  have hA : 0 <= A := by positivity
  have hB : 0 <= B := by positivity
  have hC : 0 <= C := hshift
  have hP : 1 <= P := terminalReversePolynomialBase_one_le w z M
  have hcombined : A * B * C <= P := by
    exact le_max_right _ _
  have hfactor : terminalReverseFactor w z M <= P ^ N := by
    calc
      terminalReverseFactor w z M <= A ^ N * B ^ N * C ^ N := by
        simpa [A, B, C, N] using
          terminalReverseFactor_le_indexPolynomial w z M hshift
      _ = (A * B * C) ^ N := by rw [mul_pow, mul_pow]
      _ <= P ^ N := pow_le_pow_left₀ (mul_nonneg (mul_nonneg hA hB) hC)
        hcombined N
  have hpow : 1 <= P ^ N := one_le_pow₀ hP
  have hmax : max 1 (terminalReverseFactor w z M) <= P ^ N :=
    max_le hpow hfactor
  have hmaxPos : 0 < max 1 (terminalReverseFactor w z M) :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hlog := Real.log_le_log hmaxPos hmax
  change Real.log (max 1 (terminalReverseFactor w z M)) <= _
  rw [Real.log_pow] at hlog
  simpa [N, P] using hlog

end TerminalAssembly

end BernoulliSection9
