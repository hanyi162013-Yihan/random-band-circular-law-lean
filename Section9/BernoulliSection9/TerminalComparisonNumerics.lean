import BernoulliSection9.TerminalNumerics
import BernoulliLinearAlgebra.ConcreteBoundaryFinal

/-!
# Explicit polynomial bound for the terminal comparison constant

The read-only coefficient theorem uses the exact factor
`max 1 sqrt(# valid matchings)` times one translation factor per diagonal
packet coordinate.  The internally proved matching count turns its logarithm
into a literal `O(W log W)` expression.
-/

noncomputable section

namespace BernoulliSection9

open BernoulliLinearAlgebra

namespace TerminalAssembly

/-- A single polynomial base dominating both the valid-matching constant and
the diagonal translation appearing in the coefficient comparison. -/
def terminalComparisonPolynomialBase
    (w : Type*) [Fintype w] [DecidableEq w]
    (z : Complex) : Real :=
  max 1
    (((Fintype.card (ThreeBlockIndex w) *
        Fintype.card (ThreeBlockIndex w) + 1 : Nat) : Real) *
      (1 + norm z))

theorem terminalComparisonPolynomialBase_one_le
    (w : Type*) [Fintype w] [DecidableEq w]
    (z : Complex) :
    1 <= terminalComparisonPolynomialBase w z :=
  le_max_left _ _

private theorem threeBlockZeroComparisonConstant_le_indexPolynomial
    (w : Type*) [Fintype w] [DecidableEq w] :
    threeBlockZeroComparisonConstant (w := w) <=
      (((Fintype.card (ThreeBlockIndex w) *
          Fintype.card (ThreeBlockIndex w) + 1 : Nat) : Real) ^
        Fintype.card (ThreeBlockIndex w)) := by
  let P : Real :=
    (((Fintype.card (ThreeBlockIndex w) *
        Fintype.card (ThreeBlockIndex w) + 1 : Nat) : Real) ^
      Fintype.card (ThreeBlockIndex w))
  have hcardNat := card_validThreeBlockMatching_le_indexPolynomial (w := w)
  have hcard :
      (Fintype.card (ValidThreeBlockMatching w) : Real) <= P := by
    dsimp [P]
    exact_mod_cast hcardNat
  have hPone : 1 <= P := by
    dsimp [P]
    apply one_le_pow₀
    exact_mod_cast (show 1 <=
      Fintype.card (ThreeBlockIndex w) *
        Fintype.card (ThreeBlockIndex w) + 1 by omega)
  have hsqrt :
      Real.sqrt (Fintype.card (ValidThreeBlockMatching w) : Real) <= P := by
    have hcardNonneg :
        0 <= (Fintype.card (ValidThreeBlockMatching w) : Real) := by
      positivity
    have hsquare := Real.sq_sqrt hcardNonneg
    have hsqrtNonneg := Real.sqrt_nonneg
      (Fintype.card (ValidThreeBlockMatching w) : Real)
    nlinarith
  exact max_le hPone hsqrt

/-- The concrete coefficient-comparison constant is at most one copy of a
single polynomial base per full packet coordinate. -/
theorem threeBlockConcreteComparisonConstant_le_polynomialBase_pow
    (w : Type*) [Fintype w] [DecidableEq w]
    (z : Complex) :
    threeBlockConcreteComparisonConstant (W := w) z <=
      terminalComparisonPolynomialBase w z ^
        Fintype.card (ThreeBlockIndex w) := by
  let N := Fintype.card (ThreeBlockIndex w)
  let A : Real :=
    ((Fintype.card (ThreeBlockIndex w) *
      Fintype.card (ThreeBlockIndex w) + 1 : Nat) : Real)
  let B : Real := 1 + norm z
  let P : Real := terminalComparisonPolynomialBase w z
  have hA : 0 <= A := by positivity
  have hB : 0 <= B := by positivity
  have hAB : A * B <= P := le_max_right _ _
  calc
    threeBlockConcreteComparisonConstant (W := w) z =
        threeBlockZeroComparisonConstant (w := w) * B ^ N := by
      rw [threeBlockConcreteComparisonConstant,
        threeBlockTranslationFactor_eq_power]
    _ <= A ^ N * B ^ N :=
      mul_le_mul_of_nonneg_right
        (by simpa [A, N] using
          threeBlockZeroComparisonConstant_le_indexPolynomial w)
        (pow_nonneg hB N)
    _ = (A * B) ^ N := by rw [mul_pow]
    _ <= P ^ N := pow_le_pow_left₀ (mul_nonneg hA hB) hAB N

/-- Literal logarithmic `O(W log W)` bound for the exact coefficient-side
comparison loss. -/
theorem log_threeBlockConcreteComparisonConstant_le_card_mul_log_base
    (w : Type*) [Fintype w] [DecidableEq w]
    (z : Complex) :
    Real.log (threeBlockConcreteComparisonConstant (W := w) z) <=
      (Fintype.card (ThreeBlockIndex w) : Real) *
        Real.log (terminalComparisonPolynomialBase w z) := by
  let K := threeBlockConcreteComparisonConstant (W := w) z
  let P := terminalComparisonPolynomialBase w z
  let N := Fintype.card (ThreeBlockIndex w)
  have hKpos : 0 < K := by
    dsimp [K, threeBlockConcreteComparisonConstant]
    exact mul_pos
      (zero_lt_one.trans_le
        (threeBlockZeroComparisonConstant_one_le (w := w)))
      (threeBlockTranslationFactor_pos (w := w) z)
  have hbound : K <= P ^ N := by
    simpa [K, P, N] using
      threeBlockConcreteComparisonConstant_le_polynomialBase_pow w z
  have hlog := Real.log_le_log hKpos hbound
  rw [Real.log_pow] at hlog
  simpa [K, P, N] using hlog

end TerminalAssembly

end BernoulliSection9
