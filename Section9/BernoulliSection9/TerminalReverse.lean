import BernoulliSection9.TerminalAssembly
import BernoulliSection9.ValidMatchingCardinality
import BernoulliLinearAlgebra.ThreeBlockInvalidZero
import BernoulliLinearAlgebra.ThreeBlockShiftTranslation
import Mathlib.Tactic

/-!
# Sharp-support reverse bound for the terminal polynomial

Unlike the quadratic fallback in `TerminalAssembly`, this module first
translates the spectral shift back to zero and then sums only over the
stable dependency's `ValidThreeBlockMatching` subtype.  Every such matching
has at most `3W` entries.  Thus the exact finite factor below is the correct
partial-permutation factor used in (9.38), not the powerset of `7W^2`
variables.
-/

open scoped BigOperators

noncomputable section

namespace BernoulliSection9

open MeasureTheory

namespace TerminalAssembly

/-- Squarefree evaluation at genuinely complex coordinates. -/
def evalComplexSquarefree {iota : Type*} [Fintype iota] [DecidableEq iota]
    (c : Finset iota -> Complex) (x : iota -> Complex) : Complex :=
  ∑ S : Finset iota, c S * ∏ i ∈ S, x i

private theorem squarefreeExponent_prod_apply_complex
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (S : Finset iota) (x : iota -> Complex) :
    (BernoulliLinearAlgebra.squarefreeExponent S).prod
        (fun i e => x i ^ e) = ∏ i ∈ S, x i := by
  rw [Finsupp.prod_of_support_subset (s := S)]
  · simp [BernoulliLinearAlgebra.squarefreeExponent]
  · intro i hi
    simpa [BernoulliLinearAlgebra.squarefreeExponent] using hi
  · intro i _hi
    exact pow_zero (x i)

theorem eval_squarefreePolynomial_eq_evalComplexSquarefree
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (c : BernoulliLinearAlgebra.CoeffSpace iota) (x : iota -> Complex) :
    MvPolynomial.eval x (BernoulliLinearAlgebra.squarefreePolynomial c) =
      evalComplexSquarefree (fun S => c S) x := by
  classical
  simp only [BernoulliLinearAlgebra.squarefreePolynomial,
    MvPolynomial.eval_sum, MvPolynomial.eval_monomial,
    evalComplexSquarefree]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [squarefreeExponent_prod_apply_complex]

/-- At zero shift all invalid squarefree masks disappear, so evaluation is
literally a sum over valid partial-permutation matchings. -/
theorem evalComplexSquarefree_zero_eq_sum_valid
    {w : Type*} [Fintype w] [DecidableEq w]
    (Q : Matrix (BernoulliLinearAlgebra.ThreeBlockOuter w)
      (BernoulliLinearAlgebra.ThreeBlockOuter w) Complex)
    (x : BernoulliLinearAlgebra.ThreeBlockVariable w -> Complex) :
    evalComplexSquarefree
        (fun S => BernoulliLinearAlgebra.threeBlockDetCoefficient Q 0 S) x =
      ∑ a : BernoulliLinearAlgebra.ValidThreeBlockMatching w,
        BernoulliLinearAlgebra.threeBlockDetCoefficient Q 0 a.1 *
          ∏ i ∈ a.1, x i := by
  classical
  let term : Finset (BernoulliLinearAlgebra.ThreeBlockVariable w) -> Complex :=
    fun S => BernoulliLinearAlgebra.threeBlockDetCoefficient Q 0 S *
      ∏ i ∈ S, x i
  have hfilter :
      (∑ S ∈ Finset.univ.filter
          BernoulliLinearAlgebra.IsValidThreeBlockMatching, term S) =
        ∑ S : Finset (BernoulliLinearAlgebra.ThreeBlockVariable w), term S := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hSuniv hSnot
    have hnotValid :
        ¬BernoulliLinearAlgebra.IsValidThreeBlockMatching S := by
      intro hvalid
      exact hSnot (Finset.mem_filter.mpr ⟨hSuniv, hvalid⟩)
    simp [term,
      BernoulliLinearAlgebra.threeBlockDetCoefficient_zero_of_not_valid
        Q S hnotValid]
  have hsubtype :
      (∑ S ∈ Finset.univ.filter
          BernoulliLinearAlgebra.IsValidThreeBlockMatching, term S) =
        ∑ a : BernoulliLinearAlgebra.ValidThreeBlockMatching w, term a.1 := by
    apply Finset.sum_subtype
    intro S
    simp
  calc
    evalComplexSquarefree
        (fun S => BernoulliLinearAlgebra.threeBlockDetCoefficient Q 0 S) x =
        ∑ S : Finset (BernoulliLinearAlgebra.ThreeBlockVariable w), term S := rfl
    _ = ∑ S ∈ Finset.univ.filter
          BernoulliLinearAlgebra.IsValidThreeBlockMatching, term S :=
      hfilter.symm
    _ = ∑ a : BernoulliLinearAlgebra.ValidThreeBlockMatching w, term a.1 :=
      hsubtype
    _ = _ := rfl

/-- The literal shifted terminal determinant, rewritten as a zero-shift
valid-matching sum evaluated at diagonally translated coordinates. -/
theorem packetTerminalValue_eq_sum_valid_zeroShift
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    {mu : Measure Omega}
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (omega : Omega) :
    packetTerminalValue Q z X omega =
      ∑ a : BernoulliLinearAlgebra.ValidThreeBlockMatching w,
        BernoulliLinearAlgebra.threeBlockDetCoefficient
            (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) 0 a.1 *
          ∏ i ∈ a.1,
            BernoulliLinearAlgebra.threeBlockDiagonalShift z
              (fun j => (X.atom j omega : Complex)) i := by
  let Qouter := BernoulliLinearAlgebra.threeBlockOuterOfPacket Q
  let shifted := BernoulliLinearAlgebra.threeBlockDiagonalShift z
    (fun j => (X.atom j omega : Complex))
  calc
    packetTerminalValue Q z X omega =
        MvPolynomial.eval (fun j => (X.atom j omega : Complex))
          (BernoulliLinearAlgebra.threeBlockDetPolynomial Qouter z) := by
      symm
      exact BernoulliLinearAlgebra.eval_threeBlockDetPolynomial Qouter z _
    _ = MvPolynomial.eval shifted
          (BernoulliLinearAlgebra.threeBlockDetPolynomial Qouter 0) := by
      exact BernoulliLinearAlgebra.eval_threeBlockDetPolynomial_shift Qouter z _
    _ = MvPolynomial.eval shifted
          (BernoulliLinearAlgebra.squarefreePolynomial
            (BernoulliLinearAlgebra.threeBlockDetCoeffVector Qouter 0)) := by
      rw [BernoulliLinearAlgebra.threeBlockDetPolynomial_zero_eq_squarefreePolynomial]
    _ = evalComplexSquarefree
          (fun S => BernoulliLinearAlgebra.threeBlockDetCoefficient Qouter 0 S)
          shifted := by
      exact eval_squarefreePolynomial_eq_evalComplexSquarefree
        (iota := BernoulliLinearAlgebra.ThreeBlockVariable w)
        (BernoulliLinearAlgebra.threeBlockDetCoeffVector Qouter 0) shifted
    _ = _ := evalComplexSquarefree_zero_eq_sum_valid Qouter shifted

/-- A valid matching uses at most one entry per full packet row, hence has
degree at most `card (ThreeBlockIndex w) = 3 card w`. -/
theorem validThreeBlockMatching_card_le_indexCard
    {w : Type*} [Fintype w] [DecidableEq w]
    (a : BernoulliLinearAlgebra.ValidThreeBlockMatching w) :
    a.1.card <= Fintype.card (BernoulliLinearAlgebra.ThreeBlockIndex w) := by
  rw [← BernoulliLinearAlgebra.threeBlockMatchingRows_card a]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- Bound one valid-matching monomial by a `3W`-degree power. -/
theorem norm_validMatchingMonomial_le_index_power
    {w : Type*} [Fintype w] [DecidableEq w]
    (Y : BernoulliLinearAlgebra.ThreeBlockVariable w -> Complex)
    (M : Real) (hM : 1 <= M)
    (hY : forall i, norm (Y i) <= M)
    (a : BernoulliLinearAlgebra.ValidThreeBlockMatching w) :
    norm (∏ i ∈ a.1, Y i) <=
      M ^ Fintype.card (BernoulliLinearAlgebra.ThreeBlockIndex w) := by
  calc
    norm (∏ i ∈ a.1, Y i) = ∏ i ∈ a.1, norm (Y i) := by
      exact norm_prod _ _
    _ <= ∏ _i ∈ a.1, M := by
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun i _ => hY i)
    _ = M ^ a.1.card := by simp
    _ <= M ^ Fintype.card (BernoulliLinearAlgebra.ThreeBlockIndex w) :=
      pow_le_pow_right₀ hM (validThreeBlockMatching_card_le_indexCard a)

/-- A zero-shift coefficient is controlled by the shifted coefficient norm
with exactly the stable diagonal-translation factor. -/
theorem norm_zeroCoefficient_le_translationFactor_mul_shiftedNorm
    {w : Type*} [Fintype w] [DecidableEq w]
    (Q : Matrix (BernoulliLinearAlgebra.ThreeBlockOuter w)
      (BernoulliLinearAlgebra.ThreeBlockOuter w) Complex)
    (z : Complex) (S : Finset (BernoulliLinearAlgebra.ThreeBlockVariable w)) :
    norm (BernoulliLinearAlgebra.threeBlockDetCoefficient Q 0 S) <=
      BernoulliLinearAlgebra.threeBlockTranslationFactor (w := w) z *
        BernoulliLinearAlgebra.threeBlockDetCoefficientNorm Q z := by
  let tf := BernoulliLinearAlgebra.threeBlockTranslationFactor (w := w) z
  have hcoordinate :
      norm (BernoulliLinearAlgebra.threeBlockDetCoefficient Q 0 S) <=
        BernoulliLinearAlgebra.threeBlockDetCoefficientNorm Q 0 := by
    simpa [BernoulliLinearAlgebra.threeBlockDetCoefficientNorm] using
      (PiLp.norm_apply_le
        (BernoulliLinearAlgebra.threeBlockDetCoeffVector Q 0) S)
  have htfpos : 0 < tf :=
    BernoulliLinearAlgebra.threeBlockTranslationFactor_pos (w := w) z
  have hlower :=
    BernoulliLinearAlgebra.threeBlockDetCoefficientNorm_shift_lower Q z
  have hscaled := mul_le_mul_of_nonneg_left hlower htfpos.le
  have hzeroNorm :
      BernoulliLinearAlgebra.threeBlockDetCoefficientNorm Q 0 <=
        tf * BernoulliLinearAlgebra.threeBlockDetCoefficientNorm Q z := by
    calc
      BernoulliLinearAlgebra.threeBlockDetCoefficientNorm Q 0 =
          tf * (tf⁻¹ *
            BernoulliLinearAlgebra.threeBlockDetCoefficientNorm Q 0) := by
        rw [← mul_assoc, mul_inv_cancel₀ htfpos.ne', one_mul]
      _ <= tf * BernoulliLinearAlgebra.threeBlockDetCoefficientNorm Q z :=
        hscaled
  exact hcoordinate.trans hzeroNorm

/-- On the coordinatewise `M` event, the diagonally translated coordinates
are bounded by `M + norm z`. -/
theorem norm_threeBlockDiagonalShift_atom_le
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    {mu : Measure Omega}
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (z : Complex) (M : Real) (omega : Omega)
    (homega : omega ∈ coordinatewiseBoundedEvent X M)
    (i : BernoulliLinearAlgebra.ThreeBlockVariable w) :
    norm (BernoulliLinearAlgebra.threeBlockDiagonalShift z
      (fun j => (X.atom j omega : Complex)) i) <= M + norm z := by
  by_cases hii : i.1.1 = i.1.2
  · simp only [BernoulliLinearAlgebra.threeBlockDiagonalShift, hii, if_pos]
    calc
      norm ((X.atom i omega : Complex) - z) <=
          norm (X.atom i omega : Complex) + norm z := norm_sub_le _ _
      _ <= M + norm z := by
        gcongr
        simpa [Complex.norm_real] using homega i
  · simp only [BernoulliLinearAlgebra.threeBlockDiagonalShift, hii, if_neg]
    calc
      norm (X.atom i omega : Complex) <= M := by
        simpa [Complex.norm_real] using homega i
      _ <= M + norm z := le_add_of_nonneg_right (norm_nonneg z)

/-- Sharp-support deterministic reverse bound.  Its factor has
`card ValidThreeBlockMatching` summands, translation loss on exactly `3W`
diagonal variables, and monomial degree at most `3W`. -/
theorem norm_packetTerminalValue_le_validMatchingFactor
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    {mu : Measure Omega}
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (M : Real) (hshift : 1 <= M + norm z)
    (omega : Omega) (homega : omega ∈ coordinatewiseBoundedEvent X M) :
    norm (packetTerminalValue Q z X omega) <=
      (Fintype.card (BernoulliLinearAlgebra.ValidThreeBlockMatching w) : Real) *
        BernoulliLinearAlgebra.threeBlockTranslationFactor (w := w) z *
        (M + norm z) ^
          Fintype.card (BernoulliLinearAlgebra.ThreeBlockIndex w) *
        packetTerminalCoefficientNorm Q z := by
  classical
  rw [packetTerminalValue_eq_sum_valid_zeroShift]
  calc
    norm (∑ a : BernoulliLinearAlgebra.ValidThreeBlockMatching w,
        BernoulliLinearAlgebra.threeBlockDetCoefficient
            (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) 0 a.1 *
          ∏ i ∈ a.1,
            BernoulliLinearAlgebra.threeBlockDiagonalShift z
              (fun j => (X.atom j omega : Complex)) i) <=
        ∑ a : BernoulliLinearAlgebra.ValidThreeBlockMatching w,
          norm (BernoulliLinearAlgebra.threeBlockDetCoefficient
              (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) 0 a.1 *
            ∏ i ∈ a.1,
              BernoulliLinearAlgebra.threeBlockDiagonalShift z
                (fun j => (X.atom j omega : Complex)) i) := norm_sum_le _ _
    _ <= ∑ _a : BernoulliLinearAlgebra.ValidThreeBlockMatching w,
        (BernoulliLinearAlgebra.threeBlockTranslationFactor (w := w) z *
            packetTerminalCoefficientNorm Q z) *
          (M + norm z) ^
            Fintype.card (BernoulliLinearAlgebra.ThreeBlockIndex w) := by
      apply Finset.sum_le_sum
      intro a _ha
      rw [norm_mul]
      have hzero :
          norm (BernoulliLinearAlgebra.threeBlockDetCoefficient
            (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) 0 a.1) <=
            BernoulliLinearAlgebra.threeBlockTranslationFactor (w := w) z *
              packetTerminalCoefficientNorm Q z := by
        simpa [packetTerminalCoefficientNorm,
          BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket] using
          (norm_zeroCoefficient_le_translationFactor_mul_shiftedNorm
            (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) z a.1)
      exact mul_le_mul
        hzero
        (norm_validMatchingMonomial_le_index_power
          (fun i => BernoulliLinearAlgebra.threeBlockDiagonalShift z
            (fun j => (X.atom j omega : Complex)) i)
          (M + norm z) hshift
          (norm_threeBlockDiagonalShift_atom_le X z M omega homega) a)
        (norm_nonneg _)
        (mul_nonneg
          (BernoulliLinearAlgebra.threeBlockTranslationFactor_pos
            (w := w) z).le
          (by
            exact norm_nonneg _))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The explicit partial-function count used to numericalize the sharp
support estimate.  For `N = card (ThreeBlockIndex w) = 3W`, this is
`(N^2 + 1)^N`, hence its logarithm is `O(W log W)`. -/
def validMatchingIndexPolynomialCount (w : Type*) [Fintype w] : Nat :=
  (Fintype.card (BernoulliLinearAlgebra.ThreeBlockIndex w) *
      Fintype.card (BernoulliLinearAlgebra.ThreeBlockIndex w) + 1) ^
    Fintype.card (BernoulliLinearAlgebra.ThreeBlockIndex w)

/-- The sharp-support deterministic bound with the valid-matching
cardinality replaced by its explicit `exp(O(W log W))` upper bound. -/
theorem norm_packetTerminalValue_le_indexPolynomialFactor
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    {mu : Measure Omega}
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (M : Real) (hshift : 1 <= M + norm z)
    (omega : Omega) (homega : omega ∈ coordinatewiseBoundedEvent X M) :
    norm (packetTerminalValue Q z X omega) <=
      (validMatchingIndexPolynomialCount w : Real) *
        BernoulliLinearAlgebra.threeBlockTranslationFactor (w := w) z *
        (M + norm z) ^
          Fintype.card (BernoulliLinearAlgebra.ThreeBlockIndex w) *
        packetTerminalCoefficientNorm Q z := by
  have hcardNat :=
    BernoulliSection9.card_validThreeBlockMatching_le_indexPolynomial
      (w := w)
  have hcardReal :
      (Fintype.card
          (BernoulliLinearAlgebra.ValidThreeBlockMatching w) : Real) <=
        (validMatchingIndexPolynomialCount w : Real) := by
    exact_mod_cast hcardNat
  refine (norm_packetTerminalValue_le_validMatchingFactor
    Q z X M hshift omega homega).trans ?_
  have htf : 0 <=
      BernoulliLinearAlgebra.threeBlockTranslationFactor (w := w) z :=
    (BernoulliLinearAlgebra.threeBlockTranslationFactor_pos
      (w := w) z).le
  have hpower : 0 <= (M + norm z) ^
      Fintype.card (BernoulliLinearAlgebra.ThreeBlockIndex w) :=
    pow_nonneg (zero_le_one.trans hshift) _
  have hcoeff : 0 <= packetTerminalCoefficientNorm Q z := by
    exact norm_nonneg _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcardReal htf) hpower) hcoeff

/-- Equation (7.22), with its exact finite partial-permutation factor left
visible for the final numerical `exp(C W log W)` estimate. -/
theorem packetTerminal_reverse_validMatching
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w] [LinearOrder w]
    {mu : Measure Omega}
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (M reverseLoss : Real) (hshift : 1 <= M + norm z)
    (hreverseLoss : 0 <= reverseLoss)
    (hfactor :
      (Fintype.card (BernoulliLinearAlgebra.ValidThreeBlockMatching w) : Real) *
        BernoulliLinearAlgebra.threeBlockTranslationFactor (w := w) z *
        (M + norm z) ^
          Fintype.card (BernoulliLinearAlgebra.ThreeBlockIndex w) <=
        Real.exp reverseLoss) :
    ∀ omega, omega ∈ coordinatewiseBoundedEvent X M ->
      Real.posLog
        (norm (packetTerminalValue Q z X omega) /
          packetTerminalCoefficientNorm Q z) <= reverseLoss := by
  intro omega homega
  apply posLog_value_div_coefficient_le hreverseLoss
    (packetTerminalCoefficientNorm_pos Q z)
  exact (norm_packetTerminalValue_le_validMatchingFactor
    Q z X M hshift omega homega).trans (by
      exact mul_le_mul_of_nonneg_right hfactor
        (packetTerminalCoefficientNorm_pos Q z).le)

/-- Equation (7.22) with an entirely explicit `exp(O(W log W))` counting
factor.  No matching, mask, or elimination certificate is exposed to the
caller. -/
theorem packetTerminal_reverse_indexPolynomial
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w] [LinearOrder w]
    {mu : Measure Omega}
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (M reverseLoss : Real) (hshift : 1 <= M + norm z)
    (hreverseLoss : 0 <= reverseLoss)
    (hfactor :
      (validMatchingIndexPolynomialCount w : Real) *
        BernoulliLinearAlgebra.threeBlockTranslationFactor (w := w) z *
        (M + norm z) ^
          Fintype.card (BernoulliLinearAlgebra.ThreeBlockIndex w) <=
        Real.exp reverseLoss) :
    ∀ omega, omega ∈ coordinatewiseBoundedEvent X M ->
      Real.posLog
        (norm (packetTerminalValue Q z X omega) /
          packetTerminalCoefficientNorm Q z) <= reverseLoss := by
  intro omega homega
  apply posLog_value_div_coefficient_le hreverseLoss
    (packetTerminalCoefficientNorm_pos Q z)
  exact (norm_packetTerminalValue_le_indexPolynomialFactor
    Q z X M hshift omega homega).trans (by
      exact mul_le_mul_of_nonneg_right hfactor
        (packetTerminalCoefficientNorm_pos Q z).le)

end TerminalAssembly

end BernoulliSection9
