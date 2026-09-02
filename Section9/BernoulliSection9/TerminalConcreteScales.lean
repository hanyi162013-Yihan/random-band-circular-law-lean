import BernoulliSection9.TerminalConcreteBounds
import BernoulliSection9.TerminalConcreteResidual
import BernoulliSection9.TerminalAssembly
import Mathlib.Tactic

/-!
# Canonical scalar bounds for the literal terminal CUR reduction

Every quantity in this file is computed from the paper data.  In particular,
the bounds below do not ask for a block decomposition, an RRQR certificate,
or an auxiliary deformation.  The deliberately generous cardinal factors
keep the ensuing large-`W` arithmetic transparent.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

open MeasureTheory BernoulliLinearAlgebra
open TerminalAssembly

/-- A finite complex matrix with entries bounded by `R` has the displayed
cardinality-times-entry bound in Euclidean operator norm. -/
theorem norm_matrix_le_card_mul_card_mul_of_entry_norm_le
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n Complex) (R : Real)
    (hentry : forall i j, ‖A i j‖ <= R) :
    ‖A‖ <= (Fintype.card m : Real) * Fintype.card n * R := by
  calc
    ‖A‖ <= ∑ i, ∑ j, ‖A i j‖ := matrix_l2_opNorm_le_sum_entry_norm A
    _ <= ∑ _i : m, ∑ _j : n, R := by
      gcongr with i _ j
      exact hentry i j
    _ = (Fintype.card m : Real) * Fintype.card n * R := by
      simp [mul_assoc]

/-- Canonical RRQR cutoff exponent.  It is strictly larger than the shift
exponent by the proved RRQR exponent and a fixed safety margin. -/
def terminalCanonicalThresholdExponent (Kz : Nat) : Nat :=
  Kz + strongRRQRExponent + 12

/-- The paper's `tau_W = W^K0`, with `K0` fixed internally. -/
def terminalCanonicalThreshold (W Kz : Nat) : Real :=
  (W : Real) ^ terminalCanonicalThresholdExponent Kz

theorem terminalCanonicalThreshold_one_le
    {W Kz : Nat} (hW : 1 <= W) :
    1 <= terminalCanonicalThreshold W Kz := by
  unfold terminalCanonicalThreshold
  exact one_le_pow₀ (by exact_mod_cast hW)

/-- A fixed first-Cook polynomial exponent. -/
def terminalCanonicalFirstCookExponent (Kz : Nat) : Real :=
  (8 * (terminalCanonicalThresholdExponent Kz +
    strongRRQRExponent + Kz + 8) : Nat)

/-- The second exponent also absorbs the inverse supplied by the first Cook
call.  It depends only on Cook's explicit input and the fixed shift exponent. -/
def terminalCanonicalSecondCookExponent
    (cook : CookDeformedSquareInput) (Kz : Nat) : Real :=
  2 * terminalCanonicalFirstCookExponent Kz +
    cook.beta (terminalCanonicalFirstCookExponent Kz) + 8

theorem terminalCanonicalFirstCookExponent_nonneg (Kz : Nat) :
    0 <= terminalCanonicalFirstCookExponent Kz := by
  unfold terminalCanonicalFirstCookExponent
  positivity

theorem terminalCanonicalSecondCookExponent_nonneg
    (cook : CookDeformedSquareInput) (Kz : Nat) :
    0 <= terminalCanonicalSecondCookExponent cook Kz := by
  unfold terminalCanonicalSecondCookExponent
  have hbeta := (cook.beta_pos
    (terminalCanonicalFirstCookExponent Kz)).le
  have hfirst := terminalCanonicalFirstCookExponent_nonneg Kz
  linarith

/-- On the canonical maximum-coordinate event, every entry of the literal
reindexed perturbation is bounded by `M + |z|`. -/
theorem norm_terminalBalancedPerturbation_entry_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (M : Real) (hM : 0 <= M) (omega : Omega)
    (homega : omega ∈ coordinatewiseBoundedEvent X M)
    (i j : Fin r ⊕ TerminalBalancedResidualIndex rowEquiv colEquiv) :
    ‖terminalBalancedPerturbation rowEquiv colEquiv z X omega i j‖ <=
      M + ‖z‖ := by
  let ri := terminalBalancedRowEquiv rowEquiv colEquiv i
  let cj := terminalBalancedColEquiv rowEquiv colEquiv j
  have hdelta :
      ‖threeBlockDelta (fun k => (X.atom k omega : Complex)) ri cj‖ <= M := by
    by_cases hfresh : threeBlockFresh ri cj
    · rw [threeBlockDelta_apply_of_fresh _ _ _ hfresh]
      simpa [Real.norm_eq_abs] using homega
        (⟨(ri, cj), hfresh⟩ : ThreeBlockVariable (Fin W))
    · rw [threeBlockDelta_apply_of_not_fresh _ _ _ hfresh]
      simpa using hM
  have hshift :
      ‖(z • (1 : Matrix (ThreeBlockIndex (Fin W))
        (ThreeBlockIndex (Fin W)) Complex)) ri cj‖ <= ‖z‖ := by
    by_cases hij : ri = cj
    · calc
        ‖(z • (1 : Matrix (ThreeBlockIndex (Fin W))
          (ThreeBlockIndex (Fin W)) Complex)) ri cj‖ = ‖z‖ := by
            simp [Matrix.one_apply, hij]
        _ <= ‖z‖ := le_rfl
    · simp [Matrix.one_apply, hij]
  change ‖threeBlockDelta (fun k => (X.atom k omega : Complex)) ri cj -
      (z • (1 : Matrix (ThreeBlockIndex (Fin W))
        (ThreeBlockIndex (Fin W)) Complex)) ri cj‖ <= M + ‖z‖
  exact (norm_sub_le _ _).trans (add_le_add hdelta hshift)

/-- A single scalar dominating all four blocks of the literal perturbation. -/
def terminalDeltaBlockScale {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex) (M : Real) : Real :=
  let N := Fintype.card (TerminalBalancedResidualIndex rowEquiv colEquiv)
  ((r + N : Nat) : Real) ^ 2 * (M + ‖z‖)

theorem terminalDeltaBlockScale_nonneg {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex) {M : Real} (hM : 0 <= M) :
    0 <= terminalDeltaBlockScale rowEquiv colEquiv z M := by
  unfold terminalDeltaBlockScale
  positivity

/-- Each of the pivot and pivot/residual perturbation blocks is bounded by
the same canonical scalar. -/
theorem terminalDelta_blocks_norm_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (M : Real) (hM : 0 <= M) (omega : Omega)
    (homega : omega ∈ coordinatewiseBoundedEvent X M) :
    let Delta := terminalBalancedPerturbation rowEquiv colEquiv z X omega
    let D := terminalDeltaBlockScale rowEquiv colEquiv z M
    ‖delta11 Delta‖ <= D ∧ ‖delta12 Delta‖ <= D ∧
      ‖delta21 Delta‖ <= D ∧ ‖delta22 Delta‖ <= D := by
  dsimp only
  let N := Fintype.card (TerminalBalancedResidualIndex rowEquiv colEquiv)
  let R := M + ‖z‖
  have hR : 0 <= R := add_nonneg hM (norm_nonneg z)
  have hentry := norm_terminalBalancedPerturbation_entry_le
    rowEquiv colEquiv z X M hM omega homega
  have h11 := norm_matrix_le_card_mul_card_mul_of_entry_norm_le
    (delta11 (terminalBalancedPerturbation rowEquiv colEquiv z X omega)) R
    (fun i j => hentry (Sum.inl i) (Sum.inl j))
  have h12 := norm_matrix_le_card_mul_card_mul_of_entry_norm_le
    (delta12 (terminalBalancedPerturbation rowEquiv colEquiv z X omega)) R
    (fun i j => hentry (Sum.inl i) (Sum.inr j))
  have h21 := norm_matrix_le_card_mul_card_mul_of_entry_norm_le
    (delta21 (terminalBalancedPerturbation rowEquiv colEquiv z X omega)) R
    (fun i j => hentry (Sum.inr i) (Sum.inl j))
  have h22 := norm_matrix_le_card_mul_card_mul_of_entry_norm_le
    (delta22 (terminalBalancedPerturbation rowEquiv colEquiv z X omega)) R
    (fun i j => hentry (Sum.inr i) (Sum.inr j))
  change _ <= (((r + N : Nat) : Real) ^ 2 * R) ∧
    _ <= (((r + N : Nat) : Real) ^ 2 * R) ∧
    _ <= (((r + N : Nat) : Real) ^ 2 * R) ∧
    _ <= (((r + N : Nat) : Real) ^ 2 * R)
  have hr : (0 : Real) <= r := by positivity
  have hN : (0 : Real) <= N := by positivity
  have hrr : (r : Real) * r <= ((r + N : Nat) : Real) ^ 2 := by
    push_cast
    nlinarith
  have hrN : (r : Real) * N <= ((r + N : Nat) : Real) ^ 2 := by
    push_cast
    nlinarith
  have hNr : (N : Real) * r <= ((r + N : Nat) : Real) ^ 2 := by
    push_cast
    nlinarith
  have hNN : (N : Real) * N <= ((r + N : Nat) : Real) ^ 2 := by
    push_cast
    nlinarith
  constructor
  · exact h11.trans (mul_le_mul_of_nonneg_right
      (by simpa only [Fintype.card_fin] using hrr) hR)
  constructor
  · exact h12.trans (mul_le_mul_of_nonneg_right
      (by simpa only [Fintype.card_fin] using hrN) hR)
  constructor
  · exact h21.trans (mul_le_mul_of_nonneg_right
      (by simpa only [Fintype.card_fin] using hNr) hR)
  · exact h22.trans (mul_le_mul_of_nonneg_right
      (by simpa only [Fintype.card_fin] using hNN) hR)

/-- Canonical dimension-loss bound for both extended skeleton coefficients. -/
def terminalExtendedCoefficientScale {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) : Real :=
  (r : Real) *
    Fintype.card (TerminalBalancedResidualIndex rowEquiv colEquiv) *
      ((2 * W : Nat) : Real) ^ strongRRQRExponent

/-- Canonical dimension-loss bound for the extended skeleton error. -/
def terminalExtendedErrorScale {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (tau : Real) : Real :=
  (Fintype.card (TerminalBalancedResidualIndex rowEquiv colEquiv) : Real) ^ 2 *
    (((2 * W : Nat) : Real) ^ strongRRQRExponent * tau)

/-- Canonical inverse scale for the unperturbed RRQR pivot. -/
def terminalPivotInverseScale (W : Nat) (tau : Real) : Real :=
  ((2 * W : Nat) : Real) ^ strongRRQRExponent / tau

/-- A cardinality-safe bound for a residual block whose entries are bounded
by `entryScale`. -/
def terminalResidualBlockScale {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (entryScale : Real) : Real :=
  (Fintype.card (TerminalBalancedResidualIndex rowEquiv colEquiv) : Real) ^ 2 *
    entryScale

/-- Raw first-Cook deformation scale. -/
def terminalFirstDeformationScale {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex) (Fscale : Real) : Real :=
  terminalResidualBlockScale rowEquiv colEquiv (‖z‖ + Fscale)

/-- Uniform scale for each residual cross block after CUR. -/
def terminalCrossBlockScale {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex) (M Fscale : Real) : Real :=
  terminalResidualBlockScale rowEquiv colEquiv (M + ‖z‖ + Fscale)

/-- Raw second-Cook deformation scale on the first-Cook good event. -/
def terminalSecondDeformationScale {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex) (M Fscale firstInverseScale : Real) : Real :=
  terminalFirstDeformationScale rowEquiv colEquiv z Fscale +
    terminalCrossBlockScale rowEquiv colEquiv z M Fscale *
      firstInverseScale *
      terminalCrossBlockScale rowEquiv colEquiv z M Fscale

/-! ## `Q`-uniform polynomial scales -/

theorem rrqr_split_rank_le_two_mul {W r q : Nat}
    (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) : r <= 2 * W := by
  have hcard := Fintype.card_congr e
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  omega

/-- Pivot plus residual coordinates always total the literal `3W` rows. -/
theorem terminalBalancedTotalCard_eq_three_mul {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    r + Fintype.card (TerminalBalancedResidualIndex rowEquiv colEquiv) =
      3 * W := by
  have hcard := Fintype.card_congr
    (terminalBalancedRowEquiv rowEquiv colEquiv)
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard ⊢
  change r + (terminalBalancedSize rowEquiv colEquiv +
      (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv)) = 3 * W
  have hcard' : r + (terminalBalancedSize rowEquiv colEquiv +
      (W + outerResidualLeftCount rowEquiv +
        outerResidualRightCount rowEquiv -
          terminalBalancedSize rowEquiv colEquiv)) = 2 * W + W := by
    simpa [ThreeBlockOuter] using hcard
  omega

theorem terminalBalancedResidualCard_le_three_mul {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    Fintype.card (TerminalBalancedResidualIndex rowEquiv colEquiv) <=
      3 * W := by
  have h := terminalBalancedTotalCard_eq_three_mul rowEquiv colEquiv
  omega

theorem terminalBalancedFirstSize_le_three_mul {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    terminalBalancedSize rowEquiv colEquiv <= 3 * W := by
  have h := terminalBalancedTotalCard_eq_three_mul rowEquiv colEquiv
  simp only [TerminalBalancedResidualIndex, Fintype.card_sum,
    Fintype.card_fin] at h
  omega

theorem terminalBalancedSecondSize_le_three_mul {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    W + outerResidualLeftCount rowEquiv + outerResidualRightCount rowEquiv -
        terminalBalancedSize rowEquiv colEquiv <= 3 * W := by
  have h := terminalBalancedTotalCard_eq_three_mul rowEquiv colEquiv
  simp only [TerminalBalancedResidualIndex, Fintype.card_sum,
    Fintype.card_fin] at h
  omega

theorem div_three_le_terminalBalancedFirstSize {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    W / 3 <= terminalBalancedSize rowEquiv colEquiv := by
  unfold terminalBalancedSize balancedSquareSize
  omega

theorem div_three_le_terminalBalancedSecondSize {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    W / 3 <=
      W + outerResidualLeftCount rowEquiv + outerResidualRightCount rowEquiv -
        terminalBalancedSize rowEquiv colEquiv := by
  let a := outerResidualLeftCount rowEquiv
  let b := outerResidualRightCount rowEquiv
  let c := outerResidualLeftCount colEquiv
  let e := outerResidualRightCount colEquiv
  have ha := outerResidualLeftCount_le rowEquiv
  have hc := outerResidualLeftCount_le colEquiv
  have hs := terminalResidual_sideCount_eq rowEquiv colEquiv
  have hsW := outerResidualCount_add_le_two_mul rowEquiv
  have hupper := balancedSquareSize_le_maskUpper ha hc hs hsW
  have hthree := three_mul_balanced_le_two_mul_residual hs hsW
  change W / 3 <= W + a + b - balancedSquareSize W a b c
  have hthree' :
      3 * balancedSquareSize W a b c <= 2 * (W + a + b) := by
    simpa [a, b, c] using hthree
  omega

theorem terminalBalancedFirstSize_two_le {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (hW : 6 <= W) : 2 <= terminalBalancedSize rowEquiv colEquiv := by
  have h := div_three_le_terminalBalancedFirstSize rowEquiv colEquiv
  omega

theorem terminalBalancedSecondSize_two_le {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (hW : 6 <= W) :
    2 <= W + outerResidualLeftCount rowEquiv +
      outerResidualRightCount rowEquiv -
        terminalBalancedSize rowEquiv colEquiv := by
  have h := div_three_le_terminalBalancedSecondSize rowEquiv colEquiv
  omega

/-- `Q`-uniform bound for the extended RRQR coefficients. -/
def terminalUniformCoefficientScale (W : Nat) : Real :=
  ((2 * W : Nat) : Real) * ((3 * W : Nat) : Real) *
    ((2 * W : Nat) : Real) ^ strongRRQRExponent

/-- `Q`-uniform bound for the extended RRQR error. -/
def terminalUniformErrorScale (W : Nat) (tau : Real) : Real :=
  ((3 * W : Nat) : Real) ^ 2 *
    (((2 * W : Nat) : Real) ^ strongRRQRExponent * tau)

/-- `Q`-uniform bound for all perturbation blocks on `E_max`. -/
def terminalUniformDeltaScale (W : Nat) (z : Complex) (M : Real) : Real :=
  ((3 * W : Nat) : Real) ^ 2 * (M + ‖z‖)

/-- `Q`-uniform fixed-polynomial bound for the cancellation-visible CUR
error `F`. -/
def terminalUniformFScale (W : Nat) (tau M : Real) (z : Complex) : Real :=
  terminalFPolynomialScale
    (terminalUniformCoefficientScale W)
    (terminalUniformErrorScale W tau)
    (terminalUniformDeltaScale W z M)
    (terminalPivotInverseScale W tau)

/-- `Q`-uniform first Cook deformation bound. -/
def terminalUniformFirstDeformationScale
    (W : Nat) (tau M : Real) (z : Complex) : Real :=
  ((3 * W : Nat) : Real) ^ 2 *
    (‖z‖ + terminalUniformFScale W tau M z)

/-- `Q`-uniform residual cross-block bound. -/
def terminalUniformCrossScale
    (W : Nat) (tau M : Real) (z : Complex) : Real :=
  ((3 * W : Nat) : Real) ^ 2 *
    (M + ‖z‖ + terminalUniformFScale W tau M z)

/-- Worst first-square inverse scale, using only `n₁ <= 3W`. -/
def terminalUniformFirstCookInverseScale
    (cook : CookDeformedSquareInput) (W Kz : Nat) : Real :=
  ((3 * W : Nat) : Real) ^
    cook.beta (terminalCanonicalFirstCookExponent Kz)

/-- `Q`-uniform second Cook deformation bound. -/
def terminalUniformSecondDeformationScale
    (cook : CookDeformedSquareInput) (W Kz : Nat)
    (tau M : Real) (z : Complex) : Real :=
  terminalUniformFirstDeformationScale W tau M z +
    terminalUniformCrossScale W tau M z *
      terminalUniformFirstCookInverseScale cook W Kz *
      terminalUniformCrossScale W tau M z

theorem terminalDeltaBlockScale_eq_uniform {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex) (M : Real) :
    terminalDeltaBlockScale rowEquiv colEquiv z M =
      terminalUniformDeltaScale W z M := by
  dsimp [terminalDeltaBlockScale, terminalUniformDeltaScale]
  rw [terminalBalancedTotalCard_eq_three_mul rowEquiv colEquiv]

theorem terminalExtendedCoefficientScale_le_uniform {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :
    terminalExtendedCoefficientScale rowEquiv colEquiv <=
      terminalUniformCoefficientScale W := by
  unfold terminalExtendedCoefficientScale terminalUniformCoefficientScale
  have hr : (r : Real) <= (2 * W : Nat) := by
    exact_mod_cast rrqr_split_rank_le_two_mul rowEquiv
  have hN :
      (Fintype.card (TerminalBalancedResidualIndex rowEquiv colEquiv) : Real) <=
        (3 * W : Nat) := by
    exact_mod_cast terminalBalancedResidualCard_le_three_mul rowEquiv colEquiv
  have hpow : 0 <= ((2 * W : Nat) : Real) ^ strongRRQRExponent := by positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hr hN (by positivity) (by positivity)) hpow

theorem terminalExtendedErrorScale_le_uniform {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    {tau : Real} (htau : 0 <= tau) :
    terminalExtendedErrorScale rowEquiv colEquiv tau <=
      terminalUniformErrorScale W tau := by
  unfold terminalExtendedErrorScale terminalUniformErrorScale
  have hN :
      (Fintype.card (TerminalBalancedResidualIndex rowEquiv colEquiv) : Real) <=
        (3 * W : Nat) := by
    exact_mod_cast terminalBalancedResidualCard_le_three_mul rowEquiv colEquiv
  have hsquare :
      (Fintype.card (TerminalBalancedResidualIndex rowEquiv colEquiv) : Real) ^ 2 <=
        ((3 * W : Nat) : Real) ^ 2 := by
    nlinarith [sq_nonneg
      ((3 * W : Nat) - Fintype.card
        (TerminalBalancedResidualIndex rowEquiv colEquiv) : Real)]
  exact mul_le_mul_of_nonneg_right hsquare (mul_nonneg (by positivity) htau)

end BernoulliSection9
