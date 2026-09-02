import BernoulliSection9.StrongRRQR
import BernoulliSection9.TerminalConcreteCUR
import BernoulliSection9.TerminalBounds
import BernoulliSection9.PivotPerturbation
import Mathlib.Tactic

/-!
# Concrete deterministic bounds for the terminal CUR reduction

This file contains the purely deterministic estimates needed after the
canonical RRQR reindexing and before the two conditional Cook inputs.  In
particular, all constants are explicit functions of dimensions and of the
four scalar input bounds; no elimination, mask, or RRQR certificate is an
argument.
-/

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

/-! ## Entry and zero-extension estimates -/

/-- Every entry of a complex matrix is bounded by its Euclidean operator
norm.  We record this elementary fact locally because it is useful for
bounding canonical zero extensions between differently indexed spaces. -/
theorem norm_matrix_entry_le_l2_opNorm
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n Complex) (i : m) (j : n) :
    ‖A i j‖ ≤ ‖A‖ := by
  let x : EuclideanSpace Complex n := WithLp.toLp 2 (Pi.single j 1)
  have hx : ‖x‖ = 1 := by
    simp [x, PiLp.norm_single]
  have hAx := Matrix.l2_opNorm_mulVec A x
  have hcoord : ‖(Matrix.mulVec A (x : n → Complex)) i‖ ≤
      ‖(EuclideanSpace.equiv m Complex).symm
        (Matrix.mulVec A (x : n → Complex))‖ :=
    by
      simpa using PiLp.norm_apply_le
        ((EuclideanSpace.equiv m Complex).symm
          (Matrix.mulVec A (x : n → Complex))) i
  have hentry : (Matrix.mulVec A (x : n → Complex)) i = A i j := by
    simp [x]
  calc
    ‖A i j‖ = ‖(Matrix.mulVec A (x : n → Complex)) i‖ :=
      congrArg norm hentry.symm
    _ ≤ ‖(EuclideanSpace.equiv m Complex).symm
        (Matrix.mulVec A (x : n → Complex))‖ := hcoord
    _ ≤ ‖A‖ * ‖x‖ := hAx
    _ = ‖A‖ := by rw [hx, mul_one]

/-- A matrix whose entries are either zero or entries of `A` has an explicit
dimension-times-operator-norm bound.  This is the robust finite-dimensional
substitute used below for an isometric zero-extension API. -/
theorem norm_matrix_le_card_mul_card_mul_of_entries_from
    {m n m' n' : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n']
    [DecidableEq m] [DecidableEq n] [DecidableEq n']
    (A : Matrix m n Complex) (B : Matrix m' n' Complex)
    (hentry : ∀ i j, B i j = 0 ∨ ∃ a b, B i j = A a b) :
    ‖B‖ ≤ (Fintype.card m' : Real) * Fintype.card n' * ‖A‖ := by
  calc
    ‖B‖ ≤ ∑ i, ∑ j, ‖B i j‖ := matrix_l2_opNorm_le_sum_entry_norm B
    _ ≤ ∑ _i : m', ∑ _j : n', ‖A‖ := by
      gcongr with i _ j
      rcases hentry i j with hij | ⟨a, b, hij⟩
      · simp [hij]
      · simpa [hij] using norm_matrix_entry_le_l2_opNorm A a b
    _ = (Fintype.card m' : Real) * Fintype.card n' * ‖A‖ := by
      simp [mul_assoc]

/-- The canonical central-zero extension of `X_skel` has an explicit
dimension loss and no analytic assumption. -/
theorem norm_terminalExtendedX_le
    {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (X : Matrix (Fin r) (Fin q) Complex) :
    ‖terminalExtendedX rowEquiv colEquiv X‖ ≤
      (r : Real) *
        Fintype.card (TerminalBalancedResidualIndex rowEquiv colEquiv) * ‖X‖ := by
  apply (norm_matrix_le_card_mul_card_mul_of_entries_from X
    (terminalExtendedX rowEquiv colEquiv X) ?_).trans_eq
  · simp
  · intro i j
    rcases hcol : terminalBalancedResidualColEquiv rowEquiv colEquiv j with k | k
    · right
      exact ⟨i, outerResidualFinEquiv colEquiv k, by
        simp [terminalExtendedX, hcol]⟩
    · left
      simp [terminalExtendedX, hcol]

/-- The canonical central-zero extension of `Y_skel` has the analogous
explicit dimension loss. -/
theorem norm_terminalExtendedY_le
    {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (Y : Matrix (Fin q) (Fin r) Complex) :
    ‖terminalExtendedY rowEquiv colEquiv Y‖ ≤
      Fintype.card (TerminalBalancedResidualIndex rowEquiv colEquiv) *
        (r : Real) * ‖Y‖ := by
  apply (norm_matrix_le_card_mul_card_mul_of_entries_from Y
    (terminalExtendedY rowEquiv colEquiv Y) ?_).trans_eq
  · simp
  · intro i j
    rcases hrow : terminalBalancedResidualRowEquiv rowEquiv colEquiv i with k | k
    · right
      exact ⟨outerResidualFinEquiv rowEquiv k, j, by
        simp [terminalExtendedY, hrow]⟩
    · left
      simp [terminalExtendedY, hrow]

/-- The canonical central-zero extension of `E₀` has an explicit squared
dimension loss. -/
theorem norm_terminalExtendedE_le
    {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (E : Matrix (Fin q) (Fin q) Complex) :
    ‖terminalExtendedE rowEquiv colEquiv E‖ ≤
      (Fintype.card (TerminalBalancedResidualIndex rowEquiv colEquiv) : Real) ^ 2 *
        ‖E‖ := by
  apply (norm_matrix_le_card_mul_card_mul_of_entries_from E _ ?_).trans_eq
  · ring
  · intro i j
    rcases hrow : terminalBalancedResidualRowEquiv rowEquiv colEquiv i with k | k <;>
      rcases hcol : terminalBalancedResidualColEquiv rowEquiv colEquiv j with l | l
    · right
      exact ⟨outerResidualFinEquiv rowEquiv k,
        outerResidualFinEquiv colEquiv l, by
          simp [terminalExtendedE, hrow, hcol]⟩
    · left; simp [terminalExtendedE, hrow, hcol]
    · left; simp [terminalExtendedE, hrow, hcol]
    · left; simp [terminalExtendedE, hrow, hcol]

/-! ## Perturbed-pivot and residual polynomial bounds -/

/-- The exact fixed polynomial appearing after the term-by-term estimate
of the cancellation-visible residual `F`. -/
def terminalFPolynomialScale (B E D I : Real) : Real :=
  E + B * D + D * B + B * D * B +
    (D + B * D) * (2 * I) * (D + D * B)

theorem terminalFPolynomialScale_nonneg
    {B E D I : Real} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hD : 0 ≤ D) (hI : 0 ≤ I) :
    0 ≤ terminalFPolynomialScale B E D I := by
  unfold terminalFPolynomialScale
  positivity

/-- Blockwise bounds and a pivot-inverse bound imply the displayed fixed
polynomial bound for `F`. -/
theorem F_norm_le_terminalFPolynomialScale
    {p q : Type*} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) Complex)
    (B E D I : Real)
    (hX : ‖S.Xskel‖ ≤ B) (hY : ‖S.Yskel‖ ≤ B)
    (hE : ‖S.E0‖ ≤ E)
    (h11 : ‖delta11 Delta‖ ≤ D) (h12 : ‖delta12 Delta‖ ≤ D)
    (h21 : ‖delta21 Delta‖ ≤ D)
    (hInv : ‖(KDelta S Delta)⁻¹‖ ≤ 2 * I)
    (hB0 : 0 ≤ B) (hD0 : 0 ≤ D) (hI0 : 0 ≤ I) :
    ‖F S Delta‖ ≤ terminalFPolynomialScale B E D I := by
  have hG21 : ‖G21 S Delta‖ ≤ D + B * D := by
    exact (G21_norm_le S Delta).trans (add_le_add h21
      (mul_le_mul hY h11 (norm_nonneg _) hB0))
  have hG12 : ‖G12 S Delta‖ ≤ D + D * B := by
    exact (G12_norm_le S Delta).trans (add_le_add h12
      (mul_le_mul h11 hX (norm_nonneg _) hD0))
  have hYD : ‖S.Yskel‖ * ‖delta12 Delta‖ ≤ B * D :=
    mul_le_mul hY h12 (norm_nonneg _) hB0
  have hDX : ‖delta21 Delta‖ * ‖S.Xskel‖ ≤ D * B :=
    mul_le_mul h21 hX (norm_nonneg _) hD0
  have hYDX : ‖S.Yskel‖ * ‖delta11 Delta‖ * ‖S.Xskel‖ ≤ B * D * B := by
    exact mul_le_mul (mul_le_mul hY h11 (norm_nonneg _) hB0) hX
      (norm_nonneg _) (mul_nonneg hB0 hD0)
  have hGKG : ‖G21 S Delta‖ * ‖(KDelta S Delta)⁻¹‖ * ‖G12 S Delta‖ ≤
      (D + B * D) * (2 * I) * (D + D * B) := by
    exact mul_le_mul (mul_le_mul hG21 hInv (norm_nonneg _)
      (add_nonneg hD0 (mul_nonneg hB0 hD0))) hG12 (norm_nonneg _)
      (mul_nonneg (add_nonneg hD0 (mul_nonneg hB0 hD0))
        (mul_nonneg (by norm_num) hI0))
  exact (F_norm_le S Delta).trans (by
    unfold terminalFPolynomialScale
    linarith)

/-- A convenient scalar hypothesis implies the exact perturbative
smallness condition `‖K⁻¹ Δ₁₁‖ ≤ 1/2`. -/
theorem norm_inv_mul_delta11_le_half_of_bounds
    {p q : Type*} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) Complex)
    (D I : Real) (hD : ‖delta11 Delta‖ ≤ D)
    (hI : ‖S.Kpiv⁻¹‖ ≤ I) (hsmall : I * D ≤ (2 : Real)⁻¹) :
    ‖S.Kpiv⁻¹ * delta11 Delta‖ ≤ (2 : Real)⁻¹ := by
  calc
    ‖S.Kpiv⁻¹ * delta11 Delta‖ ≤
        ‖S.Kpiv⁻¹‖ * ‖delta11 Delta‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ I * D := mul_le_mul hI hD (norm_nonneg _) (le_trans (norm_nonneg _) hI)
    _ ≤ (2 : Real)⁻¹ := hsmall

/-- Complete positive-rank pivot stability package: invertibility, inverse
bound, and determinant lower bound. -/
theorem terminalPivot_stable
    {r q : Nat} (hr : 0 < r)
    (S : BlockSkeletonData (Fin r) (Fin q))
    (Delta : Matrix (Fin r ⊕ Fin q) (Fin r ⊕ Fin q) Complex)
    (D I pivotLower : Real)
    (hK : IsUnit S.Kpiv.det)
    (hD : ‖delta11 Delta‖ ≤ D) (hI : ‖S.Kpiv⁻¹‖ ≤ I)
    (hsmall : I * D ≤ (2 : Real)⁻¹)
    (hpivotLower : 0 ≤ pivotLower)
    (hpivot : pivotLower ≤ ‖S.Kpiv.det‖) :
    IsUnit (KDelta S Delta).det ∧
      ‖(KDelta S Delta)⁻¹‖ ≤ 2 * I ∧
      (2 : Real)⁻¹ ^ r * pivotLower ≤ ‖(KDelta S Delta).det‖ := by
  have hpert := norm_inv_mul_delta11_le_half_of_bounds S Delta D I hD hI hsmall
  have hdet := pivot_add_det_lower hr S.Kpiv (delta11 Delta) hK hpert
    hpivotLower hpivot
  have hdetpos : 0 < ‖(KDelta S Delta).det‖ := by
    have hfactor : 0 < (2 : Real)⁻¹ ^ r := pow_pos (by norm_num) _
    have hKpos : 0 < ‖S.Kpiv.det‖ := norm_pos_iff.mpr
      (isUnit_iff_ne_zero.mp hK)
    have hraw := pivot_add_det_lower_of_inv_mul_norm_le_half hr
      S.Kpiv (delta11 Delta) hK hpert
    exact (mul_pos hfactor hKpos).trans_le (by simpa [KDelta] using hraw)
  refine ⟨isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hdetpos), ?_, ?_⟩
  · exact (norm_pivot_add_inv_le_two_mul_of_inv_mul_norm_le_half hr
      S.Kpiv (delta11 Delta) hK hpert).trans
        (mul_le_mul_of_nonneg_left hI (by norm_num))
  · simpa [KDelta] using hdet

/-- Determinant lower bound for an RRQR pivot in terms of the selected
large singular values.  The fixed loss is `n^(-C_RRQR r)`.  The product on
the left is definitionally the first-`r` product used by
`largeSingularProduct`, but retaining the `Fin r` indexing makes the theorem
directly usable without an auxiliary finite-set reindexing lemma. -/
theorem rrqrPivot_det_lower_selectedProduct
    {n r : Nat} (A : Matrix (Fin n) (Fin n) Complex) (tau : Real)
    (R : StrongRRQRConclusion A tau r) :
    ((n : Real) ^ strongRRQRExponent)⁻¹ ^ r *
        (∏ j : Fin r, (Matrix.toEuclideanLin A).singularValues
          (Fin.castLE R.r_le_n j)) ≤ ‖R.data.Kpiv.det‖ := by
  rw [norm_det_eq_prod_matrixSingularValue]
  have hprod :
      ∏ j : Fin r,
          (((n : Real) ^ strongRRQRExponent)⁻¹ *
            (Matrix.toEuclideanLin A).singularValues
              (Fin.castLE R.r_le_n j)) ≤
        ∏ j : Fin r,
          (Matrix.toEuclideanLin R.data.Kpiv).singularValues j := by
    exact Finset.prod_le_prod (fun _ _ => mul_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))
      ((Matrix.toEuclideanLin A).singularValues_nonneg _))
      (fun j _ => R.pivot_singular_lower j)
  simpa [Finset.prod_mul_distrib, matrixSingularValue,
    Finset.prod_const, Fin.prod_univ_eq_prod_range] using hprod

end BernoulliSection9
