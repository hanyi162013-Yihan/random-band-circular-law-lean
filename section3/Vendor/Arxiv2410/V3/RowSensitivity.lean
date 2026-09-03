/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/RowSensitivity.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.RowReplacement
import Vendor.Arxiv2410.V3.ResolventPerturbation

/-!
# Row sensitivity of the normalized resolvent trace

This file closes the deterministic implication in v3 Proposition 3.4, proof step (3): the
rank-two Hermitization perturbation caused by replacing one row changes the normalized Stieltjes
trace by at most `2 / (n * Im eta)`.  The bound is independent of the size of the replaced row,
which is why the paper needs no moment assumption for McDiarmid concentration.
-/

namespace Arxiv2410V3

open Matrix Complex
open scoped Matrix.Norms.L2Operator

/-- A general finite-dimensional low-rank resolvent trace bound.  It combines the proved
`|Tr T| ≤ rank(T) ‖T‖`, the resolvent rank inequality, and the two `1 / Im eta` resolvent norm
bounds. -/
theorem norm_normalizedTrace_hermitian_resolvent_sub_le_rank
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    {eta : ℂ} (heta : 0 < eta.im) :
    ‖normalizedTrace ((A - eta • (1 : Matrix ι ι ℂ))⁻¹) -
        normalizedTrace ((B - eta • (1 : Matrix ι ι ℂ))⁻¹)‖ ≤
      ((B - A).rank : ℝ) * (2 * eta.im⁻¹) / (Fintype.card ι : ℝ) := by
  let RA : Matrix ι ι ℂ := (A - eta • (1 : Matrix ι ι ℂ))⁻¹
  let RB : Matrix ι ι ℂ := (B - eta • (1 : Matrix ι ι ℂ))⁻¹
  have hrank : (RA - RB).rank ≤ (B - A).rank := by
    exact rank_hermitian_resolvent_sub_le A B hA hB heta
  have hnorm : ‖RA - RB‖ ≤ 2 * eta.im⁻¹ := by
    calc
      ‖RA - RB‖ ≤ ‖RA‖ + ‖RB‖ := norm_sub_le _ _
      _ ≤ eta.im⁻¹ + eta.im⁻¹ := add_le_add
        (hermitian_resolvent_l2OpNorm_le_inv_im A hA heta)
        (hermitian_resolvent_l2OpNorm_le_inv_im B hB heta)
      _ = 2 * eta.im⁻¹ := by ring
  have htrace : ‖Matrix.trace (RA - RB)‖ ≤
      ((B - A).rank : ℝ) * (2 * eta.im⁻¹) := by
    calc
      ‖Matrix.trace (RA - RB)‖ ≤ ((RA - RB).rank : ℝ) * ‖RA - RB‖ :=
        norm_matrix_trace_le_rank_mul_l2OpNorm (RA - RB)
      _ ≤ ((B - A).rank : ℝ) * (2 * eta.im⁻¹) := by
        apply mul_le_mul
        · exact_mod_cast hrank
        · exact hnorm
        · positivity
        · positivity
  rw [← normalizedTrace_sub, normalizedTrace, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right htrace (Nat.cast_nonneg _)

/-- v3 Proposition 3.4, proof step (3): replacing a single row changes the actual normalized
Stieltjes trace by at most `2 / (n Im eta)`. -/
theorem norm_stieltjesTrace_sub_le_of_differsOnlyOnRow
    {n : ℕ} [NeZero n]
    (X X' : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {eta : ℂ} (heta : 0 < eta.im)
    (i : Fin n) (hrow : DiffersOnlyOnRow X X' i) :
    ‖stieltjesTrace X z eta - stieltjesTrace X' z eta‖ ≤
      2 / ((n : ℝ) * eta.im) := by
  have hrow' : DiffersOnlyOnRow X' X i := by
    intro k j hki
    exact (hrow k j hki).symm
  have hrank : (hermitization X' z - hermitization X z).rank ≤ 2 :=
    rank_hermitization_sub_le_two X' X z i hrow'
  have hgeneral := norm_normalizedTrace_hermitian_resolvent_sub_le_rank
    (hermitization X z) (hermitization X' z)
    (hermitization_isHermitian X z) (hermitization_isHermitian X' z) heta
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_neZero n)
  calc
    ‖stieltjesTrace X z eta - stieltjesTrace X' z eta‖ ≤
        ((hermitization X' z - hermitization X z).rank : ℝ) *
          (2 * eta.im⁻¹) / (Fintype.card (HermitizationIndex n) : ℝ) := by
      simpa only [stieltjesTrace, greenFunction] using hgeneral
    _ ≤ 2 * (2 * eta.im⁻¹) / (2 * n : ℕ) := by
      rw [card_hermitizationIndex]
      apply div_le_div_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hrank
        · positivity
      · positivity
    _ = 2 / ((n : ℝ) * eta.im) := by
      norm_num
      field_simp

/-- Real-coordinate bounded difference used by the real McDiarmid application. -/
theorem abs_re_stieltjesTrace_sub_le_of_differsOnlyOnRow
    {n : ℕ} [NeZero n]
    (X X' : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {eta : ℂ} (heta : 0 < eta.im)
    (i : Fin n) (hrow : DiffersOnlyOnRow X X' i) :
    |(stieltjesTrace X z eta).re - (stieltjesTrace X' z eta).re| ≤
      2 / ((n : ℝ) * eta.im) := by
  calc
    |(stieltjesTrace X z eta).re - (stieltjesTrace X' z eta).re| =
        |(stieltjesTrace X z eta - stieltjesTrace X' z eta).re| := by
      rw [Complex.sub_re]
    _ ≤ ‖stieltjesTrace X z eta - stieltjesTrace X' z eta‖ :=
      Complex.abs_re_le_norm _
    _ ≤ 2 / ((n : ℝ) * eta.im) :=
      norm_stieltjesTrace_sub_le_of_differsOnlyOnRow X X' z heta i hrow

/-- Imaginary-coordinate bounded difference used by the real McDiarmid application. -/
theorem abs_im_stieltjesTrace_sub_le_of_differsOnlyOnRow
    {n : ℕ} [NeZero n]
    (X X' : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {eta : ℂ} (heta : 0 < eta.im)
    (i : Fin n) (hrow : DiffersOnlyOnRow X X' i) :
    |(stieltjesTrace X z eta).im - (stieltjesTrace X' z eta).im| ≤
      2 / ((n : ℝ) * eta.im) := by
  calc
    |(stieltjesTrace X z eta).im - (stieltjesTrace X' z eta).im| =
        |(stieltjesTrace X z eta - stieltjesTrace X' z eta).im| := by
      rw [Complex.sub_im]
    _ ≤ ‖stieltjesTrace X z eta - stieltjesTrace X' z eta‖ :=
      Complex.abs_im_le_norm _
    _ ≤ 2 / ((n : ℝ) * eta.im) :=
      norm_stieltjesTrace_sub_le_of_differsOnlyOnRow X X' z heta i hrow

end Arxiv2410V3

