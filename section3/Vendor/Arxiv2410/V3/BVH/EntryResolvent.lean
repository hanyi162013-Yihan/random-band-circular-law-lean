/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/EntryResolvent.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.ResolventPerturbation
import Vendor.Arxiv2410.V3.RowReplacement
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The rank-two entry resolvent calculation behind BVH Remark 6.13

This file contains only deterministic finite-dimensional algebra for the specialization of
Brailovskaya--van Handel, Remark 6.13 used in arXiv:2410.16457v3, Proposition 3.4.
A single complex entry is embedded as a self-adjoint rank-two summand in the Hermitization.
We then prove the exact resolvent expansion through second order and bound its cubic remainder
in normalized trace.  No probability or comparison conclusion is assumed here.
-/

namespace Arxiv2410V3

open Matrix Complex
open scoped Matrix.Norms.L2Operator

namespace BVH

/-- The matrix with the single entry `w` in position `(i,j)`. -/
def singleEntryMatrix {n : ℕ} (i j : Fin n) (w : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single i j w

/-- The self-adjoint `2n × 2n` summand contributed by one complex entry:
`[[0, w Eᵢⱼ], [(w Eᵢⱼ)ᴴ, 0]]`. -/
def entryHermitianSummand {n : ℕ} (i j : Fin n) (w : ℂ) :
    Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ :=
  let E := singleEntryMatrix i j w
  Matrix.fromBlocks 0 E Eᴴ 0

/-- A single complex entry gives a Hermitian summand. -/
theorem entryHermitianSummand_isHermitian {n : ℕ} (i j : Fin n) (w : ℂ) :
    (entryHermitianSummand i j w).IsHermitian := by
  exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero rfl Matrix.isHermitian_zero

/-- The entry summand is the difference of the corresponding Hermitizations at zero shift. -/
theorem entryHermitianSummand_eq_hermitization_sub {n : ℕ}
    (i j : Fin n) (w : ℂ) :
    entryHermitianSummand i j w =
      hermitization (singleEntryMatrix i j w) 0 - hermitization 0 0 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [entryHermitianSummand, singleEntryMatrix, hermitization, shiftedMatrix]

/-- A single complex entry changes the Hermitization by rank at most two. -/
theorem entryHermitianSummand_rank_le_two {n : ℕ}
    (i j : Fin n) (w : ℂ) :
    (entryHermitianSummand i j w).rank ≤ 2 := by
  have hrow : DiffersOnlyOnRow (singleEntryMatrix i j w) 0 i := by
    intro k l hki
    change Matrix.single i j w k l = 0
    exact Matrix.single_apply_of_row_ne hki.symm j l w
  rw [entryHermitianSummand_eq_hermitization_sub]
  exact rank_hermitization_sub_le_two (singleEntryMatrix i j w) 0 0 i hrow

/-- The transposition exchanging the two coordinates on which an entry summand is supported. -/
private def entrySwapPerm {n : ℕ} (i j : Fin n) :
    Equiv.Perm (HermitizationIndex n) :=
  Equiv.swap (Sum.inl i) (Sum.inr j)

/-- The two nonzero weights used to factor an entry summand as a permutation times a diagonal. -/
private def entrySwapWeight {n : ℕ} (i j : Fin n) (w : ℂ) :
    HermitizationIndex n → ℂ
  | Sum.inl k => if k = i then star w else 0
  | Sum.inr k => if k = j then w else 0

/-- Factorization used to read off the `L²` operator norm of the rank-two summand. -/
private theorem entryHermitianSummand_eq_perm_mul_diagonal {n : ℕ}
    (i j : Fin n) (w : ℂ) :
    entryHermitianSummand i j w =
      (entrySwapPerm i j).permMatrix ℂ * Matrix.diagonal (entrySwapWeight i j w) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · by_cases hai : a = i
    · subst a
      simp [entryHermitianSummand, singleEntryMatrix, entrySwapPerm, entrySwapWeight,
        Matrix.mul_apply, Equiv.toPEquiv, PEquiv.toMatrix, Matrix.diagonal_apply,
        Equiv.swap_apply_def]
    · by_cases hab : a = b
      · subst b
        simp [entryHermitianSummand, singleEntryMatrix, entrySwapPerm, entrySwapWeight,
          Matrix.mul_apply, Equiv.toPEquiv, PEquiv.toMatrix, Matrix.diagonal_apply,
          Equiv.swap_apply_def, hai]
      · simp [entryHermitianSummand, singleEntryMatrix, entrySwapPerm, entrySwapWeight,
          Matrix.mul_apply, Equiv.toPEquiv, PEquiv.toMatrix, Matrix.diagonal_apply,
          Equiv.swap_apply_def, hai, hab]
  · by_cases hai : a = i
    · subst a
      by_cases hbj : b = j
      · subst b
        simp [entryHermitianSummand, singleEntryMatrix, entrySwapPerm, entrySwapWeight,
          Matrix.mul_apply, Equiv.toPEquiv, PEquiv.toMatrix, Matrix.diagonal_apply,
          Equiv.swap_apply_def]
      · simp [entryHermitianSummand, singleEntryMatrix, entrySwapPerm, entrySwapWeight,
          Matrix.mul_apply, Equiv.toPEquiv, PEquiv.toMatrix, Matrix.diagonal_apply,
          Equiv.swap_apply_def, hbj]
        exact Matrix.single_apply_of_col_ne i i (fun h => hbj h.symm) w
    · simp [entryHermitianSummand, singleEntryMatrix, entrySwapPerm, entrySwapWeight,
        Matrix.mul_apply, Equiv.toPEquiv, PEquiv.toMatrix, Matrix.diagonal_apply,
        Equiv.swap_apply_def, hai]
      exact Matrix.single_apply_of_row_ne (fun h => hai h.symm) j b w
  · by_cases haj : a = j
    · subst a
      by_cases hbi : b = i
      · subst b
        simp [entryHermitianSummand, singleEntryMatrix, entrySwapPerm, entrySwapWeight,
          Matrix.mul_apply, Equiv.toPEquiv, PEquiv.toMatrix, Matrix.diagonal_apply,
          Equiv.swap_apply_def]
      · simp [entryHermitianSummand, singleEntryMatrix, entrySwapPerm, entrySwapWeight,
          Matrix.mul_apply, Equiv.toPEquiv, PEquiv.toMatrix, Matrix.diagonal_apply,
          Equiv.swap_apply_def, hbi]
        exact Matrix.single_apply_of_col_ne j j (fun h => hbi h.symm) (star w)
    · simp [entryHermitianSummand, singleEntryMatrix, entrySwapPerm, entrySwapWeight,
        Matrix.mul_apply, Equiv.toPEquiv, PEquiv.toMatrix, Matrix.diagonal_apply,
        Equiv.swap_apply_def, haj]
      exact Matrix.single_apply_of_row_ne (fun h => haj h.symm) i b (star w)
  · by_cases haj : a = j
    · subst a
      simp [entryHermitianSummand, singleEntryMatrix, entrySwapPerm, entrySwapWeight,
        Matrix.mul_apply, Equiv.toPEquiv, PEquiv.toMatrix, Matrix.diagonal_apply,
        Equiv.swap_apply_def]
    · by_cases hab : a = b
      · subst b
        simp [entryHermitianSummand, singleEntryMatrix, entrySwapPerm, entrySwapWeight,
          Matrix.mul_apply, Equiv.toPEquiv, PEquiv.toMatrix, Matrix.diagonal_apply,
          Equiv.swap_apply_def, haj]
      · simp [entryHermitianSummand, singleEntryMatrix, entrySwapPerm, entrySwapWeight,
          Matrix.mul_apply, Equiv.toPEquiv, PEquiv.toMatrix, Matrix.diagonal_apply,
          Equiv.swap_apply_def, haj, hab]

/-- The `L²` operator norm of a single entry summand is at most the modulus of the entry. -/
theorem entryHermitianSummand_l2OpNorm_le {n : ℕ}
    (i j : Fin n) (w : ℂ) :
    ‖entryHermitianSummand i j w‖ ≤ ‖w‖ := by
  rw [entryHermitianSummand_eq_perm_mul_diagonal]
  calc
    ‖(entrySwapPerm i j).permMatrix ℂ * Matrix.diagonal (entrySwapWeight i j w)‖
        ≤ ‖(entrySwapPerm i j).permMatrix ℂ‖ *
            ‖Matrix.diagonal (entrySwapWeight i j w)‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * ‖Matrix.diagonal (entrySwapWeight i j w)‖ := by
      gcongr
      exact Matrix.permMatrix_l2_opNorm_le (entrySwapPerm i j)
    _ = ‖entrySwapWeight i j w‖ := by simp
    _ ≤ ‖w‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2
      intro k
      rcases k with k | k
      · by_cases hk : k = i <;> simp [entrySwapWeight, hk]
      · by_cases hk : k = j <;> simp [entrySwapWeight, hk]

/-- The entry summand depends real-linearly on its complex entry.  These are the two fixed
Hermitian directions whose first and second scalar moments cancel in the local Lindeberg step. -/
theorem entryHermitianSummand_re_im_decomposition {n : ℕ}
    (i j : Fin n) (w : ℂ) :
    entryHermitianSummand i j w =
      (w.re : ℂ) • entryHermitianSummand i j 1 +
        (w.im : ℂ) • entryHermitianSummand i j Complex.I := by
  have hstar : star w = (w.re : ℂ) - (w.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [entryHermitianSummand, singleEntryMatrix, Matrix.single, hstar]
  all_goals split_ifs with h <;> simp_all [Complex.re_add_im, sub_eq_add_neg]

/-- Adding one entry to `X` adds exactly the corresponding Hermitian summand to its
Hermitization.  The deterministic shift by `z` is unchanged. -/
theorem hermitization_add_singleEntryMatrix {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (i j : Fin n) (w : ℂ) :
    hermitization (X + singleEntryMatrix i j w) z =
      hermitization X z + entryHermitianSummand i j w := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [hermitization, shiftedMatrix, entryHermitianSummand, singleEntryMatrix] <;> ring

section ResolventExpansion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cubic remainder in the exact second-order expansion of the resolvent at `A` in
direction `H`.  There are four resolvent factors and three copies of `H`. -/
noncomputable def resolventCubicRemainder
    (A H : Matrix ι ι ℂ) (eta : ℂ) : Matrix ι ι ℂ :=
  let R := (A - eta • (1 : Matrix ι ι ℂ))⁻¹
  let RH := (A + H - eta • (1 : Matrix ι ι ℂ))⁻¹
  R * H * R * H * R * H * RH

/-- Exact noncommutative resolvent expansion through second order:

`R(A+H) = R - RHR + RHRHR - RHRHRHR(A+H)`.

This algebraic identity replaces the informal Taylor expansion in the specialized proof of
BVH Remark 6.13. -/
theorem hermitian_resolvent_second_order_expansion
    (A H : Matrix ι ι ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    {eta : ℂ} (heta : 0 < eta.im) :
    let R := (A - eta • (1 : Matrix ι ι ℂ))⁻¹
    let RH := (A + H - eta • (1 : Matrix ι ι ℂ))⁻¹
    RH = R - R * H * R + R * H * R * H * R - resolventCubicRemainder A H eta := by
  dsimp only
  let R := (A - eta • (1 : Matrix ι ι ℂ))⁻¹
  let RH := (A + H - eta • (1 : Matrix ι ι ℂ))⁻¹
  have hres := hermitian_resolvent_sub_resolvent A (A + H) hA (hA.add hH) heta
  have hdiff : A + H - A = H := by abel
  rw [hdiff] at hres
  change R - RH = R * H * RH at hres
  have hbase : RH = R - R * H * RH := by
    calc
      RH = R - (R - RH) := by abel
      _ = R - R * H * RH := by rw [hres]
  calc
    RH = R - R * H * RH := hbase
    _ = R - R * H * (R - R * H * RH) :=
      congrArg (fun X => R - R * H * X) hbase
    _ = R - R * H * R + R * H * R * H * RH := by noncomm_ring
    _ = R - R * H * R + R * H * R * H * (R - R * H * RH) :=
      congrArg (fun X => R - R * H * R + R * H * R * H * X) hbase
    _ = R - R * H * R + R * H * R * H * R -
        resolventCubicRemainder A H eta := by
      simp only [resolventCubicRemainder, R, RH]
      noncomm_ring

/-- Entrywise version of the exact expansion, displayed as a fixed quadratic polynomial in
`Re w` and `Im w`.  This is the precise algebra needed for cancellation of matching first and
second real moments in a one-coordinate Lindeberg replacement. -/
theorem entry_resolvent_second_order_expansion_re_im
    {n : ℕ}
    (A : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ)
    (hA : A.IsHermitian) (i j : Fin n) (w : ℂ)
    {eta : ℂ} (heta : 0 < eta.im) :
    let R := (A - eta • (1 : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ))⁻¹
    let Hr := entryHermitianSummand i j 1
    let Hi := entryHermitianSummand i j Complex.I
    let x : ℂ := w.re
    let y : ℂ := w.im
    let RH := (A + entryHermitianSummand i j w -
      eta • (1 : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ))⁻¹
    RH = R - x • (R * Hr * R) - y • (R * Hi * R) +
        (x * x) • (R * Hr * R * Hr * R) +
        (x * y) • (R * Hr * R * Hi * R) +
        (y * x) • (R * Hi * R * Hr * R) +
        (y * y) • (R * Hi * R * Hi * R) -
        resolventCubicRemainder A (entryHermitianSummand i j w) eta := by
  dsimp only
  let H := entryHermitianSummand i j w
  let Hr := entryHermitianSummand i j 1
  let Hi := entryHermitianSummand i j Complex.I
  let R := (A - eta •
    (1 : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ))⁻¹
  have hgen := hermitian_resolvent_second_order_expansion A H hA
    (entryHermitianSummand_isHermitian i j w) heta
  have hdecomp : H = (w.re : ℂ) • Hr + (w.im : ℂ) • Hi := by
    simpa only [H, Hr, Hi] using entryHermitianSummand_re_im_decomposition i j w
  have hlinear : R * H * R =
      (w.re : ℂ) • (R * Hr * R) + (w.im : ℂ) • (R * Hi * R) := by
    rw [hdecomp]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hquadratic : R * H * R * H * R =
      ((w.re : ℂ) * (w.re : ℂ)) • (R * Hr * R * Hr * R) +
      ((w.re : ℂ) * (w.im : ℂ)) • (R * Hr * R * Hi * R) +
      ((w.im : ℂ) * (w.re : ℂ)) • (R * Hi * R * Hr * R) +
      ((w.im : ℂ) * (w.im : ℂ)) • (R * Hi * R * Hi * R) := by
    rw [hdecomp]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul]
    module
  change (A + H - eta •
      (1 : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ))⁻¹ = _
  change (A + H - eta •
      (1 : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ))⁻¹ =
    R - R * H * R + R * H * R * H * R - resolventCubicRemainder A H eta at hgen
  refine hgen.trans ?_
  rw [hquadratic, hlinear]
  abel

private theorem normalizedTrace_add_bvh
    {κ : Type*} [Fintype κ] (M N : Matrix κ κ ℂ) :
    normalizedTrace (M + N) = normalizedTrace M + normalizedTrace N := by
  simp [normalizedTrace, Matrix.trace_add, add_div]

private theorem normalizedTrace_smul_bvh
    {κ : Type*} [Fintype κ] (c : ℂ) (M : Matrix κ κ ℂ) :
    normalizedTrace (c • M) = c * normalizedTrace M := by
  simp [normalizedTrace, Matrix.trace_smul, mul_div_assoc]

/-- Normalized-trace form of `entry_resolvent_second_order_expansion_re_im`.  Every coefficient
is fixed once `A,i,j,eta` are fixed; all dependence on the replaced entry is an explicit complex
quadratic polynomial plus the cubic remainder. -/
theorem normalizedTrace_entry_resolvent_second_order_expansion_re_im
    {n : ℕ}
    (A : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ)
    (hA : A.IsHermitian) (i j : Fin n) (w : ℂ)
    {eta : ℂ} (heta : 0 < eta.im) :
    let R := (A - eta • (1 : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ))⁻¹
    let Hr := entryHermitianSummand i j 1
    let Hi := entryHermitianSummand i j Complex.I
    let x : ℂ := w.re
    let y : ℂ := w.im
    let RH := (A + entryHermitianSummand i j w -
      eta • (1 : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ))⁻¹
    normalizedTrace RH = normalizedTrace R - x * normalizedTrace (R * Hr * R) -
        y * normalizedTrace (R * Hi * R) +
        (x * x) * normalizedTrace (R * Hr * R * Hr * R) +
        (x * y) * normalizedTrace (R * Hr * R * Hi * R) +
        (y * x) * normalizedTrace (R * Hi * R * Hr * R) +
        (y * y) * normalizedTrace (R * Hi * R * Hi * R) -
        normalizedTrace (resolventCubicRemainder A (entryHermitianSummand i j w) eta) := by
  dsimp only
  have hmatrix := entry_resolvent_second_order_expansion_re_im A hA i j w heta
  have htrace := congrArg normalizedTrace hmatrix
  simpa only [normalizedTrace_add_bvh, normalizedTrace_sub,
    normalizedTrace_smul_bvh] using htrace

/-- The cubic remainder has no larger rank than the perturbation. -/
theorem resolventCubicRemainder_rank_le
    (A H : Matrix ι ι ℂ) (eta : ℂ) :
    (resolventCubicRemainder A H eta).rank ≤ H.rank := by
  let R := (A - eta • (1 : Matrix ι ι ℂ))⁻¹
  let RH := (A + H - eta • (1 : Matrix ι ι ℂ))⁻¹
  change (R * H * R * H * R * H * RH).rank ≤ H.rank
  calc
    (R * H * R * H * R * H * RH).rank ≤ (R * H).rank := by
      simpa only [Matrix.mul_assoc] using
        Matrix.rank_mul_le_left (R * H) (R * H * R * H * RH)
    _ ≤ H.rank := Matrix.rank_mul_le_right R H

private theorem norm_mul_seven_le
    (a b c d e f g : Matrix ι ι ℂ) :
    ‖a * b * c * d * e * f * g‖ ≤
      ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ * ‖f‖ * ‖g‖ := by
  calc
    ‖a * b * c * d * e * f * g‖ ≤ ‖a * b * c * d * e * f‖ * ‖g‖ :=
      norm_mul_le _ _
    _ ≤ (‖a * b * c * d * e‖ * ‖f‖) * ‖g‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ ((‖a * b * c * d‖ * ‖e‖) * ‖f‖) * ‖g‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ (((‖a * b * c‖ * ‖d‖) * ‖e‖) * ‖f‖) * ‖g‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ ((((‖a * b‖ * ‖c‖) * ‖d‖) * ‖e‖) * ‖f‖) * ‖g‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ (((((‖a‖ * ‖b‖) * ‖c‖) * ‖d‖) * ‖e‖) * ‖f‖) * ‖g‖ := by
      gcongr
      exact norm_mul_le _ _
    _ = ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ * ‖f‖ * ‖g‖ := by ring

/-- Four Hermitian resolvent bounds give the `v⁻⁴` cubic remainder estimate. -/
theorem resolventCubicRemainder_l2OpNorm_le
    [Nonempty ι]
    (A H : Matrix ι ι ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    {eta : ℂ} (heta : 0 < eta.im) :
    ‖resolventCubicRemainder A H eta‖ ≤ ‖H‖ ^ 3 / eta.im ^ 4 := by
  let R := (A - eta • (1 : Matrix ι ι ℂ))⁻¹
  let RH := (A + H - eta • (1 : Matrix ι ι ℂ))⁻¹
  have hR : ‖R‖ ≤ eta.im⁻¹ :=
    norm_shiftedHermitian_inv_le_inv_im A hA heta
  have hRH : ‖RH‖ ≤ eta.im⁻¹ :=
    norm_shiftedHermitian_inv_le_inv_im (A + H) (hA.add hH) heta
  change ‖R * H * R * H * R * H * RH‖ ≤ ‖H‖ ^ 3 / eta.im ^ 4
  calc
    ‖R * H * R * H * R * H * RH‖ ≤
        ‖R‖ * ‖H‖ * ‖R‖ * ‖H‖ * ‖R‖ * ‖H‖ * ‖RH‖ :=
      norm_mul_seven_le R H R H R H RH
    _ ≤ eta.im⁻¹ * ‖H‖ * eta.im⁻¹ * ‖H‖ * eta.im⁻¹ * ‖H‖ * eta.im⁻¹ := by
      gcongr
    _ = ‖H‖ ^ 3 / eta.im ^ 4 := by
      field_simp [heta.ne']

variable [Nonempty ι]

/-- Normalized-trace form of the cubic remainder bound.  The rank factor is retained so that
rank-two entry summands cancel the dimension `2n` of the Hermitization. -/
theorem norm_normalizedTrace_resolventCubicRemainder_le
    (A H : Matrix ι ι ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    {eta : ℂ} (heta : 0 < eta.im) :
    ‖normalizedTrace (resolventCubicRemainder A H eta)‖ ≤
      (H.rank : ℝ) * ‖H‖ ^ 3 /
        ((Fintype.card ι : ℝ) * eta.im ^ 4) := by
  let Q := resolventCubicRemainder A H eta
  have hcard : 0 < (Fintype.card ι : ℝ) := by positivity
  have hvpow : 0 < eta.im ^ 4 := pow_pos heta 4
  have hrank := resolventCubicRemainder_rank_le A H eta
  have htrace := norm_matrix_trace_le_rank_mul_l2OpNorm Q
  have hnorm := resolventCubicRemainder_l2OpNorm_le A H hA hH heta
  rw [normalizedTrace, norm_div, Complex.norm_natCast]
  calc
    ‖Matrix.trace Q‖ / (Fintype.card ι : ℝ)
        ≤ ((Q.rank : ℝ) * ‖Q‖) / (Fintype.card ι : ℝ) := by
      exact div_le_div_of_nonneg_right htrace hcard.le
    _ ≤ ((H.rank : ℝ) * (‖H‖ ^ 3 / eta.im ^ 4)) /
          (Fintype.card ι : ℝ) := by
      gcongr
    _ = (H.rank : ℝ) * ‖H‖ ^ 3 /
          ((Fintype.card ι : ℝ) * eta.im ^ 4) := by
      field_simp [hcard.ne', hvpow.ne']

end ResolventExpansion

/-- The BVH cubic remainder estimate specialized to one complex matrix entry.  Its scale is
exactly `‖w‖³ / (n v⁴)`; the explicit constant here is `1`. -/
theorem norm_normalizedTrace_entry_resolventCubicRemainder_le
    {n : ℕ} [NeZero n]
    (A : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ)
    (hA : A.IsHermitian) (i j : Fin n) (w : ℂ)
    {eta : ℂ} (heta : 0 < eta.im) :
    ‖normalizedTrace
        (resolventCubicRemainder A (entryHermitianSummand i j w) eta)‖ ≤
      ‖w‖ ^ 3 / ((n : ℝ) * eta.im ^ 4) := by
  let H := entryHermitianSummand i j w
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hgeneral := norm_normalizedTrace_resolventCubicRemainder_le
    A H hA (entryHermitianSummand_isHermitian i j w) heta
  have hrank : (H.rank : ℝ) ≤ 2 := by
    exact_mod_cast entryHermitianSummand_rank_le_two i j w
  have hnorm : ‖H‖ ^ 3 ≤ ‖w‖ ^ 3 := by
    exact pow_le_pow_left₀ (norm_nonneg H) (entryHermitianSummand_l2OpNorm_le i j w) 3
  calc
    ‖normalizedTrace (resolventCubicRemainder A H eta)‖
        ≤ (H.rank : ℝ) * ‖H‖ ^ 3 /
            ((Fintype.card (HermitizationIndex n) : ℝ) * eta.im ^ 4) := hgeneral
    _ ≤ 2 * ‖w‖ ^ 3 /
          (((2 * n : ℕ) : ℝ) * eta.im ^ 4) := by
      rw [card_hermitizationIndex]
      gcongr
    _ = ‖w‖ ^ 3 / ((n : ℝ) * eta.im ^ 4) := by
      push_cast
      field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']

end BVH

end Arxiv2410V3
