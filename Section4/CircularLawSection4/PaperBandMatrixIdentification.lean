import CircularLawSection4.PaperCyclicBandReindex

/-!
# Identifying the raw cyclic band matrix with `X_N - z I_N`

The manuscript numbers the coefficients in one scalar row by the offsets
`-W, ..., W`.  For the state-copy formalization it is more convenient to
number the same coefficients by `0, ..., m + 1`, where `m + 1 = 2W`, and to
single out the final coefficient as `beta`.

This module makes that last notation change exact.  We first define the
unshifted cyclic scalar band matrix `paperScalarBandMatrix`.  Its parameter
`center : Fin (m + 1)` specifies which of the first `m + 1` coefficients is
the diagonal coefficient; in the symmetric manuscript specialization it is
the coefficient numbered `W`.  We then subtract `z I` as an actual matrix
operation and prove that the result is precisely `paperCyclicRawBandMatrix`
with the spectral shift inserted in the `center` coefficient.

The formulation deliberately keeps the deterministic row coefficients
abstract.  Substituting `x i k = b k * xi i k` gives the manuscript's
`b_s xi_{i,s}` coefficients, without adding any probabilistic assumptions.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

variable {R : Type*} [Field R]

/-- The unshifted cyclic scalar band matrix.  The coefficient `x i k` is put
in row `i` and cyclic column `i - center + k`.  Thus the coefficient numbered
`center` lies on the diagonal.  Summing the indicators also gives the right
meaning in small cyclic sizes where two nominal offsets can coincide. -/
def paperScalarBandMatrix
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (x : ZMod N → Fin (m + 2) → R) : Matrix (ZMod N) (ZMod N) R :=
  fun i j ↦
    ∑ k : Fin (m + 2),
      if j = i - (center.val : ZMod N) + (k.val : ZMod N) then x i k else 0

/-- The literal matrix `X_N - z I_N` associated with
`paperScalarBandMatrix`. -/
def paperShiftedScalarBandMatrix
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (x : ZMod N → Fin (m + 2) → R) (z : R) :
    Matrix (ZMod N) (ZMod N) R :=
  paperScalarBandMatrix N m center x - z • (1 : Matrix (ZMod N) (ZMod N) R)

/-- The right-edge coefficient, which is the manuscript's `beta_i`. -/
def paperRightEdgeCoefficient
    (m : ℕ) (x : ZMod N → Fin (m + 2) → R) : ZMod N → R :=
  fun i ↦ x i (Fin.last (m + 1))

/-- The first `m + 1` row coefficients after inserting the spectral shift.
Only the coefficient indexed by `center` is changed, from `x i center` to
`x i center - z`. -/
def paperShiftedInteriorCoefficient
    (m : ℕ) (center : Fin (m + 1))
    (x : ZMod N → Fin (m + 2) → R) (z : R) :
    ZMod N → Fin (m + 1) → R :=
  fun i k ↦ x i k.castSucc - if k = center then z else 0

private theorem paper_center_position
    (N m : ℕ) [NeZero N] (center : Fin (m + 1)) (i : ZMod N) :
    i - (center.val : ZMod N) + (center.val : ZMod N) = i := by
  abel

private theorem paper_final_position
    (N m : ℕ) [NeZero N] (center : Fin (m + 1)) (i : ZMod N) :
    i + -(center.val : ZMod N) + 1 + (m : ZMod N) =
      i - (center.val : ZMod N) + ((m + 1 : ℕ) : ZMod N) := by
  push_cast
  abel

private theorem paper_spectral_shift_sum
    (N m : ℕ) [NeZero N] (center : Fin (m + 1)) (z : R)
    (i j : ZMod N) :
    (∑ k : Fin (m + 1),
        if j = i - (center.val : ZMod N) + (k.val : ZMod N) then
          (if k = center then z else 0)
        else 0) =
      if i = j then z else 0 := by
  classical
  rw [Finset.sum_eq_single center]
  · rw [paper_center_position N m center i]
    by_cases h : i = j
    · subst j
      simp
    · have hji : j ≠ i := fun hji => h hji.symm
      simp [h, hji]
  · intro k _ hk
    simp [hk]
  · simp

/-- Exact entry formula for the shifted scalar matrix. -/
theorem paperShiftedScalarBandMatrix_apply
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (x : ZMod N → Fin (m + 2) → R) (z : R) (i j : ZMod N) :
    paperShiftedScalarBandMatrix N m center x z i j =
      (∑ k : Fin (m + 2),
        if j = i - (center.val : ZMod N) + (k.val : ZMod N) then x i k else 0) -
        if i = j then z else 0 := by
  simp [paperShiftedScalarBandMatrix, paperScalarBandMatrix,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]

/-- The raw closure-plus-band matrix is exactly the manuscript's scalar
band matrix minus `z I`.  Here the raw offset is the left edge `-center`,
the final coefficient is `beta_i`, and the spectral shift is inserted in
the unique coefficient representing offset zero.

For the manuscript's symmetric width `W`, take `m + 1 = 2W` and
`center.val = W`; then the full coefficient indices `0, ..., m + 1`
represent precisely the offsets `-W, ..., W`. -/
theorem paperCyclicRawBandMatrix_eq_paperShiftedScalarBandMatrix
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (x : ZMod N → Fin (m + 2) → R) (z : R) :
    paperCyclicRawBandMatrix N m (-(center.val : ZMod N))
        (paperRightEdgeCoefficient m x)
        (paperShiftedInteriorCoefficient m center x z) =
      paperShiftedScalarBandMatrix N m center x z := by
  classical
  ext i j
  rw [paperShiftedScalarBandMatrix_apply]
  simp only [paperCyclicRawBandMatrix, paperRightEdgeCoefficient,
    paperShiftedInteriorCoefficient]
  nth_rewrite 2 [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [paper_final_position N m center i]
  simp only [← sub_eq_add_neg]
  have hsplit (k : Fin (m + 1)) :
      (if j = i - (center.val : ZMod N) + (k.val : ZMod N) then
          x i k.castSucc - (if k = center then z else 0)
        else 0) =
        (if j = i - (center.val : ZMod N) + (k.val : ZMod N) then
            x i k.castSucc else 0) -
        (if j = i - (center.val : ZMod N) + (k.val : ZMod N) then
            (if k = center then z else 0) else 0) := by
    split_ifs <;> ring
  have hsum :
      (∑ k : Fin (m + 1),
        if j = i - (center.val : ZMod N) + (k.val : ZMod N) then
          x i k.castSucc - (if k = center then z else 0)
        else 0) =
        (∑ k : Fin (m + 1),
          if j = i - (center.val : ZMod N) + (k.val : ZMod N) then
            x i k.castSucc else 0) -
          ∑ k : Fin (m + 1),
            if j = i - (center.val : ZMod N) + (k.val : ZMod N) then
              (if k = center then z else 0) else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    exact hsplit k
  rw [hsum]
  rw [paper_spectral_shift_sum (R := R) N m center z i j]
  ring

/-- The preceding identification after substituting the manuscript's
factorization `x_{i,k} = b_k xi_{i,k}`. -/
theorem paperCyclicRawBandMatrix_eq_X_sub_zI
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (b : Fin (m + 2) → R) (xi : ZMod N → Fin (m + 2) → R) (z : R) :
    paperCyclicRawBandMatrix N m (-(center.val : ZMod N))
        (fun i ↦ b (Fin.last (m + 1)) * xi i (Fin.last (m + 1)))
        (fun i k ↦ b k.castSucc * xi i k.castSucc -
          if k = center then z else 0) =
      paperShiftedScalarBandMatrix N m center
        (fun i k ↦ b k * xi i k) z := by
  change
    paperCyclicRawBandMatrix N m (-(center.val : ZMod N))
        (paperRightEdgeCoefficient m (fun i k ↦ b k * xi i k))
        (paperShiftedInteriorCoefficient m center
          (fun i k ↦ b k * xi i k) z) =
      paperShiftedScalarBandMatrix N m center
        (fun i k ↦ b k * xi i k) z
  exact paperCyclicRawBandMatrix_eq_paperShiftedScalarBandMatrix
    (R := R) N m center (fun i k ↦ b k * xi i k) z

end CircularLawSection4
