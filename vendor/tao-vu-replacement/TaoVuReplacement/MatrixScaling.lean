import TaoVuReplacement.WeylSecondMoment

/-!
# The `n^{-1/2}` normalization in the replacement principle

This file isolates the deterministic scaling calculation used in Tao--Vu,
Theorem 2.1.  For a positive-dimensional complex matrix `A`, we write

`normalizedMatrix A = n^{-1/2} A`,

where `n` is the cardinality of the index type.  Combining the exact
Hilbert--Schmidt scaling formula with Tao--Vu Lemma A.2 gives

`(1/n) sum_i |lambda_i(n^{-1/2} A)|^2 <= ‖A‖_HS^2 / n^2`.
-/

open scoped BigOperators

noncomputable section

namespace TaoVuReplacement

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The scalar `n^{-1/2}`, embedded from `ℝ` into `ℂ`. -/
def inverseSqrtDimension (n : Type*) [Fintype n] : ℂ :=
  ((Real.sqrt (Fintype.card n : ℝ))⁻¹ : ℝ)

/-- The matrix normalization `n^{-1/2} A` in Tao--Vu, Theorem 2.1. -/
def normalizedMatrix (A : Matrix n n ℂ) : Matrix n n ℂ :=
  inverseSqrtDimension n • A

/-- Hilbert--Schmidt square under multiplication by a complex scalar. -/
theorem hilbertSchmidtSq_smul (c : ℂ) (A : Matrix n n ℂ) :
    hilbertSchmidtSq (c • A) = ‖c‖ ^ 2 * hilbertSchmidtSq A := by
  unfold hilbertSchmidtSq
  change (∑ i, ∑ j, ‖c * A i j‖ ^ 2) = _
  simp_rw [norm_mul, mul_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]

/-- In positive dimension, the square norm of the normalization scalar is
exactly `1/n`. -/
theorem norm_inverseSqrtDimension_sq [Nonempty n] :
    ‖inverseSqrtDimension n‖ ^ 2 = (Fintype.card n : ℝ)⁻¹ := by
  have hn : (0 : ℝ) < Fintype.card n := by
    exact_mod_cast Fintype.card_pos
  simp only [inverseSqrtDimension, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, inv_pow]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sq_sqrt hn.le]

/-- The exact Hilbert--Schmidt scaling formula
`‖n^{-1/2} A‖_HS^2 = ‖A‖_HS^2 / n`. -/
theorem hilbertSchmidtSq_normalizedMatrix [Nonempty n]
    (A : Matrix n n ℂ) :
    hilbertSchmidtSq (normalizedMatrix A) =
      hilbertSchmidtSq A / (Fintype.card n : ℝ) := by
  rw [normalizedMatrix, hilbertSchmidtSq_smul,
    norm_inverseSqrtDimension_sq]
  rw [div_eq_mul_inv, mul_comm]

/-- Before dividing by the total spectral mass, Weyl's inequality and the
exact scaling identity give
`sum_i |lambda_i(n^{-1/2} A)|^2 <= ‖A‖_HS^2 / n`. -/
theorem normalizedEigenvalueSecondMoment_le_hilbertSchmidtSq_div_dimension
    [Nonempty n] (A : Matrix n n ℂ) :
    ((eigenvalueMultiset (normalizedMatrix A)).map
      (fun z ↦ ‖z‖ ^ 2)).sum ≤
        hilbertSchmidtSq A / (Fintype.card n : ℝ) := by
  calc
    ((eigenvalueMultiset (normalizedMatrix A)).map
        (fun z ↦ ‖z‖ ^ 2)).sum ≤
      hilbertSchmidtSq (normalizedMatrix A) :=
        eigenvalueSecondMoment_le_hilbertSchmidtSq (normalizedMatrix A)
    _ = hilbertSchmidtSq A / (Fintype.card n : ℝ) :=
      hilbertSchmidtSq_normalizedMatrix A

/-- The normalized empirical spectral second moment is bounded by the
original matrix's Hilbert--Schmidt square divided by `n^2`.

This is the scaled form of Tao--Vu Lemma A.2 used to obtain equation (27) in
the proof of Theorem 2.1:

`(1/n) sum_i |lambda_i(n^{-1/2} A)|^2 <= ‖A‖_HS^2 / n^2`.
-/
theorem normalizedEsdSecondMoment_le_hilbertSchmidtSq [Nonempty n]
    (A : Matrix n n ℂ) :
    realEsdTest (normalizedMatrix A) (fun z ↦ ‖z‖ ^ 2) ≤
      hilbertSchmidtSq A / (Fintype.card n : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < Fintype.card n := by
    exact_mod_cast Fintype.card_pos
  unfold realEsdTest realSpectralSum
  rw [div_le_iff₀ hn]
  calc
    ((eigenvalueMultiset (normalizedMatrix A)).map
          (fun z ↦ ‖z‖ ^ 2)).sum ≤
        hilbertSchmidtSq A / (Fintype.card n : ℝ) :=
      normalizedEigenvalueSecondMoment_le_hilbertSchmidtSq_div_dimension A
    _ = (hilbertSchmidtSq A / (Fintype.card n : ℝ) ^ 2) *
          (Fintype.card n : ℝ) := by
      field_simp

end TaoVuReplacement

