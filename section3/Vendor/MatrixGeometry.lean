/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/MatrixGeometry.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.NormalEvents

/-! The Hilbert--Schmidt cutoff gives the column bounds used by the net argument. -/

open scoped BigOperators
open Section5Formalization

namespace HighBandLSV.MatrixGeometry

theorem column_norm_le_hilbertSchmidt {N : Nat}
    (A : Matrix (Fin N) (Fin N) Complex) (j : Fin N) :
    ‖NormalEvents.col A j‖ ≤ hilbertSchmidt A := by
  have hcol : ‖NormalEvents.col A j‖ ^ 2 = ∑ i, ‖A i j‖ ^ 2 := by
    simpa only [NormalEvents.col] using
      PiLp.norm_sq_eq_of_L2 (fun _ : Fin N => Complex) (NormalEvents.col A j)
  have hsum : (∑ i, ‖A i j‖ ^ 2) ≤ ∑ i, ∑ k, ‖A i k‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun k _ => sq_nonneg ‖A i k‖) (Finset.mem_univ j)
  have hsum0 : 0 ≤ ∑ i, ∑ k, ‖A i k‖ ^ 2 := by positivity
  have hformula : hilbertSchmidt A = Real.sqrt (∑ i, ∑ k, ‖A i k‖ ^ 2) := by
    simp [hilbertSchmidt, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  have hhs : hilbertSchmidt A ^ 2 = ∑ i, ∑ k, ‖A i k‖ ^ 2 := by
    rw [hformula]
    exact Real.sq_sqrt hsum0
  have hhs0 : 0 ≤ hilbertSchmidt A := by rw [hformula]; exact Real.sqrt_nonneg _
  nlinarith [norm_nonneg (NormalEvents.col A j)]

theorem shifted_column {N : Nat} (A : Matrix (Fin N) (Fin N) Complex)
    (z : Complex) (j : Fin N) :
    NormalEvents.col (shifted A z) j = NormalEvents.col A j -
      z • EuclideanSpace.single j 1 := by
  ext i
  by_cases h : i = j
  · subst i
    simp [NormalEvents.col, shifted]
  · simp [NormalEvents.col, shifted, h, Ne.symm h]

theorem shifted_column_norm_le {N : Nat} (A : Matrix (Fin N) (Fin N) Complex)
    (z : Complex) (j : Fin N) :
    ‖NormalEvents.col (shifted A z) j‖ ≤ hilbertSchmidt A + ‖z‖ := by
  rw [shifted_column]
  calc
    ‖NormalEvents.col A j - z • EuclideanSpace.single j 1‖ ≤
        ‖NormalEvents.col A j‖ + ‖z • EuclideanSpace.single j 1‖ := norm_sub_le _ _
    _ = ‖NormalEvents.col A j‖ + ‖z‖ := by simp [norm_smul]
    _ ≤ hilbertSchmidt A + ‖z‖ := add_le_add (column_norm_le_hilbertSchmidt A j) le_rfl

theorem hs_cutoff_column_bound {N : Nat} (A : Matrix (Fin N) (Fin N) Complex)
    (z : Complex) {R Kz : Real} (hhs : hilbertSchmidt A ≤ R * Real.sqrt (N : Real))
    (hz : ‖z‖ ≤ Kz) : ∀ j, ‖NormalEvents.col (shifted A z) j‖ ≤ hsCap N R Kz := by
  intro j
  have hN : 1 ≤ N := by have hj := j.isLt; omega
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hs : 1 ≤ Real.sqrt (N : Real) :=
    (Real.le_sqrt (by norm_num) (by positivity)).2 (by simpa using hNr)
  have hKz : 0 ≤ Kz := (norm_nonneg _).trans hz
  apply (shifted_column_norm_le A z j).trans
  unfold hsCap
  nlinarith

theorem inner_shifted_column {N : Nat} (A : Matrix (Fin N) (Fin N) Complex)
    (z : Complex) (u : NormalEvents.Vec N) (j : Fin N) :
    inner Complex u (NormalEvents.col (shifted A z) j) =
      (∑ i, star (u i) * A i j) - star (u j) * z := by
  rw [shifted_column, inner_sub_right, inner_smul_right, NormalEvents.inner_col_eq]
  simp [EuclideanSpace.inner_single_right, mul_comm]

end HighBandLSV.MatrixGeometry

#print axioms HighBandLSV.MatrixGeometry.hs_cutoff_column_bound
#print axioms HighBandLSV.MatrixGeometry.inner_shifted_column

