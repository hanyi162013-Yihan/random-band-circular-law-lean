import CircularLawSection6.MatrixCutoffComparison
import Mathlib.Analysis.InnerProductSpace.NormDet

/-! # Actual determinant/singular-log identity and fixed scaling

These formulas use the existing norm-determinant product theorem.
Nonsingularity is retained exactly where `Real.log 0 = 0` prevents a
pointwise logarithmic product or scaling formula.
-/

open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixRawPotential (A : Matrix ι ι ℂ) : ℝ :=
  Real.log ‖A.det‖ / (Fintype.card ι : ℝ)

theorem matrix_norm_det_eq_prod_singularValues (A : Matrix ι ι ℂ) :
    ‖A.det‖ = ∏ i ∈ Finset.range (Fintype.card ι), A.toEuclideanLin.singularValues i := by
  have hn : A.toEuclideanLin.normDet = ‖A.det‖ := by
    rw [LinearMap.normDet_eq_norm_det]
    exact congrArg norm (LinearMap.det_toLpLin 2 A)
  rw [← hn, LinearMap.normDet_eq_prod_singularValues]
  simp only [finrank_euclideanSpace]

theorem matrix_log_norm_det_eq_sum_log_singularValues
    (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) :
    Real.log ‖A.det‖ = ∑ i : Fin (Fintype.card ι), Real.log (A.toEuclideanLin.singularValues i) := by
  rw [matrix_norm_det_eq_prod_singularValues]
  have hprod : (∏ i ∈ Finset.range (Fintype.card ι), A.toEuclideanLin.singularValues i) ≠ 0 := by
    rw [← matrix_norm_det_eq_prod_singularValues]
    exact norm_ne_zero_iff.mpr hA
  rw [Real.log_prod (Finset.prod_ne_zero_iff.mp hprod), ← Fin.sum_univ_eq_sum_range]

theorem matrixRawPotential_le_cutoff
    (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) (a : ℝ) :
    matrixRawPotential A ≤ matrixCutoffPotential A a := by
  have hsum : (∑ i : Fin (Fintype.card ι), Real.log (A.toEuclideanLin.singularValues i)) ≤
      ∑ i : Fin (Fintype.card ι), Real.log (max (A.toEuclideanLin.singularValues i) a) := by
    apply Finset.sum_le_sum
    intro i _
    apply Real.log_le_log
    · exact A.toEuclideanLin.injective_iff_forall_lt_finrank_singularValues_pos.mp
        (toEuclideanLin_injective_of_det_ne_zero A hA) i
        (by simpa only [finrank_euclideanSpace] using i.isLt)
    · exact le_max_left _ _
  have h := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (α := ℝ) (Fintype.card ι))
  have hindex : (∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)),
      Real.log (max (A.toEuclideanLin.singularValues i) a)) =
      ∑ i : Fin (Fintype.card ι), Real.log (max (A.toEuclideanLin.singularValues i) a) :=
    Fintype.sum_equiv (finCongr (finrank_euclideanSpace (𝕜 := ℂ) (ι := ι))) _ _ (fun _ => rfl)
  unfold matrixRawPotential matrixCutoffPotential operatorCutoffPotential
  rw [matrix_log_norm_det_eq_sum_log_singularValues A hA, hindex, finrank_euclideanSpace]
  exact h

theorem matrixRawPotential_smul [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) {r : ℝ} (hr : 0 < r) :
    matrixRawPotential ((r : ℂ) • A) = Real.log r + matrixRawPotential A := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
  unfold matrixRawPotential
  rw [Matrix.det_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr, Real.log_mul (pow_ne_zero _ hr.ne') (norm_ne_zero_iff.mpr hA), Real.log_pow]
  field_simp

theorem matrixRawPotential_shifted_smul [Nonempty ι]
    (A : Matrix ι ι ℂ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hA : (A - (z / (r : ℂ)) • 1).det ≠ 0) :
    matrixRawPotential ((r : ℂ) • A - z • 1) =
      Real.log r + matrixRawPotential (A - (z / (r : ℂ)) • 1) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hm : (r : ℂ) • A - z • 1 = (r : ℂ) • (A - (z / (r : ℂ)) • 1) := by
    rw [smul_sub, smul_smul]
    congr 2
    field_simp
  rw [hm, matrixRawPotential_smul _ hA hr]

end CircularLawSection6
