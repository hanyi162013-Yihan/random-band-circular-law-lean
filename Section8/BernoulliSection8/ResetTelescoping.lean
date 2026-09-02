import BernoulliSection8.MatrixCappedReset
import BernoulliSection10.SandwichIntegrability
import BernoulliSection10.IntervalRestriction

/-! # Telescoping the actual matrix reset losses -/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection8

open BernoulliSection10

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Chronological order is reset, then core at each site. -/
def resetPrefixProduct (core reset : ℕ → Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => 1
  | n + 1 => core n * reset n * resetPrefixProduct core reset n

theorem reverseMatrixProduct_nat_succ (A : ℕ → Matrix ι ι ℂ) (K : ℕ) :
    reverseMatrixProduct (fun j : Fin (K + 1) => A j.1) =
      A K * reverseMatrixProduct (fun j : Fin K => A j.1) := by
  unfold reverseMatrixProduct
  rw [list_ofFn_fin_rev (fun j : Fin (K + 1) => A j.1),
    List.ofFn_succ_last, List.reverse_concat, List.prod_cons]
  simp only [Fin.val_last, Fin.val_castSucc]
  rw [list_ofFn_fin_rev (fun j : Fin K => A j.1)]

theorem reverseMatrixProduct_eq_resetPrefixProduct
    (core reset : ℕ → Matrix ι ι ℂ) (K : ℕ) :
    reverseMatrixProduct (fun j : Fin K => core j.1 * reset j.1) =
      resetPrefixProduct core reset K := by
  induction K with
  | zero => simp [reverseMatrixProduct, resetPrefixProduct]
  | succ K ih =>
    rw [reverseMatrixProduct_nat_succ (fun j => core j * reset j) K, ih, resetPrefixProduct]

theorem resetPrefixProduct_det_isUnit (core reset : ℕ → Matrix ι ι ℂ)
    {K : ℕ} (hcore : ∀ j < K, IsUnit (core j).det)
    (hreset : ∀ j < K, IsUnit (reset j).det) :
    IsUnit (resetPrefixProduct core reset K).det := by
  induction K with
  | zero => simp [resetPrefixProduct]
  | succ K ih =>
    simp only [resetPrefixProduct, Matrix.det_mul]
    exact ((hcore K (by omega)).mul (hreset K (by omega))).mul
      (ih (fun j hj => hcore j (by omega)) (fun j hj => hreset j (by omega)))

def prefixResetLoss (core reset : ℕ → Matrix ι ι ℂ) (T : ℝ) (j : ℕ) : ℝ :=
  cappedSpliceLoss T ‖core j‖ ‖resetPrefixProduct core reset j‖
    ‖resetPrefixProduct core reset (j + 1)‖

theorem resetPrefixProduct_log_lower (core reset : ℕ → Matrix ι ι ℂ)
    (K : ℕ) (T : ℝ)
    (hcore : ∀ j < K, IsUnit (core j).det)
    (hreset : ∀ j < K, IsUnit (reset j).det)
    (hcap : ∀ j < K, 2 * matrixHodgeLoss (core j) + matrixHodgeLoss (reset j) ≤ T) :
    (∑ j ∈ Finset.range K, Real.log ‖core j‖) -
      (∑ j ∈ Finset.range K, prefixResetLoss core reset T j) ≤
        Real.log ‖resetPrefixProduct core reset K‖ := by
  induction K with
  | zero => simp [resetPrefixProduct]
  | succ K ih =>
    have hprev := resetPrefixProduct_det_isUnit core reset (K := K)
      (fun j hj => hcore j (show j < K + 1 by omega))
      (fun j hj => hreset j (show j < K + 1 by omega))
    have hB : resetPrefixProduct core reset K ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mpr hprev).ne_zero
    have hone := matrix_log_product_ge_sub_cappedSpliceLoss (core K) (reset K)
      (resetPrefixProduct core reset K) (hcore K (by omega)) (hreset K (by omega))
      hB (hcap K (by omega))
    have hind := ih (fun j hj => hcore j (by omega)) (fun j hj => hreset j (by omega))
      (fun j hj => hcap j (by omega))
    simp only [Finset.sum_range_succ]
    change _ ≤ Real.log ‖core K * reset K * resetPrefixProduct core reset K‖
    simp only [prefixResetLoss, resetPrefixProduct] at hind ⊢
    linarith

theorem resetPrefixProduct_log_upper (core reset : ℕ → Matrix ι ι ℂ)
    (K : ℕ)
    (hcore : ∀ j < K, IsUnit (core j).det)
    (hreset : ∀ j < K, IsUnit (reset j).det) :
    Real.log ‖resetPrefixProduct core reset K‖ ≤
      (∑ j ∈ Finset.range K, Real.log ‖core j‖) +
        ∑ j ∈ Finset.range K, Real.log ‖reset j‖ := by
  induction K with
  | zero => simp [resetPrefixProduct]
  | succ K ih =>
    have hprev := resetPrefixProduct_det_isUnit core reset (K := K)
      (fun j hj => hcore j (show j < K + 1 by omega))
      (fun j hj => hreset j (show j < K + 1 by omega))
    have hone := log_norm_sandwich_upper (core K) (reset K)
      (resetPrefixProduct core reset K) (hcore K (by omega)) (hreset K (by omega)) hprev
    have hind := ih (fun j hj => hcore j (by omega)) (fun j hj => hreset j (by omega))
    simp only [resetPrefixProduct, Finset.sum_range_succ]
    linarith

end BernoulliSection8
