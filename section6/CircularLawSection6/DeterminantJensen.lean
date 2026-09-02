import CircularLawSection6.PolynomialJensen
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-! # Jensen's lower bound for the literal core-plus-tail determinant

The matrix `A` is the shifted core `Y - zI`, and `B` is the discarded tail.
No Gaussian, independence, or expectation assumption is needed for this
deterministic phase-average inequality. Those enter only when averaging it
over the matrix realizations.
-/

open Polynomial MeasureTheory Set Real

namespace CircularLawSection6

noncomputable def affineDeterminantPolynomial
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) : ℂ[X] :=
  ((X : ℂ[X]) • B.map C + A.map C).det

theorem affineDeterminantPolynomial_eval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (w : ℂ) :
    (affineDeterminantPolynomial A B).eval w = (w • B + A).det := by
  change (evalRingHom w) (((X : ℂ[X]) • B.map C + A.map C).det) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp
  exact mul_comm _ _

@[simp]
theorem affineDeterminantPolynomial_eval_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) :
    (affineDeterminantPolynomial A B).eval 0 = A.det := by
  simp [affineDeterminantPolynomial_eval]

theorem affineDeterminantPolynomial_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.det ≠ 0) :
    affineDeterminantPolynomial A B ≠ 0 := by
  intro h
  have := affineDeterminantPolynomial_eval_zero A B
  simp only [h, eval_zero] at this
  exact hA this.symm

theorem log_norm_affine_det_circleIntegrable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (r : ℝ) :
    CircleIntegrable (fun w => Real.log ‖(w • B + A).det‖) 0 r := by
  simpa only [affineDeterminantPolynomial_eval] using
    polynomial_log_circleIntegrable (affineDeterminantPolynomial A B) r

theorem log_norm_det_le_circleAverage_affine_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.det ≠ 0) :
    Real.log ‖A.det‖ ≤ circleAverage (fun w => Real.log ‖(w • B + A).det‖) 0 1 := by
  simpa only [polynomialCircleMean, affineDeterminantPolynomial_eval,
    zero_smul, zero_add] using
    log_norm_eval_zero_le_polynomialCircleMean (affineDeterminantPolynomial A B)
      (by simpa only [affineDeterminantPolynomial_eval_zero] using hA)

/-- The exact normalized deterministic inequality used before the tail's
rotation-invariant law is used to remove the phase average. -/
theorem normalized_log_norm_det_le_circleAverage_affine_det
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0) :
    Real.log ‖A.det‖ / (n : ℝ) ≤
      circleAverage (fun w => Real.log ‖(w • B + A).det‖) 0 1 / (n : ℝ) := by
  exact div_le_div_of_nonneg_right
    (log_norm_det_le_circleAverage_affine_det A B hA) (Nat.cast_nonneg n)

end CircularLawSection6
