import CircularLawSection6.AffineLogFromDiagonal
import CircularLawSection6.RowResamplingClosure
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Actual determinant row fibers

Cofactors are encoded by the existing adjugate/Cramer identities. Freezing
one row to zero gives a center depending only on the other rows, and the
Section 4 affine-log estimate applies to its exact determinant expression.
-/

open MeasureTheory ProbabilityTheory CircularLawSection4
open scoped BigOperators ENNReal

noncomputable section

namespace CircularLawSection6

def weightedRowsMatrix {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ)
    (rows : Fin n → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => b i j * rows i j

def weightedRowsLogDet {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (rows : Fin n → Fin n → ℂ) : ℝ :=
  Real.log ‖(weightedRowsMatrix b rows - z • 1).det‖

theorem weightedRowsLogDet_measurable {n : ℕ}
    (b : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : Measurable (weightedRowsLogDet b z) := by
  apply Real.measurable_log.comp
  have hc : Continuous (fun rows : Fin n → Fin n → ℂ =>
      (weightedRowsMatrix b rows - z • 1).det) := by
    unfold weightedRowsMatrix
    fun_prop
  exact hc.norm.measurable

def rowCofactorOperator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) : ℂ →L[ℂ] ℂ := A.adjugate j i • ContinuousLinearMap.id ℂ ℂ

theorem det_updateRow_affine {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (b η : Fin n → ℂ) (z : ℂ) :
    (A.updateRow i (fun j => b j * η j - if i = j then z else 0)).det =
      (∑ j, (b j * η j) * A.adjugate j i) - z * A.adjugate i i := by
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
    Matrix.adjugate_transpose]
  simp [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib,
    mul_ite, mul_comm, mul_left_comm, mul_assoc]

theorem norm_operatorAffine_cofactor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (b η : Fin n → ℂ) (z : ℂ) :
    ‖operatorAffine b η (rowCofactorOperator A i) z (rowCofactorOperator A i i)‖ =
      ‖(A.updateRow i (fun j => b j * η j - if i = j then z else 0)).det‖ := by
  unfold operatorAffine rowCofactorOperator
  simp only [smul_smul]
  rw [← Finset.sum_smul, ← sub_smul, norm_smul, ContinuousLinearMap.norm_id, mul_one,
    det_updateRow_affine]

theorem weightedRowsMatrix_update {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ)
    (rows : Fin n → Fin n → ℂ) (i : Fin n) (η : Fin n → ℂ) (z : ℂ) :
    weightedRowsMatrix b (Function.update rows i η) - z • 1 =
      (weightedRowsMatrix b rows - z • 1).updateRow i
        (fun j => b i j * η j - if i = j then z else 0) := by
  ext k j
  by_cases hk : k = i
  · subst k
    by_cases hj : i = j <;>
      simp [weightedRowsMatrix, Matrix.updateRow, Matrix.one_apply, hj]
  · simp [weightedRowsMatrix, Matrix.updateRow, hk, Ne.symm hk]

def frozenRowMatrix {n : ℕ} (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (z : ℂ) (i : Fin (n + 1)) (y : Fin n → Fin (n + 1) → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  weightedRowsMatrix b (i.insertNth 0 y) - z • 1

def rowLogCenter {n : ℕ} (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (z : ℂ) (i : Fin (n + 1)) (y : Fin n → Fin (n + 1) → ℂ) : ℝ :=
  Real.log (operatorAffineScale i (b i) (rowCofactorOperator (frozenRowMatrix b z i y) i))

theorem weightedRowsLogDet_insertNth {n : ℕ}
    (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (z : ℂ)
    (i : Fin (n + 1)) (y : Fin n → Fin (n + 1) → ℂ) (η : Fin (n + 1) → ℂ) :
    weightedRowsLogDet b z (i.insertNth η y) =
      Real.log ‖operatorAffine (b i) η (rowCofactorOperator (frozenRowMatrix b z i y) i)
        z (rowCofactorOperator (frozenRowMatrix b z i y) i i)‖ := by
  rw [norm_operatorAffine_cofactor]
  unfold weightedRowsLogDet frozenRowMatrix
  rw [← weightedRowsMatrix_update, Fin.update_insertNth]

theorem weightedRowsLogDet_fiber {n : ℕ}
    (ν : Measure ℂ) [IsProbabilityMeasure ν] {L : ℝ}
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (z : ℂ)
    (i : Fin (n + 1)) (y : Fin n → Fin (n + 1) → ℂ)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hb : q ≤ ‖b i i‖)
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    MemLp (fun η => weightedRowsLogDet b z (i.insertNth η y) - rowLogCenter b z i y)
      2 (iidMeasure ν (n + 1)) ∧
    (∫ η, (weightedRowsLogDet b z (i.insertNth η y) - rowLogCenter b z i y) ^ 2
      ∂iidMeasure ν (n + 1)) ≤ affineRowLogBound n q L z := by
  have h := complex_affine_log_memLp_of_diagonal_all_scales ν hν hL i (b i)
    (rowCofactorOperator (frozenRowMatrix b z i y) i) z hq hq1 hb hInt hSecond
  have hm : Measurable (fun η => weightedRowsLogDet b z (i.insertNth η y) - rowLogCenter b z i y) :=
    ((weightedRowsLogDet_measurable b z).comp (measurable_fin_insertNth_left i y)).sub_const _
  constructor
  · apply (memLp_norm_iff hm.aestronglyMeasurable).1
    simpa only [weightedRowsLogDet_insertNth, rowLogCenter, Real.norm_eq_abs] using h.1
  · simpa only [weightedRowsLogDet_insertNth, rowLogCenter, sq_abs] using h.2

theorem weightedRowsLogDet_memLp_and_variance {n : ℕ}
    (ν : Measure ℂ) [IsProbabilityMeasure ν] {L : ℝ}
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (z : ℂ)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hb : ∀ i, q ≤ ‖b i i‖)
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    MemLp (weightedRowsLogDet b z) 2 (iidMeasure (iidMeasure ν (n + 1)) (n + 1)) ∧
      variance (weightedRowsLogDet b z) (iidMeasure (iidMeasure ν (n + 1)) (n + 1)) ≤
        2 * (n + 1 : ℝ) * affineRowLogBound n q L z := by
  let : IsProbabilityMeasure (iidMeasure ν (n + 1)) := iidMeasure_isProbability ν (n + 1)
  exact memLp_and_variance_le_of_uniform_fibers (iidMeasure ν (n + 1))
    (weightedRowsLogDet b z) (weightedRowsLogDet_measurable b z) (rowLogCenter b z)
    (affineRowLogBound n q L z)
    (fun i y => (weightedRowsLogDet_fiber ν hν hL b z i y hq hq1 (hb i) hInt hSecond).1)
    (fun i y => (weightedRowsLogDet_fiber ν hν hL b z i y hq hq1 (hb i) hInt hSecond).2)

end CircularLawSection6
