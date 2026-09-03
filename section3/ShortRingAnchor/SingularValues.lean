import ShortRingAnchor.SourceStatement
import ShortRingAnchor.LogDecomposition
import ShortRingAnchor.ProbabilityModes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# Singular values and the logarithmic determinant

This file proves the finite-dimensional algebraic bridge used throughout the
proof of Proposition 3.6.  It is not an external random-matrix input: the
absolute determinant is the product of the singular values, and hence its
logarithm is their logarithmic sum whenever the shifted matrix is nonsingular.
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

namespace ShortRingAnchor

open Module InnerProductSpace MeasureTheory

/-- The `j`-th singular value of a complex square matrix, in decreasing and
zero-indexed order. -/
def matrixSingularValue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (j : ℕ) : ℝ :=
  A.toEuclideanLin.singularValues j

theorem matrixSingularValue_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) :
    0 <= matrixSingularValue A j :=
  A.toEuclideanLin.singularValues_nonneg j

/-- Exact deterministic singular-value product formula. -/
theorem norm_det_eq_prod_matrixSingularValue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ = ∏ j ∈ Finset.range n, matrixSingularValue A j := by
  let T := A.toEuclideanLin
  have hdet : T.normDet = ‖A.det‖ := by
    simpa [T, Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      (T.normDet_eq_norm_det_toMatrix
        (EuclideanSpace.basisFun (Fin n) ℂ)
        (EuclideanSpace.basisFun (Fin n) ℂ))
  rw [← hdet, LinearMap.normDet_eq_prod_singularValues]
  simp [matrixSingularValue, T]

/-- Taking logarithms of the preceding product is sound on the nonsingular
event.  The premise is essential because `Real.log 0 = 0` in Lean. -/
theorem log_norm_det_eq_sum_log_matrixSingularValue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hdet : A.det ≠ 0) :
    Real.log ‖A.det‖ =
      ∑ j ∈ Finset.range n, Real.log (matrixSingularValue A j) := by
  rw [norm_det_eq_prod_matrixSingularValue]
  apply Real.log_prod
  have hprod : (∏ j ∈ Finset.range n, matrixSingularValue A j) ≠ 0 := by
    rw [← norm_det_eq_prod_matrixSingularValue]
    exact norm_ne_zero_iff.mpr hdet
  exact Finset.prod_ne_zero_iff.mp hprod

/-- Singular value of the shifted matrix in Proposition 3.6. -/
def shiftedSingularValue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (j : ℕ) : ℝ :=
  matrixSingularValue (A - z • (1 : Matrix (Fin n) (Fin n) ℂ)) j

theorem shiftedSingularValue_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (j : ℕ) :
    0 <= shiftedSingularValue A z j :=
  matrixSingularValue_nonneg _ _

/-- The shifted singular values as an `n`-element finite family. -/
def shiftedSingularValueFamily {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : Fin n -> ℝ :=
  fun j => shiftedSingularValue A z j.val

/-- Singular-value families for a dimension-varying random matrix sequence. -/
def shiftedSingularValueProcess
    {Omega : Type*} {M : Nat -> Nat}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) : forall n, Omega -> Fin (M n) -> Real :=
  fun n omega => shiftedSingularValueFamily (A n omega) z

/-- A strictly positive representative of the shifted singular-value family.
On a singular sample it is set to the constant family `1`; on every
nonsingular sample it is the genuine family.  This is the convenient way to
respect Lean's total convention `Real.log 0 = 0` while changing nothing in
probability when singular samples form a null set. -/
noncomputable def positiveShiftedSingularValueProcess
    {Omega : Type*} {M : Nat -> Nat}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) : forall n, Omega -> Fin (M n) -> Real :=
  fun n omega i =>
    if (A n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0 then
      shiftedSingularValueFamily (A n omega) z i
    else 1

theorem shiftedSingularValueFamily_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (j : Fin n) :
    0 <= shiftedSingularValueFamily A z j :=
  shiftedSingularValue_nonneg A z j.val

/-- Nonsingularity makes every member of the shifted singular-value family
strictly positive.  This supplies the positivity premise used by the
low/middle/high logarithmic decomposition. -/
theorem shiftedSingularValueFamily_pos_of_det_ne_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (hdet : (A - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det ≠ 0)
    (j : Fin n) :
    0 < shiftedSingularValueFamily A z j := by
  have hprod :
      (∏ k ∈ Finset.range n,
        matrixSingularValue
          (A - z • (1 : Matrix (Fin n) (Fin n) ℂ)) k) ≠ 0 := by
    rw [← norm_det_eq_prod_matrixSingularValue]
    exact norm_ne_zero_iff.mpr hdet
  have hjne : shiftedSingularValueFamily A z j ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mp hprod j.val (Finset.mem_range.mpr j.isLt)
  exact lt_of_le_of_ne (shiftedSingularValueFamily_nonneg A z j) hjne.symm

theorem positiveShiftedSingularValueProcess_pos
    {Omega : Type*} {M : Nat -> Nat}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (n : Nat) (omega : Omega) (i : Fin (M n)) :
    0 < positiveShiftedSingularValueProcess A z n omega i := by
  by_cases hdet : (A n omega - z •
      (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0
  · unfold positiveShiftedSingularValueProcess
    rw [if_pos hdet]
    exact shiftedSingularValueFamily_pos_of_det_ne_zero
      (A n omega) z hdet i
  · unfold positiveShiftedSingularValueProcess
    rw [if_neg hdet]
    exact zero_lt_one

/-- The positive representative equals the genuine singular-value process
almost everywhere whenever the shifted determinant is nonzero almost
everywhere. -/
theorem positiveShiftedSingularValueProcess_ae_eq
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ)
    (hdet : forall n, ∀ᵐ omega ∂mu,
      (A n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0) :
    forall n,
      (positiveShiftedSingularValueProcess A z n) =ᵐ[mu]
        shiftedSingularValueProcess A z n := by
  intro n
  filter_upwards [hdet n] with omega homega
  funext i
  simp [positiveShiftedSingularValueProcess, shiftedSingularValueProcess,
    homega]

/-- Formula (3.8), rewritten as the empirical logarithmic singular-value
average on the nonsingular event. -/
theorem normalizedShiftLogDet_eq_singularValueAverage {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (hdet : (A - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det ≠ 0) :
    normalizedShiftLogDet A z =
      (∑ j : Fin n, Real.log (shiftedSingularValue A z j)) / (n : ℝ) := by
  rw [normalizedShiftLogDet,
    log_norm_det_eq_sum_log_matrixSingularValue _ hdet]
  rw [← Fin.sum_univ_eq_sum_range]
  simp [shiftedSingularValue]

/-- Formula (3.8) in the empirical-average notation used by the truncation
modules. -/
theorem normalizedShiftLogDet_eq_empiricalLog_shiftedSingularValues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (hdet : (A - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det ≠ 0) :
    normalizedShiftLogDet A z =
      empiricalLog (shiftedSingularValueFamily A z) := by
  rw [normalizedShiftLogDet_eq_singularValueAverage A z hdet]
  simp [empiricalLog, empiricalAverage, shiftedSingularValueFamily]

/-- Almost-everywhere determinant/singular-log identity for the positive
representative. -/
theorem normalizedShiftLogDet_ae_eq_empiricalLog_positiveProcess
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ)
    (hdet : forall n, ∀ᵐ omega ∂mu,
      (A n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0) :
    forall n,
      (fun omega => normalizedShiftLogDet (A n omega) z) =ᵐ[mu]
        (fun omega => empiricalLog
          (positiveShiftedSingularValueProcess A z n omega)) := by
  intro n
  filter_upwards [hdet n] with omega homega
  rw [normalizedShiftLogDet_eq_empiricalLog_shiftedSingularValues
    (A n omega) z homega]
  congr 1
  funext i
  simp [positiveShiftedSingularValueProcess, homega]

/-- Transfer a convergence theorem for the singular-value logarithmic
average to the normalized shifted log determinant. -/
theorem normalizedShiftLogDet_convergesInProbability_of_singularValues
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} [forall n, Nonempty (Fin (M n))]
    {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (limit : Real)
    (hdet : forall n omega,
      (A n omega - z • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (hlog : ConvergesInProbability mu
      (fun n omega => empiricalLog (shiftedSingularValueProcess A z n omega))
      limit) :
    ConvergesInProbability mu
      (fun n omega => normalizedShiftLogDet (A n omega) z) limit := by
  have hfun :
      (fun n omega => normalizedShiftLogDet (A n omega) z) =
        (fun n omega =>
          empiricalLog (shiftedSingularValueProcess A z n omega)) := by
    funext n omega
    exact normalizedShiftLogDet_eq_empiricalLog_shiftedSingularValues
      (A n omega) z (hdet n omega)
  rw [hfun]
  exact hlog

/-- Almost-everywhere version of the preceding convergence transfer. -/
theorem normalizedShiftLogDet_convergesInProbability_of_positiveProcess
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat -> Nat} {mu : Measure Omega}
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (limit : Real)
    (hdet : forall n, ∀ᵐ omega ∂mu,
      (A n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (hlog : ConvergesInProbability mu
      (fun n omega => empiricalLog
        (positiveShiftedSingularValueProcess A z n omega)) limit) :
    ConvergesInProbability mu
      (fun n omega => normalizedShiftLogDet (A n omega) z) limit := by
  unfold ConvergesInProbability at hlog ⊢
  exact hlog.congr_left fun n =>
    (normalizedShiftLogDet_ae_eq_empiricalLog_positiveProcess
      A z hdet n).symm

end ShortRingAnchor
