import BernoulliSection9.StrongRRQR
import BernoulliSection9.InterfaceControl
import BernoulliSection9.MatrixGramVolumeSingular
import Mathlib.Tactic

/-!
# Threshold spectral bridges for the concrete terminal assembly

These two lemmas eliminate the last hand-written spectral side conditions
from the RRQR/CUR assembly.  The cutoff is always the actual number of
singular values strictly above `tau`.
-/

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

/-- Every in-range singular value is bounded by the operator norm.  This is
the easy upper half of the min--max principle, recorded here because it
turns endpoint operator-norm control into uniform exterior-degree control. -/
theorem singularValue_le_operatorNorm
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Complex E]
    [NormedAddCommGroup F] [InnerProductSpace Complex F]
    [FiniteDimensional Complex E] [FiniteDimensional Complex F]
    (T : E →ₗ[Complex] F)
    (i : Fin (Module.finrank Complex E)) :
    T.singularValues i <= ‖T.toContinuousLinearMap‖ := by
  apply singularValue_le_of_submodule_bound T i
    (singularSpectralTail T i) ‖T.toContinuousLinearMap‖
    (finrank_singularSpectralTail T i)
  intro x _
  exact T.toContinuousLinearMap.le_opNorm x

/-- A rough but completely explicit operator-norm upper bound for Gram
volume.  Its deliberately generous factor is sufficient for the paper's
`exp (O(W log W))` endpoint estimate. -/
theorem gramVolume_le_two_mul_max_one_norm_pow
    {iota : Type*} [Fintype iota] [DecidableEq iota] [LinearOrder iota]
    (A : Matrix iota iota Complex) :
    BernoulliLinearAlgebra.gramVolume A <=
      (2 * max 1 ‖A‖) ^ Fintype.card iota := by
  rw [gramVolume_eq_singularGraph_normDet]
  let T := Matrix.toEuclideanLin A
  let tau : Real := max 1 ‖A‖
  have htau : 1 <= tau := le_max_left _ _
  have hlarge : ∀ i : Fin (Module.finrank Complex
      (EuclideanSpace Complex iota)), (i : Nat) < 0 ->
      tau < T.singularValues i := by
    intro i hi
    omega
  have hsmall : ∀ i : Fin (Module.finrank Complex
      (EuclideanSpace Complex iota)), 0 <= (i : Nat) ->
      T.singularValues i <= tau := by
    intro i _
    have h := singularValue_le_operatorNorm T i
    have hop : ‖T.toContinuousLinearMap‖ = ‖A‖ := by
      symm
      exact Matrix.cstar_norm_def A
    exact h.trans (hop.le.trans (le_max_right _ _))
  simpa [T, tau, largeSingularProduct, finrank_euclideanSpace] using
    (graph_normDet_le_threshold_factor_mul_largeSingularProduct
      T 0 tau htau hlarge hsmall)

/-- A positive RRQR pivot has inverse norm at most the fixed RRQR power
divided by the threshold.  No pivot certificate occurs here: `R` is the
output of the internally constructed strong RRQR theorem. -/
theorem strongRRQRPivot_inv_norm_le_pow_div_threshold
    {n r : Nat} (A : Matrix (Fin n) (Fin n) Complex) (tau : Real)
    (R : StrongRRQRConclusion A tau r) (hr : 0 < r)
    (htau : 1 <= tau) :
    ‖R.data.Kpiv⁻¹‖ <= (n : Real) ^ strongRRQRExponent / tau := by
  have hrEq : r = largeSingularValueCount A tau := by
    simpa [largeSingularValueCount, largeSingularValueIndices] using R.r_eq
  have hn : 0 < n := lt_of_lt_of_le hr R.r_le_n
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have htauPos : 0 < tau := zero_lt_one.trans_le htau
  let jlast : Fin r := ⟨r - 1, by omega⟩
  have hthreshold : tau <
      (Matrix.toEuclideanLin A).singularValues (r - 1) := by
    rw [hrEq]
    exact singularValue_pred_count_gt A tau (hrEq ▸ hr)
  have hpivot := R.pivot_singular_lower jlast
  have hmin : ((n : Real) ^ strongRRQRExponent)⁻¹ * tau <=
      matrixSMin R.data.Kpiv := by
    rw [matrixSMin, if_neg (Nat.ne_of_gt hr)]
    calc
      ((n : Real) ^ strongRRQRExponent)⁻¹ * tau <=
          ((n : Real) ^ strongRRQRExponent)⁻¹ *
            (Matrix.toEuclideanLin A).singularValues (r - 1) :=
        mul_le_mul_of_nonneg_left hthreshold.le (by positivity)
      _ <= (Matrix.toEuclideanLin R.data.Kpiv).singularValues
          (r - 1) := by
        simpa [jlast] using hpivot
  have hscalePos : 0 <
      ((n : Real) ^ strongRRQRExponent)⁻¹ * tau :=
    mul_pos (inv_pos.mpr (pow_pos hnReal _)) htauPos
  have hinv := norm_nonsing_inv_le_inv_of_le_matrixSMin hr R.data.Kpiv
    hscalePos hmin
  calc
    ‖R.data.Kpiv⁻¹‖ <=
        (((n : Real) ^ strongRRQRExponent)⁻¹ * tau)⁻¹ := hinv
    _ = (n : Real) ^ strongRRQRExponent / tau := by
      field_simp

/-- For the canonical threshold count, all preceding singular values are
strictly above `tau`. -/
theorem singularValue_gt_of_lt_largeSingularValueCount
    {n : Nat} (A : Matrix (Fin n) (Fin n) Complex) (tau : Real)
    (i : Fin n) (hi : (i : Nat) < largeSingularValueCount A tau) :
    tau < (Matrix.toEuclideanLin A).singularValues i := by
  have hr : 0 < largeSingularValueCount A tau := lt_of_le_of_lt (Nat.zero_le _) hi
  have hlast := singularValue_pred_count_gt A tau hr
  have hir : (i : Nat) <= largeSingularValueCount A tau - 1 := by omega
  exact hlast.trans_le
    ((Matrix.toEuclideanLin A).singularValues_antitone hir)

/-- For the canonical threshold count, every following singular value is
at most `tau`. -/
theorem singularValue_le_of_largeSingularValueCount_le
    {n : Nat} (A : Matrix (Fin n) (Fin n) Complex) (tau : Real)
    (i : Fin n) (hi : largeSingularValueCount A tau <= (i : Nat)) :
    (Matrix.toEuclideanLin A).singularValues i <= tau := by
  have hrlt : largeSingularValueCount A tau < n :=
    lt_of_le_of_lt hi i.isLt
  exact ((Matrix.toEuclideanLin A).singularValues_antitone hi).trans
    (singularValue_count_le A tau hrlt)

/-- The Gram volume is bounded by the large-singular-value product with no
caller-supplied `hlarge`/`hsmall` partition. -/
theorem gramVolume_le_threshold_factor_mul_canonicalLargeSingularProduct
    {n : Nat} (A : Matrix (Fin n) (Fin n) Complex) (tau : Real)
    (htau : 1 <= tau) :
    BernoulliLinearAlgebra.gramVolume A <=
      (2 * tau) ^ n *
        largeSingularProduct (Matrix.toEuclideanLin A)
          (largeSingularValueCount A tau) := by
  have hlarge : ∀ i : Fin
      (Module.finrank Complex (EuclideanSpace Complex (Fin n))),
      (i : Nat) < largeSingularValueCount A tau ->
        tau < (Matrix.toEuclideanLin A).singularValues i := by
    intro i hi
    simpa [finrank_euclideanSpace] using
      singularValue_gt_of_lt_largeSingularValueCount A tau
        (⟨i, by simpa [finrank_euclideanSpace] using i.isLt⟩ : Fin n) hi
  have hsmall : ∀ i : Fin
      (Module.finrank Complex (EuclideanSpace Complex (Fin n))),
      largeSingularValueCount A tau <= (i : Nat) ->
        (Matrix.toEuclideanLin A).singularValues i <= tau := by
    intro i hi
    simpa [finrank_euclideanSpace] using
      singularValue_le_of_largeSingularValueCount_le A tau
        (⟨i, by simpa [finrank_euclideanSpace] using i.isLt⟩ : Fin n) hi
  simpa using
    (gramVolume_le_threshold_factor_mul_matrixLargeSingularProduct
      A (largeSingularValueCount A tau) tau htau hlarge hsmall)

end BernoulliSection9
