import CircularLawSection6.NegativeMomentCutoff
import CircularLawSection6.SingularValueReindexing
import Vendor.SLT.MatrixInfra.CourantFischer
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # Ordered singular values and negative moments are measurable

The leading Gram eigenspace of one matrix and trailing Gram eigenspace of
another intersect nontrivially. Comparing their singular quotients proves
the operator-norm perturbation bound directly, including repeated and zero
singular values. No measurable choice of eigenvectors is used.
-/

open MeasureTheory Module ShortRingAnchor
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace CircularLawSection6

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

theorem singularValue_le_add_opNorm (T S : E →L[ℂ] F)
    {n : ℕ} (hn : finrank ℂ E = n) (i : Fin n) :
    T.toLinearMap.singularValues i ≤ S.toLinearMap.singularValues i + ‖T - S‖ := by
  let L : Submodule ℂ E := T.toLinearMap.isSymmetric_adjoint_comp_self.leadingEigenSubspace
    hn (Nat.succ_le_of_lt i.2)
  have hL : finrank ℂ L = i.1 + 1 := by
    simpa only [L] using T.toLinearMap.isSymmetric_adjoint_comp_self.finrank_leadingEigenSubspace
      hn (Nat.succ_le_of_lt i.2)
  obtain ⟨x, hxL, hxS, hx0⟩ :=
    S.toLinearMap.isSymmetric_adjoint_comp_self.exists_ne_zero_mem_inf_trailingEigenSubspace_of_finrank_eq_succ
      hn i L hL
  have hleft := LinearMap.singularValues_le_singularQuotient_of_mem_gram_leadingEigenSubspace
    T.toLinearMap hn i hxL hx0
  have hright := LinearMap.singularQuotient_le_singularValues_of_mem_gram_trailingEigenSubspace
    S.toLinearMap hn i hxS hx0
  have hnorm : ‖T x‖ ≤ ‖S x‖ + ‖T - S‖ * ‖x‖ := by
    calc
      ‖T x‖ = ‖S x + (T - S) x‖ := by simp
      _ ≤ ‖S x‖ + ‖(T - S) x‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl ((T - S).le_opNorm x)
  have hquot : LinearMap.singularQuotient T.toLinearMap x ≤
      LinearMap.singularQuotient S.toLinearMap x + ‖T - S‖ := by
    unfold LinearMap.singularQuotient
    apply (div_le_iff₀ (norm_pos_iff.mpr hx0)).2
    rw [add_mul, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx0)]
    exact hnorm
  exact hleft.trans (hquot.trans (add_le_add hright le_rfl))

theorem singularValue_lipschitz {n : ℕ} (hn : finrank ℂ E = n) (i : Fin n) :
    LipschitzWith 1 (fun T : E →L[ℂ] F => T.toLinearMap.singularValues i) := by
  apply LipschitzWith.of_dist_le_mul
  intro T S
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply abs_sub_le_iff.2
  have hTS := singularValue_le_add_opNorm T S hn i
  have hST := singularValue_le_add_opNorm S T hn i
  rw [norm_sub_rev S T] at hST
  constructor <;> linarith

set_option backward.isDefEq.respectTransparency false in
theorem continuous_matrix_singularValue
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i : Fin (Fintype.card ι)) :
    Continuous (fun A : Matrix ι ι ℂ => A.toEuclideanLin.singularValues i) := by
  have hCLM : Continuous (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) :=
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  have hLip : LipschitzWith 1 (fun T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι =>
      T.toLinearMap.singularValues i) :=
    singularValue_lipschitz (E := EuclideanSpace ℂ ι) (F := EuclideanSpace ℂ ι)
      (finrank_euclideanSpace (𝕜 := ℂ) (ι := ι)) i
  simpa only [Function.comp_def, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
    hLip.continuous.comp hCLM

theorem measurable_matrixNegativeMoment
    {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) :
    Measurable (fun A : Matrix ι ι ℂ => matrixNegativeMoment A p) := by
  unfold matrixNegativeMoment normalizedNegativeMoment empiricalAverage
  apply Measurable.div_const
  exact Finset.measurable_sum _ fun i _ =>
    (continuous_matrix_singularValue i).measurable.pow_const (-p)

theorem matrixNegativeMoment_reindex
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℂ) (p : ℝ) :
    matrixNegativeMoment (A.submatrix e.symm e.symm) p = matrixNegativeMoment A p := by
  unfold matrixNegativeMoment normalizedNegativeMoment empiricalAverage
  have hcard : Fintype.card κ = Fintype.card ι := (Fintype.card_congr e).symm
  simp only [Fintype.card_fin]
  refine congrArg₂ (fun x y : ℝ => x / y) ?_ (by exact_mod_cast hcard)
  apply Fintype.sum_equiv (finCongr hcard)
  intro i
  change (A.submatrix e.symm e.symm).toEuclideanLin.singularValues i ^ (-p) =
    A.toEuclideanLin.singularValues i ^ (-p)
  rw [matrix_singularValues_reindex]

end CircularLawSection6
