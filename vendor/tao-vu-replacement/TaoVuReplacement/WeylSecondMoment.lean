import TaoVuReplacement.EmpiricalSpectrum
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Weyl comparison for the spectral second moment

This file reconstructs Tao--Vu, Lemma A.2, in the exact strength used in the
proof of Theorem 2.1:

`sum_i |lambda_i(A)|^2 <= sum_{i,j} |A i j|^2`.

The proof follows the source: first put the operator in upper-triangular form
in an orthonormal basis (finite-dimensional complex Schur triangularization),
then retain only the diagonal terms of the Hilbert--Schmidt sum.
-/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace TaoVuReplacement

open Matrix Polynomial Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The square of the Hilbert--Schmidt/Frobenius norm, written without
choosing one of mathlib's competing matrix norm instances. -/
def hilbertSchmidtSq (A : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem hilbertSchmidtSq_nonneg (A : Matrix n n ℂ) :
    0 ≤ hilbertSchmidtSq A := by
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- For an upper-triangular complex matrix, the roots of the characteristic
polynomial, with algebraic multiplicity, are exactly the diagonal entries.
This is the triangular step in Tao--Vu Lemma A.2. -/
theorem eigenvalueMultiset_eq_diag_of_isUpperTriangular [LinearOrder n]
    (A : Matrix n n ℂ) (hA : A.IsUpperTriangular) :
    eigenvalueMultiset A =
      ((Finset.univ : Finset n).val.map fun i ↦ A i i) := by
  rw [eigenvalueMultiset, Matrix.charpoly_of_isUpperTriangular A hA]
  rw [Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Polynomial.X_sub_C_ne_zero _

/-- The spectral second moment of an upper-triangular matrix is its diagonal
square sum. -/
theorem eigenvalueSecondMoment_eq_diag_of_isUpperTriangular [LinearOrder n]
    (A : Matrix n n ℂ) (hA : A.IsUpperTriangular) :
    ((eigenvalueMultiset A).map fun z ↦ ‖z‖ ^ 2).sum =
      ∑ i, ‖A i i‖ ^ 2 := by
  rw [eigenvalueMultiset_eq_diag_of_isUpperTriangular A hA]
  simp

/-- Keeping the diagonal terms can only decrease the Hilbert--Schmidt square
sum. -/
theorem diagonalSecondMoment_le_hilbertSchmidtSq (A : Matrix n n ℂ) :
    (∑ i, ‖A i i‖ ^ 2) ≤ hilbertSchmidtSq A := by
  unfold hilbertSchmidtSq
  apply Finset.sum_le_sum
  intro i hi
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖A i j‖) (Finset.mem_univ i)

/-! ## Finite-dimensional complex Schur triangularization -/

section Schur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Matrix coefficients in an orthonormal basis are inner products. -/
theorem toMatrix_orthonormalBasis_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : Module.End ℂ E) (i j : ι) :
    LinearMap.toMatrix b.toBasis b.toBasis T i j = ⟪b i, T (b j)⟫_ℂ := by
  rw [LinearMap.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply,
    b.repr_apply_apply]

private theorem exists_schur_orthonormalBasis_of_finrank
    (d : ℕ) (hd : finrank ℂ E = d) (T : Module.End ℂ E) :
    ∃ b : OrthonormalBasis (Fin d) ℂ E,
      (LinearMap.toMatrix b.toBasis b.toBasis T).IsUpperTriangular := by
  induction d using Nat.strong_induction_on generalizing E with
  | h d ih =>
      rcases d with _ | d
      · let b : OrthonormalBasis (Fin 0) ℂ E :=
          (stdOrthonormalBasis ℂ E).reindex (finCongr hd)
        refine ⟨b, ?_⟩
        intro i
        exact Fin.elim0 i
      · have hpos : 0 < finrank ℂ E := by simpa [hd]
        letI : Nontrivial E := finrank_pos_iff.mp hpos
        obtain ⟨mu, hmu⟩ := Module.End.exists_eigenvalue T
        obtain ⟨v, hv⟩ := hmu.exists_hasEigenvector
        let u : E := ((‖v‖ : ℂ)⁻¹) • v
        have hu_ne : u ≠ 0 := by
          simp [u, hv.2]
        have hu_norm : ‖u‖ = 1 := by
          simp [u, norm_smul, hv.2]
        have hTu : T u = mu • u := by
          simp [u, hv.apply_eq_smul, smul_smul, mul_comm]
        let K : Submodule ℂ E := ℂ ∙ u
        let Tperp : Module.End ℂ Kᗮ :=
          Kᗮ.orthogonalProjectionOnto.toLinearMap.comp (T.comp Kᗮ.subtype)
        letI : Fact (finrank ℂ E = d + 1) := ⟨hd⟩
        have hperp : finrank ℂ Kᗮ = d := by
          simpa [K] using
            (Submodule.finrank_orthogonal_span_singleton (𝕜 := ℂ) hu_ne)
        obtain ⟨bp, hbp⟩ := ih d (Nat.lt_succ_self d) hperp Tperp
        let q : Fin (d + 1) → E := Matrix.vecCons u (fun i ↦ (bp i : E))
        have huK : u ∈ K := by
          exact Submodule.mem_span_singleton_self u
        have hu_orth : ∀ i, ⟪u, (bp i : E)⟫_ℂ = 0 := by
          intro i
          exact K.inner_right_of_mem_orthogonal huK (bp i).property
        have hq : Orthonormal ℂ q := by
          change Orthonormal ℂ (Matrix.vecCons u (fun i ↦ (bp i : E)))
          rw [orthonormal_vecCons_iff]
          refine ⟨hu_norm, hu_orth, ?_⟩
          change Orthonormal ℂ (Kᗮ.subtypeₗᵢ ∘ (bp : Fin d → Kᗮ))
          exact bp.orthonormal.comp_linearIsometry Kᗮ.subtypeₗᵢ
        have hspan : Submodule.span ℂ (Set.range q) = ⊤ := by
          apply hq.linearIndependent.span_eq_top_of_card_eq_finrank
          simp [hd]
        let b : OrthonormalBasis (Fin (d + 1)) ℂ E :=
          OrthonormalBasis.mk hq hspan.ge
        refine ⟨b, ?_⟩
        intro i j
        change j < i → _
        revert j
        refine Fin.cases ?_ (fun i' ↦ ?_) i
        · intro j hji
          exact (Fin.not_lt_zero j hji).elim
        · intro j
          refine Fin.cases ?_ (fun j' ↦ ?_) j
          · intro _hji
            rw [toMatrix_orthonormalBasis_apply]
            simp only [b, OrthonormalBasis.coe_mk, q, Matrix.cons_val_succ,
              Matrix.cons_val_zero, hTu, inner_smul_right]
            rw [K.inner_left_of_mem_orthogonal huK (bp i').property]
            simp
          · intro hji
            have hji' : j' < i' := Fin.succ_lt_succ_iff.mp hji
            have hc := hbp hji'
            rw [toMatrix_orthonormalBasis_apply] at hc
            rw [toMatrix_orthonormalBasis_apply]
            simp only [b, OrthonormalBasis.coe_mk, q, Matrix.cons_val_succ]
            rw [← Kᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
              (bp i') (T (bp j' : E))]
            simpa [Tperp, LinearMap.comp_apply] using hc

/-- Schur triangularization over `ℂ`, with an orthonormal basis indexed in the
standard order.  This is the Jordan-plus-QR reduction used in the proof of
Tao--Vu Lemma A.2, reconstructed directly by induction. -/
theorem exists_schur_orthonormalBasis (T : Module.End ℂ E) :
    ∃ b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E,
      (LinearMap.toMatrix b.toBasis b.toBasis T).IsUpperTriangular :=
  exists_schur_orthonormalBasis_of_finrank (finrank ℂ E) rfl T

/-! ## Basis invariance of the Hilbert--Schmidt square -/

/-- Basis-free Hilbert--Schmidt square, expressed as `Re trace(T* T)`. -/
def operatorHilbertSchmidtSq (T : Module.End ℂ E) : ℝ :=
  RCLike.re ((T.adjoint.comp T).trace ℂ E)

/-- In any orthonormal basis, the entrywise square sum of the representing
matrix is `Re trace(T* T)`. -/
theorem hilbertSchmidtSq_toMatrix_orthonormalBasis {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ E)
    (T : Module.End ℂ E) :
    hilbertSchmidtSq (LinearMap.toMatrix b.toBasis b.toBasis T) =
      operatorHilbertSchmidtSq T := by
  unfold hilbertSchmidtSq
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ i, ‖LinearMap.toMatrix b.toBasis b.toBasis T i j‖ ^ 2) =
        ∑ j, ‖T (b j)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _hj
      simp_rw [toMatrix_orthonormalBasis_apply]
      exact b.sum_sq_norm_inner_right (T (b j))
    _ = operatorHilbertSchmidtSq T := by
      unfold operatorHilbertSchmidtSq
      rw [LinearMap.trace_eq_sum_inner (T.adjoint.comp T) b, map_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
        inner_self_eq_norm_sq_to_K]
      exact (RCLike.re_ofReal_pow (K := ℂ) ‖T (b j)‖ 2).symm

/-- The entrywise Hilbert--Schmidt square is unchanged when the same operator
is represented in two orthonormal bases. -/
theorem hilbertSchmidtSq_toMatrix_orthonormalBasis_eq
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ E)
    (T : Module.End ℂ E) :
    hilbertSchmidtSq (LinearMap.toMatrix b.toBasis b.toBasis T) =
      hilbertSchmidtSq (LinearMap.toMatrix c.toBasis c.toBasis T) := by
  rw [hilbertSchmidtSq_toMatrix_orthonormalBasis,
    hilbertSchmidtSq_toMatrix_orthonormalBasis]

end Schur

/-! ## Tao--Vu Lemma A.2 -/

/-- **Weyl comparison inequality for the second moment** (Tao--Vu,
Lemma A.2).  The roots are counted with algebraic multiplicity. -/
theorem eigenvalueSecondMoment_le_hilbertSchmidtSq (A : Matrix n n ℂ) :
    ((eigenvalueMultiset A).map fun z ↦ ‖z‖ ^ 2).sum ≤
      hilbertSchmidtSq A := by
  let T : Module.End ℂ (EuclideanSpace ℂ n) := Matrix.toEuclideanLin A
  obtain ⟨b, hb⟩ := exists_schur_orthonormalBasis T
  let M : Matrix (Fin (finrank ℂ (EuclideanSpace ℂ n)))
      (Fin (finrank ℂ (EuclideanSpace ℂ n))) ℂ :=
    LinearMap.toMatrix b.toBasis b.toBasis T
  let e : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) :=
    EuclideanSpace.basisFun n ℂ
  have hstd : LinearMap.toMatrix e.toBasis e.toBasis T = A := by
    simpa [T, e, Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      (LinearMap.toMatrix_toLin (v₁ := e.toBasis) (v₂ := e.toBasis) A)
  have hcharA : T.charpoly = A.charpoly := by
    simpa [T, e, Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      (Matrix.charpoly_toLin A e.toBasis)
  have hcharM : M.charpoly = T.charpoly := by
    exact LinearMap.charpoly_toMatrix T b.toBasis
  have hroots : eigenvalueMultiset A = eigenvalueMultiset M := by
    unfold eigenvalueMultiset
    rw [← hcharA, hcharM]
  have hhs : hilbertSchmidtSq M = hilbertSchmidtSq A := by
    calc
      hilbertSchmidtSq M = operatorHilbertSchmidtSq T := by
        exact hilbertSchmidtSq_toMatrix_orthonormalBasis b T
      _ = hilbertSchmidtSq (LinearMap.toMatrix e.toBasis e.toBasis T) := by
        symm
        exact hilbertSchmidtSq_toMatrix_orthonormalBasis e T
      _ = hilbertSchmidtSq A := by rw [hstd]
  calc
    ((eigenvalueMultiset A).map fun z ↦ ‖z‖ ^ 2).sum =
        ((eigenvalueMultiset M).map fun z ↦ ‖z‖ ^ 2).sum := by rw [hroots]
    _ = ∑ i, ‖M i i‖ ^ 2 :=
      eigenvalueSecondMoment_eq_diag_of_isUpperTriangular M hb
    _ ≤ hilbertSchmidtSq M := diagonalSecondMoment_le_hilbertSchmidtSq M
    _ = hilbertSchmidtSq A := hhs

end TaoVuReplacement

