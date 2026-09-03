import CircularLawSection6.BlockSingularCutoff

/-! # Exact cutoff invariance under simultaneous matrix reindexing

The actual Euclidean coordinate permutation transports singular bases.
Comparing with the canonical bases proves invariance of the normalized
cutoff, including a common spectral shift. This is the missing spectral
adapter for identifying routed block coordinates with the literal
Section 4/5 cyclic model.
-/

open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def euclideanReindex (e : ι ≃ κ) : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

theorem toEuclideanLin_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    (A.submatrix e.symm e.symm).toEuclideanLin (euclideanReindex e x) =
      euclideanReindex e (A.toEuclideanLin x) := by
  ext i
  change (∑ j : κ, A (e.symm i) (e.symm j) * x (e.symm j)) =
    ∑ j : ι, A (e.symm i) j * x j
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

theorem toEuclideanLin_adjoint_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    (A.submatrix e.symm e.symm).toEuclideanLin.adjoint (euclideanReindex e x) =
      euclideanReindex e (A.toEuclideanLin.adjoint x) := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_submatrix, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact toEuclideanLin_reindex e A.conjTranspose x

theorem matrixCutoffPotential_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) (hA : A.det ≠ 0)
    {a : ℝ} (ha : 0 < a) :
    matrixCutoffPotential (A.submatrix e.symm e.symm) a = matrixCutoffPotential A a := by
  obtain ⟨u, v, hTv, hTu⟩ := exists_canonical_positive_singular_bases A.toEuclideanLin
    (toEuclideanLin_injective_of_det_ne_zero A hA)
  have hAr : (A.submatrix e.symm e.symm).det ≠ 0 := by
    rwa [Matrix.det_submatrix_equiv_self]
  have hsum := singularValues_sum_eq_of_indexed_singular_bases
    (A.submatrix e.symm e.symm).toEuclideanLin
    (toEuclideanLin_injective_of_det_ne_zero _ hAr)
    (u.map (euclideanReindex e)) (v.map (euclideanReindex e))
    (fun i => A.toEuclideanLin.singularValues i)
    (fun i => A.toEuclideanLin.singularValues_nonneg i)
    (by
      intro i
      simp only [OrthonormalBasis.map_apply]
      rw [toEuclideanLin_reindex, hTv, (euclideanReindex e).map_smul])
    (by
      intro i
      simp only [OrthonormalBasis.map_apply]
      rw [toEuclideanLin_adjoint_reindex, hTu, (euclideanReindex e).map_smul])
    (fun s => Real.log (max s a)) (inv_nonneg.mpr ha.le) (log_max_lipschitz ha)
  unfold matrixCutoffPotential operatorCutoffPotential
  rw [hsum]
  congr 1
  simp only [finrank_euclideanSpace]
  exact_mod_cast (Fintype.card_congr e).symm

theorem matrixCutoffPotential_shifted_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) (z : ℂ)
    (hA : (A - z • 1).det ≠ 0) {a : ℝ} (ha : 0 < a) :
    matrixCutoffPotential (A.submatrix e.symm e.symm - z • 1) a =
      matrixCutoffPotential (A - z • 1) a := by
  have hm : (A - z • 1).submatrix e.symm e.symm = A.submatrix e.symm e.symm - z • 1 := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, e.symm.injective.eq_iff]
  rw [← hm]
  exact matrixCutoffPotential_reindex e (A - z • 1) hA ha

end CircularLawSection6
