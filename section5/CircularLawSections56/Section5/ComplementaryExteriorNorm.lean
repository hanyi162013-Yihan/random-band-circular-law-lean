import CircularLawSections56.Section5.CompanionInverseNorm
import Mathlib.Analysis.Matrix.Spectrum

/-! # Exact complementary-degree identities for exterior operator norms

The proof uses the spectral theorem only for the Gram matrix.  Complementing
the sets indexing diagonal minors supplies the exact determinant denominator;
unitary changes of coordinates introduce no dimension-dependent factor.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSections56.Section5

open CircularLawSection4 Matrix Set.powersetCard

def complementaryDegree (d : ℕ) (q : ExteriorDegree (d + 1)) : ExteriorDegree (d + 1) :=
  ⟨d + 1 - q.val, by omega⟩

def exteriorComplementEquiv (d : ℕ) (q : ExteriorDegree (d + 1)) :
    ExteriorIndex (d + 1) q ≃ ExteriorIndex (d + 1) (complementaryDegree d q) where
  toFun s := ⟨s.valᶜ, by
    change (s.valᶜ).card = d + 1 - q.val
    rw [Finset.card_compl, Fintype.card_fin, s.prop]⟩
  invFun s := ⟨s.valᶜ, by
    have hq := q.isLt
    change (s.valᶜ).card = q.val
    rw [Finset.card_compl, Fintype.card_fin, s.prop]
    change d + 1 - (d + 1 - q.val) = q.val
    omega⟩
  left_inv s := by ext; simp
  right_inv s := by ext; simp

theorem compound_diagonal (d k : ℕ) (a : Fin (d + 1) → ℂ) :
    compound k (Matrix.diagonal a) =
      Matrix.diagonal (fun s : Set.powersetCard (Fin (d + 1)) k => ∏ i ∈ s.val, a i) := by
  classical
  ext s t
  rw [compound_apply, minor]
  by_cases hst : s = t
  · subst t
    rw [Matrix.diagonal_apply_eq]
    have heq : (Matrix.diagonal a).submatrix (ofFinEmbEquiv.symm s)
        (ofFinEmbEquiv.symm s) = Matrix.diagonal (fun i => a (ofFinEmbEquiv.symm s i)) := by
      ext i j
      simp [Matrix.submatrix_apply, Matrix.diagonal_apply,
        (ofFinEmbEquiv.symm s).injective.eq_iff]
    rw [heq, Matrix.det_diagonal]
    exact Finset.prod_bij (fun i _ => ofFinEmbEquiv.symm s i)
      (fun i _ => by
        exact (mem_range_ofFinEmbEquiv_symm_iff_mem s _).1 ⟨i, rfl⟩)
      (fun i _ j _ h => (ofFinEmbEquiv.symm s).injective h)
      (fun j hj => by
        obtain ⟨i, hi⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s j).2 hj
        exact ⟨i, Finset.mem_univ _, hi⟩)
      (fun _ _ => rfl)
  · rw [Matrix.diagonal_apply_ne _ hst]
    obtain ⟨i, his, hit⟩ := (exists_mem_notMem_iff_ne s t).1 hst
    obtain ⟨j, rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s i).2 his
    apply Matrix.det_eq_zero_of_row_eq_zero j
    intro l
    apply Matrix.diagonal_apply_ne
    intro h
    apply hit
    rw [h]
    exact (mem_range_ofFinEmbEquiv_symm_iff_mem t _).1 ⟨l, rfl⟩

def compoundUnitary (d : ℕ) (q : ExteriorDegree (d + 1))
    (U : unitary (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) :
    unitary (Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ) := by
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := U
  have hleft : Aᴴ * A = 1 := Unitary.coe_star_mul_self U
  have hright : A * Aᴴ = 1 := Unitary.coe_mul_star_self U
  refine ⟨compound q.val A, ?_⟩
  change (compound q.val A)ᴴ * compound q.val A = 1 ∧
    compound q.val A * (compound q.val A)ᴴ = 1
  constructor
  · rw [← compound_conjTranspose, ← compound_mul, hleft, compound_identity]
  · rw [← compound_conjTranspose, ← compound_mul, hright, compound_identity]

theorem norm_compound_unitary_conjugate (d : ℕ) (q : ExteriorDegree (d + 1))
    (U : unitary (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ))
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    ‖compound q.val ((U : Matrix (Fin (d + 1)) _ ℂ) * A *
      (U : Matrix (Fin (d + 1)) _ ℂ)ᴴ)‖ = ‖compound q.val A‖ := by
  rw [compound_mul, compound_mul, compound_conjTranspose]
  change ‖(compoundUnitary d q U : Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ) *
    compound q.val A * star (compoundUnitary d q U :
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)‖ = _
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

theorem compound_nonsing_inv (d k : ℕ)
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (hA : IsUnit A.det) :
    compound k A⁻¹ = (compound k A)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← compound_mul, Matrix.nonsing_inv_mul _ hA, compound_identity]

theorem norm_compound_diagonal_inverse (d : ℕ) (q : ExteriorDegree (d + 1))
    (a : Fin (d + 1) → ℂ) (ha : ∀ i, a i ≠ 0) :
    ‖compound q.val (Matrix.diagonal a)⁻¹‖ =
      ‖compound (complementaryDegree d q).val (Matrix.diagonal a)‖ / ‖(Matrix.diagonal a).det‖ := by
  classical
  let e := exteriorComplementEquiv d q
  let g : ExteriorIndex (d + 1) (complementaryDegree d q) → ℂ :=
    fun s => ∏ i ∈ s.val, a i
  have hprod : ∀ s : ExteriorIndex (d + 1) q,
      (∏ i ∈ s.val, (a i)⁻¹) = (∏ i, a i)⁻¹ * g (e s) := by
    intro s
    have hs : (∏ i ∈ s.val, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => ha i)
    have ht : (∏ i ∈ s.valᶜ, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => ha i)
    rw [Finset.prod_inv_distrib, ← Finset.prod_mul_prod_compl s.val a]
    change (∏ i ∈ s.val, a i)⁻¹ =
      ((∏ i ∈ s.val, a i) * (∏ i ∈ s.valᶜ, a i))⁻¹ * (∏ i ∈ s.valᶜ, a i)
    field_simp
  have hinv : (Matrix.diagonal a)⁻¹ = Matrix.diagonal (fun i => (a i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    have he : (fun i => (a i)⁻¹ * a i) = fun _ => (1 : ℂ) :=
      funext fun i => inv_mul_cancel₀ (ha i)
    rw [he, Matrix.diagonal_one]
  rw [hinv, compound_diagonal, compound_diagonal,
    Matrix.l2_opNorm_diagonal, Matrix.l2_opNorm_diagonal, Matrix.det_diagonal]
  have heq : (fun s : ExteriorIndex (d + 1) q => ∏ i ∈ s.val, (a i)⁻¹) =
      (∏ i, a i)⁻¹ • (g ∘ e) := by
    funext s
    exact hprod s
  change ‖(fun s : ExteriorIndex (d + 1) q => ∏ i ∈ s.val, (a i)⁻¹)‖ =
    ‖g‖ / ‖∏ i, a i‖
  rw [heq, norm_smul, norm_inv, e.surjective.pi_norm_comp]
  ring

theorem norm_compound_hermitian_inverse (d : ℕ) (q : ExteriorDegree (d + 1))
    (H : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    ‖compound q.val H⁻¹‖ = ‖compound (complementaryDegree d q).val H‖ / ‖H.det‖ := by
  classical
  let U := hH.eigenvectorUnitary
  let a : Fin (d + 1) → ℂ := RCLike.ofReal ∘ hH.eigenvalues
  have hdiagdet : (Matrix.diagonal a).det = H.det := by
    rw [Matrix.det_diagonal, hH.det_eq_prod_eigenvalues]
    rfl
  have ha : ∀ i, a i ≠ 0 := by
    have hp : (∏ i, a i) ≠ 0 := by
      rw [← Matrix.det_diagonal, hdiagdet]
      exact hdet.ne_zero
    exact fun i => Finset.prod_ne_zero_iff.1 hp i (Finset.mem_univ _)
  have hdiag : H = (U : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Matrix.diagonal a *
      (U : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)ᴴ := by
    exact hH.spectral_theorem
  have hUi : (U : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)⁻¹ =
      (U : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)ᴴ :=
    Matrix.inv_eq_left_inv (Unitary.coe_star_mul_self U)
  have hUhi : (U : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)ᴴ⁻¹ =
      (U : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    Matrix.inv_eq_left_inv (Unitary.coe_mul_star_self U)
  have hinv : H⁻¹ = (U : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * (Matrix.diagonal a)⁻¹ *
      (U : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)ᴴ := by
    rw [hdiag, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hUi, hUhi, Matrix.mul_assoc]
  have hn : ‖compound (complementaryDegree d q).val H‖ =
      ‖compound (complementaryDegree d q).val (Matrix.diagonal a)‖ :=
    (congrArg (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
      ‖compound (complementaryDegree d q).val M‖) hdiag).trans
        (norm_compound_unitary_conjugate d (complementaryDegree d q) U (Matrix.diagonal a))
  calc
    _ = ‖compound q.val (Matrix.diagonal a)⁻¹‖ := by
      rw [hinv, norm_compound_unitary_conjugate]
    _ = ‖compound (complementaryDegree d q).val (Matrix.diagonal a)‖ / ‖H.det‖ := by
      rw [norm_compound_diagonal_inverse d q a ha, hdiagdet]
    _ = _ := congrArg (fun x : ℝ => x / ‖H.det‖) hn.symm

/-- Exact Jacobi/Hodge norm identity, including exterior degrees zero and `d + 1`.
Only invertibility is assumed; no singular-value formula is an input. -/
theorem norm_compound_inverse_eq_complement (d : ℕ) (q : ExteriorDegree (d + 1))
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (hA : IsUnit A.det) :
    ‖(compound q.val A)⁻¹‖ = ‖compound (complementaryDegree d q).val A‖ / ‖A.det‖ := by
  have hdet : IsUnit (A * Aᴴ).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact hA.mul hA.star
  have h := norm_compound_hermitian_inverse d q (A * Aᴴ)
    (Matrix.isHermitian_mul_conjTranspose_self A) hdet
  have hleft : ‖compound q.val (A * Aᴴ)⁻¹‖ = ‖compound q.val A⁻¹‖ * ‖compound q.val A⁻¹‖ := by
    rw [Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv, compound_mul,
      compound_conjTranspose, Matrix.l2_opNorm_conjTranspose_mul_self]
  have hright : ‖compound (complementaryDegree d q).val (A * Aᴴ)‖ =
      ‖compound (complementaryDegree d q).val A‖ * ‖compound (complementaryDegree d q).val A‖ := by
    rw [compound_mul, compound_conjTranspose]
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] using
      Matrix.l2_opNorm_conjTranspose_mul_self (compound (complementaryDegree d q).val A)ᴴ
  have hdetnorm : ‖(A * Aᴴ).det‖ = ‖A.det‖ * ‖A.det‖ := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star]
  rw [hleft, hright, hdetnorm] at h
  rw [← compound_nonsing_inv d q.val A hA]
  apply (sq_eq_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) (norm_nonneg _))).1
  calc
    _ = ‖compound q.val A⁻¹‖ * ‖compound q.val A⁻¹‖ := pow_two _
    _ = _ := h
    _ = _ := by rw [div_pow, pow_two, pow_two]

end CircularLawSections56.Section5
