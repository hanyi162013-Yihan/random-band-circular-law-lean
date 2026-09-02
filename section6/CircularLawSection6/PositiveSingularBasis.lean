import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Tactic.FieldSimp

/-! # Canonical singular bases on the nonsingular event

The right basis and its singular values are mathlib's existing Gram
spectral data. Dividing their images by the positive singular values gives
the left orthonormal basis. Nonsingularity is explicit, so no zero-singular
value is silently divided away. The resulting comparison applies on the
almost-sure nonsingular event already proved for the random models.
-/

open scoped BigOperators InnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem exists_canonical_positive_singular_bases (T : Module.End ℂ E)
    (hT : Function.Injective T) :
    ∃ u v : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E,
      (∀ i, T (v i) = (T.singularValues i : ℂ) • u i) ∧
      (∀ i, T.adjoint (u i) = (T.singularValues i : ℂ) • v i) := by
  let v := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  let s : Fin (Module.finrank ℂ E) → ℝ := fun i => T.singularValues i
  have hs (i) : 0 < s i :=
    T.injective_iff_forall_lt_finrank_singularValues_pos.mp hT i i.isLt
  have hsC (i) : (s i : ℂ) ≠ 0 := by exact_mod_cast (hs i).ne'
  have hgram (i) : T.adjoint (T (v i)) = (s i : ℂ) ^ 2 • v i := by
    have h := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
    rw [← T.sq_singularValues_fin rfl i] at h
    simp only [LinearMap.comp_apply, RCLike.ofReal_pow] at h
    convert h using 1 <;> rfl
  let u₀ : Fin (Module.finrank ℂ E) → E := fun i => (s i : ℂ)⁻¹ • T (v i)
  have hu : Orthonormal ℂ u₀ := by
    rw [orthonormal_iff_ite]
    intro i j
    dsimp only [u₀]
    rw [inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ),
      ← T.adjoint_inner_right, hgram, inner_smul_right (𝕜 := ℂ),
      orthonormal_iff_ite.mp v.orthonormal]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, map_inv₀]
      rw [show (starRingEnd ℂ) (s i : ℂ) = (s i : ℂ) from Complex.conj_ofReal _]
      field_simp [hsC i]
    · simp [hij]
  have hspan : Submodule.span ℂ (Set.range u₀) = ⊤ :=
    hu.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)
  let u := OrthonormalBasis.mk hu hspan.ge
  refine ⟨u, v, ?_, ?_⟩
  · intro i
    simp only [u, OrthonormalBasis.coe_mk]
    change T (v i) = (s i : ℂ) • ((s i : ℂ)⁻¹ • T (v i))
    rw [smul_smul, mul_inv_cancel₀ (hsC i), one_smul]
  · intro i
    simp only [u, OrthonormalBasis.coe_mk]
    change T.adjoint ((s i : ℂ)⁻¹ • T (v i)) = (s i : ℂ) • v i
    rw [map_smul, hgram, smul_smul]
    congr 1
    field_simp [hsC i]

end CircularLawSection6
