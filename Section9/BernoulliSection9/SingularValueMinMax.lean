import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Interval.Finset.Fin

/-!
# Spectral groundwork for finite-dimensional singular-value min--max

This file develops the Courant--Fischer properties of Mathlib's decreasing
singular-value sequence from the eigenbasis of `T†T`, for use in strong
RRQR.  It contains no assumptions
and no caller-supplied certificates.
-/

open scoped InnerProductSpace

noncomputable section

namespace BernoulliSection9

open Module

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-- The Rayleigh form of a symmetric finite-dimensional operator is the
weighted squared-coordinate sum in its decreasing eigenbasis. -/
theorem spectral_re_inner_expansion (T : E →ₗ[𝕜] E)
    (hT : T.IsSymmetric) (x : E) :
    RCLike.re (inner 𝕜 x (T x)) =
      ∑ i : Fin (finrank 𝕜 E),
        hT.eigenvalues rfl i * ‖(hT.eigenvectorBasis rfl).repr x i‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis rfl).sum_inner_mul_inner x (T x), map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← (hT.eigenvectorBasis rfl).repr_apply_apply,
    hT.eigenvectorBasis_apply_self_apply]
  have hinner : inner 𝕜 x ((hT.eigenvectorBasis rfl) i) =
      starRingEnd 𝕜 ((hT.eigenvectorBasis rfl).repr x i) := by
    rw [(hT.eigenvectorBasis rfl).repr_apply_apply]
    exact (inner_conj_symm x ((hT.eigenvectorBasis rfl) i)).symm
  rw [hinner]
  simp only [RCLike.mul_re, RCLike.mul_im, RCLike.ofReal_re,
    RCLike.ofReal_im, zero_mul, sub_zero, RCLike.conj_re, RCLike.conj_im]
  rw [RCLike.norm_sq_eq_def]
  ring

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable [FiniteDimensional 𝕜 F]

/-- Exact Parseval expansion of `‖T x‖²` in the right singular-vector
eigenbasis. -/
theorem singular_norm_sq_expansion (T : E →ₗ[𝕜] F) (x : E) :
    ‖T x‖ ^ 2 =
      ∑ i : Fin (finrank 𝕜 E),
        T.singularValues i ^ 2 *
          ‖(T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).repr x i‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜),
    ← LinearMap.adjoint_inner_right T x (T x)]
  change RCLike.re (inner 𝕜 x ((LinearMap.adjoint T ∘ₗ T) x)) = _
  rw [spectral_re_inner_expansion]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [T.sq_singularValues_fin rfl]

/-- On the spectral tail beginning at `i`, `T` has norm at most its `i`th
singular value.  Membership is written as the equivalent vanishing of all
lower-index coordinates so this lemma can be reused before packaging the
tail as a submodule. -/
theorem norm_apply_le_singularValue_mul_norm_of_lower_coefficients_eq_zero
    (T : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) (x : E)
    (hx : ∀ j : Fin (finrank 𝕜 E), j < i →
      (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).repr x j = 0) :
    ‖T x‖ ≤ T.singularValues i * ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (T.singularValues_nonneg i) (norm_nonneg _)),
    singular_norm_sq_expansion, mul_pow,
    ← (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).sum_sq_norm_inner_right x]
  simp_rw [← (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).repr_apply_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _hj
  by_cases hji : j < i
  · simp [hx j hji]
  · have hs : T.singularValues j ≤ T.singularValues i :=
      T.singularValues_antitone (le_of_not_gt hji)
    exact mul_le_mul_of_nonneg_right
      (sq_le_sq₀ (T.singularValues_nonneg j) (T.singularValues_nonneg i) |>.mpr hs)
      (sq_nonneg _)

/-- On the spectral head ending at `i`, `T` is bounded below by its `i`th
singular value. -/
theorem singularValue_mul_norm_le_norm_apply_of_upper_coefficients_eq_zero
    (T : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) (x : E)
    (hx : ∀ j : Fin (finrank 𝕜 E), i < j →
      (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).repr x j = 0) :
    T.singularValues i * ‖x‖ ≤ ‖T x‖ := by
  rw [← sq_le_sq₀ (mul_nonneg (T.singularValues_nonneg i) (norm_nonneg _)) (norm_nonneg _),
    singular_norm_sq_expansion, mul_pow,
    ← (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).sum_sq_norm_inner_right x]
  simp_rw [← (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).repr_apply_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _hj
  by_cases hij : i < j
  · simp [hx j hij]
  · have hs : T.singularValues i ≤ T.singularValues j :=
      T.singularValues_antitone (le_of_not_gt hij)
    exact mul_le_mul_of_nonneg_right
      (sq_le_sq₀ (T.singularValues_nonneg i) (T.singularValues_nonneg j) |>.mpr hs)
      (sq_nonneg _)

/-! ## Spectral head and tail subspaces -/

abbrev SpectralTailIndex (d : ℕ) (i : Fin d) := Set.Ici i

abbrev SpectralHeadIndex (d : ℕ) (i : Fin d) := Set.Iic i

/-- The span of the right singular vectors with indices at least `i`. -/
def singularSpectralTail (T : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun j : SpectralTailIndex (finrank 𝕜 E) i =>
    T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl j.1)

/-- The span of the right singular vectors with indices at most `i`. -/
def singularSpectralHead (T : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun j : SpectralHeadIndex (finrank 𝕜 E) i =>
    T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl j.1)

theorem finrank_singularSpectralTail (T : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) :
    finrank 𝕜 (singularSpectralTail T i) = finrank 𝕜 E - i := by
  rw [singularSpectralTail, finrank_span_eq_card]
  · rw [Fintype.card_Ici, Fin.card_Ici]
  · exact (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).toBasis.linearIndependent.comp
      (fun j : SpectralTailIndex (finrank 𝕜 E) i => j.1) Subtype.val_injective

theorem finrank_singularSpectralHead (T : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) :
    finrank 𝕜 (singularSpectralHead T i) = i + 1 := by
  rw [singularSpectralHead, finrank_span_eq_card]
  · rw [Fintype.card_Iic, Fin.card_Iic]
  · exact (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).toBasis.linearIndependent.comp
      (fun j : SpectralHeadIndex (finrank 𝕜 E) i => j.1) Subtype.val_injective

theorem lower_coefficients_eq_zero_of_mem_singularSpectralTail (T : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) {x : E} (hx : x ∈ singularSpectralTail T i)
    (j : Fin (finrank 𝕜 E)) (hji : j < i) :
    (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).repr x j = 0 := by
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  change x ∈ Submodule.span 𝕜 (Set.range fun k : SpectralTailIndex (finrank 𝕜 E) i => b k.1) at hx
  refine Submodule.span_induction (p := fun y _hy => b.repr y j = 0) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨k, rfl⟩
    rw [b.repr_self]
    simp [ne_of_lt (hji.trans_le k.property)]
  · simp
  · intro y z _hy _hz py pz
    simp [py, pz]
  · intro c y _hy py
    simp [py]

theorem upper_coefficients_eq_zero_of_mem_singularSpectralHead (T : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) {x : E} (hx : x ∈ singularSpectralHead T i)
    (j : Fin (finrank 𝕜 E)) (hij : i < j) :
    (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).repr x j = 0 := by
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  change x ∈ Submodule.span 𝕜 (Set.range fun k : SpectralHeadIndex (finrank 𝕜 E) i => b k.1) at hx
  refine Submodule.span_induction (p := fun y _hy => b.repr y j = 0) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨k, rfl⟩
    rw [b.repr_self]
    simp [ne_of_lt (k.property.trans_lt hij)]
  · simp
  · intro y z _hy _hz py pz
    simp [py, pz]
  · intro c y _hy py
    simp [py]

theorem norm_apply_le_singularValue_mul_norm_of_mem_singularSpectralTail
    (T : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) {x : E}
    (hx : x ∈ singularSpectralTail T i) :
    ‖T x‖ ≤ T.singularValues i * ‖x‖ :=
  norm_apply_le_singularValue_mul_norm_of_lower_coefficients_eq_zero T i x
    fun j hji => lower_coefficients_eq_zero_of_mem_singularSpectralTail T i hx j hji

theorem singularValue_mul_norm_le_norm_apply_of_mem_singularSpectralHead
    (T : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) {x : E}
    (hx : x ∈ singularSpectralHead T i) :
    T.singularValues i * ‖x‖ ≤ ‖T x‖ :=
  singularValue_mul_norm_le_norm_apply_of_upper_coefficients_eq_zero T i x
    fun j hij => upper_coefficients_eq_zero_of_mem_singularSpectralHead T i hx j hij

/-! ## Courant--Fischer threshold characterizations -/

/-- Two subspaces whose dimensions add to more than the ambient dimension
contain a common nonzero vector. -/
theorem exists_ne_zero_mem_inf_of_finrank_lt_add (U W : Submodule 𝕜 E)
    (hdim : finrank 𝕜 E < finrank 𝕜 U + finrank 𝕜 W) :
    ∃ x : E, x ∈ U ∧ x ∈ W ∧ x ≠ 0 := by
  have hinfpos : 0 < finrank 𝕜 ↥(U ⊓ W) := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq U W
    have hsup : finrank 𝕜 ↥(U ⊔ W) ≤ finrank 𝕜 E := Submodule.finrank_le _
    omega
  have hinf : U ⊓ W ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hinfpos
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  exact ⟨x, hx.1, hx.2, hx0⟩

/-- Courant--Fischer, threshold form: every codimension-`i` subspace on
which `T` is bounded by `C` gives an upper bound for the `i`th singular
value. -/
theorem singularValue_le_of_submodule_bound (T : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) (W : Submodule 𝕜 E) (C : ℝ)
    (hW : finrank 𝕜 W = finrank 𝕜 E - i)
    (hbound : ∀ x : E, x ∈ W → ‖T x‖ ≤ C * ‖x‖) :
    T.singularValues i ≤ C := by
  obtain ⟨x, hxHead, hxW, hx0⟩ :=
    exists_ne_zero_mem_inf_of_finrank_lt_add (singularSpectralHead T i) W (by
      rw [finrank_singularSpectralHead, hW]
      omega)
  have hlower := singularValue_mul_norm_le_norm_apply_of_mem_singularSpectralHead T i hxHead
  have hupper := hbound x hxW
  nlinarith [norm_pos_iff.mpr hx0]

/-- The same upper min--max principle when the witness subspace has at
least the required dimension. -/
theorem singularValue_le_of_submodule_bound_of_le_finrank (T : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) (W : Submodule 𝕜 E) (C : ℝ)
    (hW : finrank 𝕜 E - i ≤ finrank 𝕜 W)
    (hbound : ∀ x : E, x ∈ W → ‖T x‖ ≤ C * ‖x‖) :
    T.singularValues i ≤ C := by
  obtain ⟨x, hxHead, hxW, hx0⟩ :=
    exists_ne_zero_mem_inf_of_finrank_lt_add (singularSpectralHead T i) W (by
      rw [finrank_singularSpectralHead]
      omega)
  have hlower := singularValue_mul_norm_le_norm_apply_of_mem_singularSpectralHead T i hxHead
  have hupper := hbound x hxW
  nlinarith [norm_pos_iff.mpr hx0]

/-- Dual Courant--Fischer threshold form: an `(i+1)`-dimensional subspace
on which `T` is bounded below by `C` gives a lower bound for the `i`th
singular value. -/
theorem le_singularValue_of_submodule_lower_bound (T : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) (W : Submodule 𝕜 E) (C : ℝ)
    (hW : finrank 𝕜 W = i + 1)
    (hbound : ∀ x : E, x ∈ W → C * ‖x‖ ≤ ‖T x‖) :
    C ≤ T.singularValues i := by
  obtain ⟨x, hxTail, hxW, hx0⟩ :=
    exists_ne_zero_mem_inf_of_finrank_lt_add (singularSpectralTail T i) W (by
      rw [finrank_singularSpectralTail, hW]
      omega)
  have hlower := hbound x hxW
  have hupper := norm_apply_le_singularValue_mul_norm_of_mem_singularSpectralTail T i hxTail
  nlinarith [norm_pos_iff.mpr hx0]

/-- A convenient range-parametrized version of the lower min--max
principle.  An injective map from an `(i+1)`-dimensional parameter space
produces the required witness subspace. -/
theorem le_singularValue_of_injective_parametrization
    {D : Type*} [NormedAddCommGroup D] [InnerProductSpace 𝕜 D]
    [FiniteDimensional 𝕜 D]
    (T : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E))
    (Φ : D →ₗ[𝕜] E) (C : ℝ)
    (hdim : finrank 𝕜 D = i + 1) (hΦ : Function.Injective Φ)
    (hbound : ∀ z : D, C * ‖Φ z‖ ≤ ‖T (Φ z)‖) :
    C ≤ T.singularValues i := by
  apply le_singularValue_of_submodule_lower_bound T i Φ.range C
  · rw [LinearMap.finrank_range_of_inj hΦ, hdim]
  · intro x hx
    rcases hx with ⟨z, rfl⟩
    exact hbound z

/-- Exact upper min--max characterization, expressed without infima: `C`
bounds the `i`th singular value exactly when a codimension-`i` witness
subspace has operator bound `C`. -/
theorem singularValue_le_iff_exists_submodule_bound (T : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) (C : ℝ) :
    T.singularValues i ≤ C ↔
      ∃ W : Submodule 𝕜 E,
        finrank 𝕜 W = finrank 𝕜 E - i ∧
          ∀ x : E, x ∈ W → ‖T x‖ ≤ C * ‖x‖ := by
  constructor
  · intro hC
    refine ⟨singularSpectralTail T i, finrank_singularSpectralTail T i, fun x hx => ?_⟩
    exact (norm_apply_le_singularValue_mul_norm_of_mem_singularSpectralTail T i hx).trans
      (mul_le_mul_of_nonneg_right hC (norm_nonneg x))
  · rintro ⟨W, hW, hbound⟩
    exact singularValue_le_of_submodule_bound T i W C hW hbound

/-- Exact lower max--min characterization, again in threshold form. -/
theorem le_singularValue_iff_exists_submodule_lower_bound (T : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) (C : ℝ) :
    C ≤ T.singularValues i ↔
      ∃ W : Submodule 𝕜 E,
        finrank 𝕜 W = i + 1 ∧
          ∀ x : E, x ∈ W → C * ‖x‖ ≤ ‖T x‖ := by
  constructor
  · intro hC
    refine ⟨singularSpectralHead T i, finrank_singularSpectralHead T i, fun x hx => ?_⟩
    exact (mul_le_mul_of_nonneg_right hC (norm_nonneg x)).trans
      (singularValue_mul_norm_le_norm_apply_of_mem_singularSpectralHead T i hx)
  · rintro ⟨W, hW, hbound⟩
    exact le_singularValue_of_submodule_lower_bound T i W C hW hbound

/-- Every singular value of the identity map (at an in-range index) is
exactly one. -/
theorem singularValues_id_eq_one (i : Fin (finrank 𝕜 E)) :
    (LinearMap.id : E →ₗ[𝕜] E).singularValues i = 1 := by
  apply le_antisymm
  · apply singularValue_le_of_submodule_bound
      (LinearMap.id : E →ₗ[𝕜] E) i
      (singularSpectralTail (LinearMap.id : E →ₗ[𝕜] E) i) 1
      (finrank_singularSpectralTail (LinearMap.id : E →ₗ[𝕜] E) i)
    intro x _
    simp
  · apply le_singularValue_of_submodule_lower_bound
      (LinearMap.id : E →ₗ[𝕜] E) i
      (singularSpectralHead (LinearMap.id : E →ₗ[𝕜] E) i) 1
      (finrank_singularSpectralHead (LinearMap.id : E →ₗ[𝕜] E) i)
    intro x _
    simp

/-- The operator norm is bounded by the first singular value.  This is
the endpoint `i = 0` of the spectral-tail estimate. -/
theorem opNorm_le_firstSingularValue (T : E →ₗ[𝕜] F)
    (hE : 0 < finrank 𝕜 E) :
    ‖T.toContinuousLinearMap‖ ≤ T.singularValues 0 := by
  let i : Fin (finrank 𝕜 E) := ⟨0, hE⟩
  have htail : singularSpectralTail T i = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_singularSpectralTail]
    simp [i]
  apply T.toContinuousLinearMap.opNorm_le_bound (T.singularValues_nonneg i)
  intro x
  apply norm_apply_le_singularValue_mul_norm_of_mem_singularSpectralTail T i
  rw [htail]
  exact Submodule.mem_top

/-! ## Singular values of products -/

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
variable [FiniteDimensional 𝕜 G]

/-- Left-multiplication singular-value inequality
`sᵢ(A ∘ B) ≤ ‖A‖ sᵢ(B)`. -/
theorem singularValue_comp_le_opNorm_mul (A : F →ₗ[𝕜] G) (B : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) :
    (A ∘ₗ B).singularValues i ≤ ‖A.toContinuousLinearMap‖ * B.singularValues i := by
  apply singularValue_le_of_submodule_bound (A ∘ₗ B) i (singularSpectralTail B i)
    (‖A.toContinuousLinearMap‖ * B.singularValues i)
    (finrank_singularSpectralTail B i)
  intro x hx
  calc
    ‖(A ∘ₗ B) x‖ = ‖A (B x)‖ := rfl
    _ ≤ ‖A.toContinuousLinearMap‖ * ‖B x‖ := A.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖A.toContinuousLinearMap‖ * (B.singularValues i * ‖x‖) :=
      mul_le_mul_of_nonneg_left
        (norm_apply_le_singularValue_mul_norm_of_mem_singularSpectralTail B i hx)
        (norm_nonneg _)
    _ = (‖A.toContinuousLinearMap‖ * B.singularValues i) * ‖x‖ := by ring

/-- The preimage of a subspace has dimension at least the ambient-domain
dimension minus the dimension of the quotient by that subspace. -/
theorem finrank_tsub_quotient_le_finrank_comap (B : E →ₗ[𝕜] F)
    (W : Submodule 𝕜 F) :
    finrank 𝕜 E - finrank 𝕜 (F ⧸ W) ≤ finrank 𝕜 (W.comap B) := by
  let f : E →ₗ[𝕜] (F ⧸ W) := W.mkQ.comp B
  have hrank := f.finrank_range_add_finrank_ker
  have hrange : finrank 𝕜 f.range ≤ finrank 𝕜 (F ⧸ W) := Submodule.finrank_le _
  have hker : f.ker = W.comap B := by
    change LinearMap.ker (W.mkQ.comp B) = W.comap B
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [hker] at hrank
  omega

/-- Right-multiplication singular-value inequality
`sᵢ(A ∘ B) ≤ sᵢ(A) ‖B‖`.  The index only needs to exist in both
domains; the spaces need not have equal dimension. -/
theorem singularValue_comp_le_mul_opNorm (A : F →ₗ[𝕜] G) (B : E →ₗ[𝕜] F)
    (i : ℕ) (hiE : i < finrank 𝕜 E) (hiF : i < finrank 𝕜 F) :
    (A ∘ₗ B).singularValues i ≤ A.singularValues i * ‖B.toContinuousLinearMap‖ := by
  let iE : Fin (finrank 𝕜 E) := ⟨i, hiE⟩
  let iF : Fin (finrank 𝕜 F) := ⟨i, hiF⟩
  let W := (singularSpectralTail A iF).comap B
  apply singularValue_le_of_submodule_bound_of_le_finrank (A ∘ₗ B) iE W
    (A.singularValues iF * ‖B.toContinuousLinearMap‖)
  · have hpre := finrank_tsub_quotient_le_finrank_comap B (singularSpectralTail A iF)
    have hquot := (singularSpectralTail A iF).finrank_quotient_add_finrank
    rw [finrank_singularSpectralTail] at hquot
    have hquot_eq : finrank 𝕜 (F ⧸ singularSpectralTail A iF) = i := by
      dsimp [iF] at hquot ⊢
      omega
    rw [hquot_eq] at hpre
    dsimp [iE, W]
    exact hpre
  · intro x hx
    have hxTail : B x ∈ singularSpectralTail A iF := hx
    calc
      ‖(A ∘ₗ B) x‖ = ‖A (B x)‖ := rfl
      _ ≤ A.singularValues iF * ‖B x‖ :=
        norm_apply_le_singularValue_mul_norm_of_mem_singularSpectralTail A iF hxTail
      _ ≤ A.singularValues iF * (‖B.toContinuousLinearMap‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (B.toContinuousLinearMap.le_opNorm x)
          (A.singularValues_nonneg iF)
      _ = (A.singularValues iF * ‖B.toContinuousLinearMap‖) * ‖x‖ := by ring

/-- Postcomposition by a contraction cannot increase any singular value.
This is the row-compression form of interlacing. -/
theorem singularValue_comp_le_of_opNorm_le_one (A : F →ₗ[𝕜] G) (B : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) (hA : ‖A.toContinuousLinearMap‖ ≤ 1) :
    (A ∘ₗ B).singularValues i ≤ B.singularValues i := by
  calc
    (A ∘ₗ B).singularValues i ≤ ‖A.toContinuousLinearMap‖ * B.singularValues i :=
      singularValue_comp_le_opNorm_mul A B i
    _ ≤ 1 * B.singularValues i :=
      mul_le_mul_of_nonneg_right hA (B.singularValues_nonneg i)
    _ = B.singularValues i := one_mul _

/-- Precomposition by a contraction cannot increase any singular value
whose index exists on both sides.  This is the column-compression form of
interlacing. -/
theorem singularValue_comp_le_of_right_opNorm_le_one (A : F →ₗ[𝕜] G)
    (B : E →ₗ[𝕜] F) (i : ℕ) (hiE : i < finrank 𝕜 E)
    (hiF : i < finrank 𝕜 F) (hB : ‖B.toContinuousLinearMap‖ ≤ 1) :
    (A ∘ₗ B).singularValues i ≤ A.singularValues i := by
  calc
    (A ∘ₗ B).singularValues i ≤ A.singularValues i * ‖B.toContinuousLinearMap‖ :=
      singularValue_comp_le_mul_opNorm A B i hiE hiF
    _ ≤ A.singularValues i * 1 :=
      mul_le_mul_of_nonneg_left hB (A.singularValues_nonneg i)
    _ = A.singularValues i := mul_one _

/-- If `B` has a right inverse `C`, the right product inequality can be
reversed with the expected condition-number factor. -/
theorem singularValue_le_comp_mul_opNorm_of_rightInverse
    (A : F →ₗ[𝕜] G) (B : E →ₗ[𝕜] F) (C : F →ₗ[𝕜] E)
    (hBC : B ∘ₗ C = LinearMap.id) (i : ℕ)
    (hiF : i < finrank 𝕜 F) (hiE : i < finrank 𝕜 E) :
    A.singularValues i ≤
      (A ∘ₗ B).singularValues i * ‖C.toContinuousLinearMap‖ := by
  have h := singularValue_comp_le_mul_opNorm (A ∘ₗ B) C i hiF hiE
  rw [LinearMap.comp_assoc, hBC, LinearMap.comp_id] at h
  exact h

/-- If `A` has a left inverse `C`, the left product inequality can be
reversed with the expected condition-number factor. -/
theorem singularValue_le_opNorm_mul_comp_of_leftInverse
    (A : F →ₗ[𝕜] G) (C : G →ₗ[𝕜] F) (B : E →ₗ[𝕜] F)
    (hCA : C ∘ₗ A = LinearMap.id) (i : Fin (finrank 𝕜 E)) :
    B.singularValues i ≤
      ‖C.toContinuousLinearMap‖ * (A ∘ₗ B).singularValues i := by
  have h := singularValue_comp_le_opNorm_mul C (A ∘ₗ B) i
  have hcomp : C ∘ₗ (A ∘ₗ B) = B := by
    ext x
    have hx := LinearMap.congr_fun hCA (B x)
    exact hx
  rw [hcomp] at h
  exact h

/-! ## Matrix wrappers -/

open scoped Matrix.Norms.L2Operator

/-- Matrix form of `sᵢ(A B) ≤ ‖A‖ sᵢ(B)` for complex Euclidean
operator norm and zero-based finite indices. -/
theorem matrix_singularValue_mul_le_l2OpNorm_mul {m k n : ℕ}
    (A : Matrix (Fin m) (Fin k) ℂ) (B : Matrix (Fin k) (Fin n) ℂ)
    (i : Fin n) :
    (Matrix.toEuclideanLin (A * B)).singularValues i ≤
      ‖A‖ * (Matrix.toEuclideanLin B).singularValues i := by
  let i' : Fin (finrank ℂ (EuclideanSpace ℂ (Fin n))) :=
    ⟨i, by simpa using i.isLt⟩
  have h := singularValue_comp_le_opNorm_mul
    (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) i'
  rw [← Matrix.toLpLin_mul_same] at h
  simpa [Matrix.l2_opNorm_def, i'] using h

/-- Matrix form of `sᵢ(A B) ≤ sᵢ(A) ‖B‖`. -/
theorem matrix_singularValue_mul_le_mul_l2OpNorm {m k n : ℕ}
    (A : Matrix (Fin m) (Fin k) ℂ) (B : Matrix (Fin k) (Fin n) ℂ)
    (i : ℕ) (hin : i < n) (hik : i < k) :
    (Matrix.toEuclideanLin (A * B)).singularValues i ≤
      (Matrix.toEuclideanLin A).singularValues i * ‖B‖ := by
  have h := singularValue_comp_le_mul_opNorm
    (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) i
    (by simpa using hin) (by simpa using hik)
  rw [← Matrix.toLpLin_mul_same] at h
  simpa [Matrix.l2_opNorm_def] using h

end BernoulliSection9
