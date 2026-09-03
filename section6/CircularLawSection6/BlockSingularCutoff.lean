import CircularLawSection6.SingularBasisCutoff
import Mathlib.Data.Matrix.Block

/-! # Exact singular cutoff averaging for finite block diagonal matrices

The block singular bases assemble into orthonormal bases of the full
Euclidean space. Comparing this singular decomposition with the canonical
one yields the exact dimension-weighted cutoff identity. No spectral
averaging or equality of empirical distributions is assumed.
-/

open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem singularValues_sum_eq_of_indexed_singular_bases
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {κ : Type*} [Fintype κ] (T : Module.End ℂ E) (hT : Function.Injective T)
    (u v : OrthonormalBasis κ ℂ E) (s : κ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hTv : ∀ i, T (v i) = (s i : ℂ) • u i)
    (hTu : ∀ i, T.adjoint (u i) = (s i : ℂ) • v i)
    (φ : ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ x y, |φ x - φ y| ≤ K * |x - y|) :
    (∑ i : Fin (Module.finrank ℂ E), φ (T.singularValues i)) = ∑ i, φ (s i) := by
  let e : κ ≃ Fin (Module.finrank ℂ E) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis u.toBasis).symm
  have h := singularValues_sum_eq_of_singular_bases T hT (u.reindex e) (v.reindex e)
    (fun i => s (e.symm i)) (fun i => hs (e.symm i))
    (by intro i; simpa only [OrthonormalBasis.reindex_apply] using hTv (e.symm i))
    (by intro i; simpa only [OrthonormalBasis.reindex_apply] using hTu (e.symm i)) φ hK hφ
  rw [h]
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

variable {β : Type*} [Fintype β] [DecidableEq β]
  {ι : β → Type*} [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]

def blockEuclideanCurry : EuclideanSpace ℂ ((b : β) × ι b) ≃ₗᵢ[ℂ]
    PiLp 2 (fun b => EuclideanSpace ℂ (ι b)) :=
  LinearIsometryEquiv.piLpCurry ℂ 2 (fun _ _ => ℂ)

theorem blockDiagonal_toEuclideanLin_curry (A : ∀ b, Matrix (ι b) (ι b) ℂ)
    (x : EuclideanSpace ℂ ((b : β) × ι b)) (b : β) :
    blockEuclideanCurry ((Matrix.blockDiagonal' A).toEuclideanLin x) b =
      (A b).toEuclideanLin (blockEuclideanCurry x b) := by
  ext i
  change (∑ j : (c : β) × ι c, Matrix.blockDiagonal' A ⟨b, i⟩ j * x j) =
    ∑ j, A b i j * x ⟨b, j⟩
  rw [Fintype.sum_sigma, Finset.sum_eq_single b]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro c _ hcb
    simp only [Matrix.blockDiagonal'_apply_ne A _ _ hcb.symm, zero_mul, Finset.sum_const_zero]
  · simp

theorem blockDiagonal_toEuclideanLin_injective (A : ∀ b, Matrix (ι b) (ι b) ℂ)
    (hA : ∀ b, Function.Injective (A b).toEuclideanLin) :
    Function.Injective (Matrix.blockDiagonal' A).toEuclideanLin := by
  intro x y h
  apply blockEuclideanCurry.injective
  ext b : 1
  apply hA b
  have hc := congrArg (fun v => blockEuclideanCurry v b) h
  simpa only [blockDiagonal_toEuclideanLin_curry] using hc

def blockOrthonormalBasis {κ : β → Type*} [∀ b, Fintype (κ b)]
    (u : ∀ b, OrthonormalBasis (κ b) ℂ (EuclideanSpace ℂ (ι b))) :
    OrthonormalBasis ((b : β) × κ b) ℂ (EuclideanSpace ℂ ((b : β) × ι b)) :=
  (Pi.orthonormalBasis u).map blockEuclideanCurry.symm

theorem blockDiagonal_map_basis {κ : β → Type*} [∀ b, Fintype (κ b)]
    (A : ∀ b, Matrix (ι b) (ι b) ℂ)
    (u v : ∀ b, OrthonormalBasis (κ b) ℂ (EuclideanSpace ℂ (ι b)))
    (s : ∀ b, κ b → ℂ) (hv : ∀ b i, (A b).toEuclideanLin (v b i) = s b i • u b i)
    (j : (b : β) × κ b) :
    (Matrix.blockDiagonal' A).toEuclideanLin (blockOrthonormalBasis v j) =
      s j.1 j.2 • blockOrthonormalBasis u j := by
  obtain ⟨b, i⟩ := j
  apply blockEuclideanCurry.injective
  ext c : 1
  rw [blockDiagonal_toEuclideanLin_curry]
  simp only [blockOrthonormalBasis, OrthonormalBasis.map_apply,
    LinearIsometryEquiv.apply_symm_apply, map_smul, Pi.orthonormalBasis_apply]
  by_cases h : b = c
  · subst c
    simpa only [PiLp.smul_apply, PiLp.single_eq_same] using hv b i
  · simp [h]

theorem blockDiagonal_singularValues_sum (A : ∀ b, Matrix (ι b) (ι b) ℂ)
    (hA : ∀ b, (A b).det ≠ 0) (φ : ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ x y, |φ x - φ y| ≤ K * |x - y|) :
    (∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ((b : β) × ι b))),
      φ ((Matrix.blockDiagonal' A).toEuclideanLin.singularValues i)) =
      ∑ b, ∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ (ι b))),
        φ ((A b).toEuclideanLin.singularValues i) := by
  have hinj (b) := toEuclideanLin_injective_of_det_ne_zero (A b) (hA b)
  choose u v hv hu using fun b => exists_canonical_positive_singular_bases (A b).toEuclideanLin (hinj b)
  have hv' := blockDiagonal_map_basis A u v
    (fun b i => ((A b).toEuclideanLin.singularValues i : ℂ)) hv
  have hu' (j : (b : β) × Fin (Module.finrank ℂ (EuclideanSpace ℂ (ι b)))) :
      (Matrix.blockDiagonal' A).toEuclideanLin.adjoint (blockOrthonormalBasis u j) =
      ((A j.1).toEuclideanLin.singularValues j.2 : ℂ) • blockOrthonormalBasis v j := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.blockDiagonal'_conjTranspose]
    apply blockDiagonal_map_basis (fun b => (A b).conjTranspose) v u
      (fun b i => ((A b).toEuclideanLin.singularValues i : ℂ))
    intro b i
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    exact hu b i
  rw [singularValues_sum_eq_of_indexed_singular_bases (Matrix.blockDiagonal' A).toEuclideanLin
    (blockDiagonal_toEuclideanLin_injective A hinj) (blockOrthonormalBasis u)
    (blockOrthonormalBasis v) (fun j => (A j.1).toEuclideanLin.singularValues j.2)
    (fun j => (A j.1).toEuclideanLin.singularValues_nonneg j.2) hv' hu' φ hK hφ]
  exact Fintype.sum_sigma _

theorem matrixCutoffPotential_blockDiagonal [∀ b, Nonempty (ι b)]
    (A : ∀ b, Matrix (ι b) (ι b) ℂ) (hA : ∀ b, (A b).det ≠ 0)
    {a : ℝ} (ha : 0 < a) :
    matrixCutoffPotential (Matrix.blockDiagonal' A) a =
      (∑ b, (Fintype.card (ι b) : ℝ) * matrixCutoffPotential (A b) a) /
        (∑ b, Fintype.card (ι b) : ℕ) := by
  unfold matrixCutoffPotential operatorCutoffPotential
  rw [blockDiagonal_singularValues_sum A hA (fun s => Real.log (max s a))
    (inv_nonneg.mpr ha.le) (log_max_lipschitz ha)]
  simp only [finrank_euclideanSpace, Fintype.card_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Fintype.card_pos (α := ι b)).ne')]

end CircularLawSection6
