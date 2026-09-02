import BernoulliLinearAlgebra.HodgeJacobi
import BernoulliLinearAlgebra.ChartPerturbation
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Concrete Jacobi complementary minors

This file removes the `ComplementaryMinorCertificate` input from the
Hodge--Jacobi estimates by proving the general complementary-minor identity
over `ℂ`.
-/

open Filter Topology
open scoped BigOperators Matrix Matrix.Norms.Frobenius Topology

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard

section BlockJacobi

variable {a b : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b]

set_option linter.style.haveILetI false in
/-- Jacobi's determinant identity in a block chart where the complementary
bottom-right block is invertible. -/
theorem det_inv_topLeft_eq_det_bottomRight_div_det
    (M : Matrix (a ⊕ b) (a ⊕ b) ℂ)
    (hM : IsUnit M.det) (hD : IsUnit M.toBlocks₂₂.det) :
    M⁻¹.toBlocks₁₁.det = M.det⁻¹ * M.toBlocks₂₂.det := by
  let A := M.toBlocks₁₁
  let B := M.toBlocks₁₂
  let C := M.toBlocks₂₁
  let D := M.toBlocks₂₂
  have hblocks : Matrix.fromBlocks A B C D = M := Matrix.fromBlocks_toBlocks M
  letI : Invertible D := Matrix.invertibleOfIsUnitDet D hD
  letI : Invertible M := Matrix.invertibleOfIsUnitDet M hM
  letI : Invertible (Matrix.fromBlocks A B C D) :=
    Invertible.copy (inferInstance : Invertible M) _ hblocks
  letI : Invertible (A - B * ⅟D * C) :=
    Matrix.invertibleOfFromBlocks₂₂Invertible A B C D
  letI : Invertible (A - B * ⅟D * C).det :=
    Matrix.detInvertibleOfInvertible (A - B * ⅟D * C)
  have hinv := Matrix.invOf_fromBlocks₂₂_eq A B C D
  have htop : M⁻¹.toBlocks₁₁ = ⅟(A - B * ⅟D * C) := by
    rw [← hblocks, ← Matrix.invOf_eq_nonsing_inv]
    rw [hinv, Matrix.toBlocks_fromBlocks₁₁]
  rw [htop, Matrix.det_invOf, ← hblocks, Matrix.det_fromBlocks₂₂ A B C D]
  change ⅟(A - B * ⅟D * C).det =
    (D.det * (A - B * ⅟D * C).det)⁻¹ * D.det
  have hS : (A - B * ⅟D * C).det ≠ 0 :=
    isUnit_iff_ne_zero.mp (Matrix.isUnit_det_of_invertible _)
  rw [invOf_eq_inv]
  field_simp [isUnit_iff_ne_zero.mp hD, hS]
  rw [div_self (isUnit_iff_ne_zero.mp hD)]

/-- Scalar perturbation commutes with taking the bottom-right block. -/
theorem toBlocks₂₂_scalarPerturb
    (M : Matrix (a ⊕ b) (a ⊕ b) ℂ) (z : ℂ) :
    (scalarPerturb M z).toBlocks₂₂ =
      scalarPerturb M.toBlocks₂₂ z := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [scalarPerturb, Matrix.toBlocks₂₂, Matrix.scalar_apply]
  · simp [scalarPerturb, Matrix.toBlocks₂₂, Matrix.scalar_apply, h]

/-- Scalar perturbation is continuous in its scalar parameter. -/
theorem continuous_scalarPerturb (M : Matrix a a ℂ) :
    Continuous (scalarPerturb M) := by
  rw [show scalarPerturb M = fun z ↦ M + z • (1 : Matrix a a ℂ) by
    funext z
    exact scalarPerturb_eq_add_smul_one M z]
  fun_prop

/-- The block Jacobi determinant identity without any invertibility
assumption on the complementary block.  The proof perturbs by `z I`, applies
the Schur-complement chart formula, and passes to `z → 0`. -/
theorem det_inv_topLeft_eq_det_bottomRight_div_det_of_isUnit
    (M : Matrix (a ⊕ b) (a ⊕ b) ℂ) (hM : IsUnit M.det) :
    M⁻¹.toBlocks₁₁.det = M.det⁻¹ * M.toBlocks₂₂.det := by
  let D := M.toBlocks₂₂
  rcases exists_scalarPerturbationSequence D with ⟨ε, hε0, hεD⟩
  let X : ℕ → Matrix (a ⊕ b) (a ⊕ b) ℂ := fun n ↦
    scalarPerturb M (ε n)
  have hX : Tendsto X atTop (nhds M) := by
    have h := (continuous_scalarPerturb M).continuousAt.tendsto.comp hε0
    change Tendsto (scalarPerturb M ∘ ε) atTop (nhds M)
    simpa only [scalarPerturb_zero] using h
  have hdet : Tendsto (fun n ↦ (X n).det) atTop (nhds M.det) :=
    continuous_id.matrix_det.continuousAt.tendsto.comp hX
  have hMne : M.det ≠ 0 := isUnit_iff_ne_zero.mp hM
  have hfull : ∀ᶠ n in atTop, IsUnit (X n).det :=
    (hdet.eventually_ne hMne).mono fun _ hn ↦ isUnit_iff_ne_zero.mpr hn
  have hchart : ∀ᶠ n in atTop,
      (X n)⁻¹.toBlocks₁₁.det =
        (X n).det⁻¹ * (X n).toBlocks₂₂.det := by
    filter_upwards [hfull] with n hn
    apply det_inv_topLeft_eq_det_bottomRight_div_det (X n) hn
    rw [toBlocks₂₂_scalarPerturb]
    exact isUnit_iff_ne_zero.mpr (hεD n)
  have hinv : Tendsto (fun n ↦ (X n)⁻¹) atTop (nhds M⁻¹) := by
    have hring : ContinuousAt Ring.inverse M.det := by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hMne
    exact (continuousAt_matrix_inv M hring).tendsto.comp hX
  have hleft : Tendsto (fun n ↦ (X n)⁻¹.toBlocks₁₁.det) atTop
      (nhds M⁻¹.toBlocks₁₁.det) := by
    exact continuous_id.matrix_submatrix Sum.inl Sum.inl |>.matrix_det
      |>.continuousAt.tendsto.comp hinv
  have hblock : Tendsto (fun n ↦ (X n).toBlocks₂₂.det) atTop
      (nhds M.toBlocks₂₂.det) := by
    exact continuous_id.matrix_submatrix Sum.inr Sum.inr |>.matrix_det
      |>.continuousAt.tendsto.comp hX
  have hinvdet : Tendsto (fun n ↦ (X n).det⁻¹) atTop (nhds M.det⁻¹) :=
    (continuousAt_inv₀ hMne).tendsto.comp hdet
  have hright : Tendsto
      (fun n ↦ (X n).det⁻¹ * (X n).toBlocks₂₂.det) atTop
      (nhds (M.det⁻¹ * M.toBlocks₂₂.det)) :=
    hinvdet.mul hblock
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.EventuallyEq.symm hchart))

end BlockJacobi

section OrderedSubsets

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- The order-preserving split of a finite ordered basis into a subset and
its complement. -/
def subsetSplitEquiv {k m : ℕ} (hm : m + k = Fintype.card ι)
    (s : powersetCard ι k) : Fin k ⊕ Fin m ≃ ι :=
  finSumEquivOfFinset s.prop (powersetCard.compl hm s).prop

@[simp]
theorem subsetSplitEquiv_inl {k m : ℕ}
    (hm : m + k = Fintype.card ι) (s : powersetCard ι k) (i : Fin k) :
    subsetSplitEquiv hm s (Sum.inl i) = ofFinEmbEquiv.symm s i := by
  rfl

@[simp]
theorem subsetSplitEquiv_inr {k m : ℕ}
    (hm : m + k = Fintype.card ι) (s : powersetCard ι k) (i : Fin m) :
    subsetSplitEquiv hm s (Sum.inr i) =
      ofFinEmbEquiv.symm (powersetCard.compl hm s) i := by
  rfl

/-- Reindex rows by `t, tᶜ` and columns by `s, sᶜ`.  The swap of `s`
and `t` is the one forced by inversion. -/
def jacobiReindexMatrix {k m : ℕ} (hm : m + k = Fintype.card ι)
    (E : Matrix ι ι ℂ) (s t : powersetCard ι k) :
    Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ :=
  E.submatrix (subsetSplitEquiv hm t) (subsetSplitEquiv hm s)

/-- The leading block of the inverse reindexed matrix is the requested
`(s,t)` minor of `E⁻¹`. -/
theorem det_inv_topLeft_jacobiReindexMatrix {k m : ℕ}
    (hm : m + k = Fintype.card ι) (E : Matrix ι ι ℂ)
    (s t : powersetCard ι k) :
    (jacobiReindexMatrix hm E s t)⁻¹.toBlocks₁₁.det =
      minor k E⁻¹ s t := by
  unfold jacobiReindexMatrix minor
  rw [Matrix.inv_submatrix_equiv]
  congr 1

/-- The trailing block of the reindexed matrix is the complementary minor,
with row and column subsets exchanged. -/
theorem det_bottomRight_jacobiReindexMatrix {k m : ℕ}
    (hm : m + k = Fintype.card ι) (E : Matrix ι ι ℂ)
    (s t : powersetCard ι k) :
    (jacobiReindexMatrix hm E s t).toBlocks₂₂.det =
      minor m E (powersetCard.compl hm t)
        (powersetCard.compl hm s) := by
  unfold jacobiReindexMatrix minor
  congr 1

/-- Independent row and column reindexing changes a determinant only by a
sign, hence preserves its complex norm. -/
theorem norm_det_jacobiReindexMatrix {k m : ℕ}
    (hm : m + k = Fintype.card ι) (E : Matrix ι ι ℂ)
    (s t : powersetCard ι k) :
    ‖(jacobiReindexMatrix hm E s t).det‖ = ‖E.det‖ := by
  change ‖(Matrix.reindex (subsetSplitEquiv hm t).symm
    (subsetSplitEquiv hm s).symm E).det‖ = ‖E.det‖
  rw [Matrix.det_reindex, norm_mul]
  let p : Equiv.Perm ι :=
    (subsetSplitEquiv hm s).symm.trans (subsetSplitEquiv hm t)
  have hp : ‖((Equiv.Perm.sign p : ℤ) : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs, Equiv.Perm.sign_abs]
    norm_num
  change ‖((Equiv.Perm.sign p : ℤ) : ℂ)‖ * ‖E.det‖ = ‖E.det‖
  rw [hp, one_mul]

end OrderedSubsets

section ConcreteCertificate

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- General-order Jacobi complementary-minor theorem over `ℂ`, packaged in
the interface used by `HodgeJacobi.lean`.  No complementary-minor identity is
assumed: it follows from the block formula, scalar perturbation, and the
row/column reindexing above. -/
noncomputable def complementaryMinorCertificate_of_isUnit
    (E : Matrix ι ι ℂ) (hE : IsUnit E.det)
    (k : ℕ) (hk : k ≤ Fintype.card ι) :
    ComplementaryMinorCertificate E k (Fintype.card ι - k)
      (Nat.sub_add_cancel hk) := by
  let hm : Fintype.card ι - k + k = Fintype.card ι :=
    Nat.sub_add_cancel hk
  let phase : powersetCard ι k → powersetCard ι k → ℂ := fun s t ↦
    (jacobiReindexMatrix hm E s t).det⁻¹ * E.det
  refine
    { det_isUnit := hE
      phase := phase
      phase_norm := ?_
      jacobi := ?_ }
  · intro s t
    unfold phase
    rw [norm_mul, norm_inv, norm_det_jacobiReindexMatrix]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (isUnit_iff_ne_zero.mp hE))
  · intro s t
    let M := jacobiReindexMatrix hm E s t
    have hEne : E.det ≠ 0 := isUnit_iff_ne_zero.mp hE
    have hMne : M.det ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [norm_det_jacobiReindexMatrix]
      exact norm_ne_zero_iff.mpr hEne
    have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr hMne
    have hblock :=
      det_inv_topLeft_eq_det_bottomRight_div_det_of_isUnit M hM
    rw [det_inv_topLeft_jacobiReindexMatrix,
      det_bottomRight_jacobiReindexMatrix] at hblock
    rw [hblock]
    unfold phase
    change M.det⁻¹ * _ =
      (M.det⁻¹ * E.det) * (E.det⁻¹ * _)
    symm
    rw [mul_assoc, ← mul_assoc E.det E.det⁻¹,
      mul_inv_cancel₀ hEne, one_mul]

/-- Exact Hodge--Jacobi compound norm identity with no certificate argument. -/
theorem compound_inverse_norm_eq_of_isUnit
    (E : Matrix ι ι ℂ) (hE : IsUnit E.det)
    (k : ℕ) (hk : k ≤ Fintype.card ι) :
    ‖compound k E⁻¹‖ =
      ‖E.det‖⁻¹ * ‖compound (Fintype.card ι - k) E‖ :=
  (complementaryMinorCertificate_of_isUnit E hE k hk).compound_inverse_norm_eq

/-- Uniform conditioning constructor using the concrete Jacobi theorem,
instead of a family of caller-supplied certificates. -/
theorem exteriorConditioning_of_hodgeBounds_isUnit
    {E : Matrix ι ι ℂ} {D L : ℝ}
    (hE : IsUnit E.det) (hD : 0 ≤ D)
    (hdet : ‖E.det‖⁻¹ ≤ D)
    (hforward : ∀ q : ℕ, ‖compound q E‖ ≤ L) :
    ExteriorConditioning E (max 1 (max L (D * L))) := by
  apply exteriorConditioning_of_hodgeBounds hD hdet hforward
  intro k hk
  exact complementaryMinorCertificate_of_isUnit E hE k hk

end ConcreteCertificate

end BernoulliLinearAlgebra
