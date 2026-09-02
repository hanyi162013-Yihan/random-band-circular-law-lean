import BernoulliLinearAlgebra.AllMinors
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix

/-!
# Arbitrary complex frames: deterministic amplification

This file formalizes the deterministic part of Section 9.2, equations
(9.47)--(9.55).  A frame is an isometric embedding between complex Euclidean
spaces.  Its completion to a unitary basis is made internally with
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`; no completion
matrix or certificate occurs in a caller-facing signature.

The parameter used for limits is `q + 1` (`q : ℕ`).  This is the cofinal
sequence `lambda -> infinity` and avoids a punctured-neighbourhood side
condition at `lambda = 0`.
-/

open scoped BigOperators Matrix ComplexConjugate

noncomputable section

namespace BernoulliSection9

open Filter Matrix Module Set Set.powersetCard
open BernoulliLinearAlgebra

/-- An `r`-frame in `C^n`, represented literally as an isometric linear
embedding of complex Euclidean spaces. -/
abbrev ComplexFrame (r n : ℕ) :=
  EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)

/-- The columns of an isometric frame. -/
def frameColumn {r n : ℕ} (U : ComplexFrame r n) (i : Fin r) :
    EuclideanSpace ℂ (Fin n) :=
  U (EuclideanSpace.basisFun (Fin r) ℂ i)

theorem frameColumn_orthonormal {r n : ℕ} (U : ComplexFrame r n) :
    Orthonormal ℂ (frameColumn U) := by
  change Orthonormal ℂ
    (fun i => U (EuclideanSpace.basisFun (Fin r) ℂ i))
  simpa [Function.comp_def] using
    (EuclideanSpace.basisFun (Fin r) ℂ).orthonormal.comp_linearIsometry U

/-- The canonical inclusion of the first `r` coordinates into `Fin n`. -/
def leadingEmbedding {r n : ℕ} (h : r ≤ n) : Fin r ↪ Fin n where
  toFun := Fin.castLE h
  inj' := Fin.castLE_injective h

/-- Extend the prescribed frame columns as an arbitrary function.  Only its
values on the range of `leadingEmbedding` are used in the basis-extension
argument. -/
def partialFrameFamily {r n : ℕ} (U : ComplexFrame r n) (h : r ≤ n) :
    Fin n → EuclideanSpace ℂ (Fin n) :=
  Function.extend (leadingEmbedding h) (frameColumn U) 0

@[simp]
theorem partialFrameFamily_leading {r n : ℕ} (U : ComplexFrame r n)
    (h : r ≤ n) (i : Fin r) :
    partialFrameFamily U h (leadingEmbedding h i) = frameColumn U i := by
  exact (leadingEmbedding h).injective.extend_apply (frameColumn U) 0 i

theorem partialFrameFamily_orthonormal {r n : ℕ} (U : ComplexFrame r n)
    (h : r ≤ n) :
    Orthonormal ℂ
      ((Set.range (leadingEmbedding h)).domRestrict (partialFrameFamily U h)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rcases i with ⟨_, ⟨a, rfl⟩⟩
  rcases j with ⟨_, ⟨b, rfl⟩⟩
  simp only [Set.domRestrict_apply, partialFrameFamily_leading]
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    simpa using orthonormal_iff_ite.mp (frameColumn_orthonormal U) a a
  · have hne :
        (⟨leadingEmbedding h a, ⟨a, rfl⟩⟩ : Set.range (leadingEmbedding h)) ≠
          ⟨leadingEmbedding h b, ⟨b, rfl⟩⟩ := by
        intro heq
        apply hab
        exact (leadingEmbedding h).injective (congrArg Subtype.val heq)
    rw [if_neg hne]
    simpa [hab] using orthonormal_iff_ite.mp (frameColumn_orthonormal U) a b

/-- An internally selected orthonormal completion of the columns of `U`.
The choice is noncomputable, but the theorem proving that it extends `U` is
part of this file rather than a caller-supplied certificate. -/
def completedFrameBasis {r n : ℕ} (U : ComplexFrame r n) (h : r ≤ n) :
    OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
  Classical.choose
    (Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (E := EuclideanSpace ℂ (Fin n)) (ι := Fin n) (by simp)
      (partialFrameFamily_orthonormal U h))

theorem completedFrameBasis_leading {r n : ℕ} (U : ComplexFrame r n)
    (h : r ≤ n) (i : Fin r) :
    completedFrameBasis U h (leadingEmbedding h i) = frameColumn U i := by
  have hs := Classical.choose_spec
    (Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (E := EuclideanSpace ℂ (Fin n)) (ι := Fin n) (by simp)
      (partialFrameFamily_orthonormal U h))
  rw [show completedFrameBasis U h = Classical.choose
      (Orthonormal.exists_orthonormalBasis_extension_of_card_eq
        (E := EuclideanSpace ℂ (Fin n)) (ι := Fin n) (by simp)
        (partialFrameFamily_orthonormal U h)) from rfl]
  exact (hs (leadingEmbedding h i) ⟨i, rfl⟩).trans
    (partialFrameFamily_leading U h i)

/-- The unitary matrix whose columns are the internal completion of `U`. -/
def completedFrameMatrix {r n : ℕ} (U : ComplexFrame r n) (h : r ≤ n) :
    Matrix (Fin n) (Fin n) ℂ :=
  (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix
    (completedFrameBasis U h)

theorem completedFrameMatrix_mem_unitary {r n : ℕ} (U : ComplexFrame r n)
    (h : r ≤ n) :
    completedFrameMatrix U h ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  exact OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
    (EuclideanSpace.basisFun (Fin n) ℂ) (completedFrameBasis U h)

theorem completedFrameMatrix_det_isUnit {r n : ℕ} (U : ComplexFrame r n)
    (h : r ≤ n) : IsUnit (completedFrameMatrix U h).det := by
  exact Matrix.UnitaryGroup.det_isUnit
    ⟨completedFrameMatrix U h, completedFrameMatrix_mem_unitary U h⟩

/-- The first `r` columns of the internally completed unitary matrix are
literally the columns of the caller's frame. -/
theorem completedFrameMatrix_leading {n r : ℕ} (U : ComplexFrame r n)
    (h : r ≤ n) (i : Fin n) (j : Fin r) :
    completedFrameMatrix U h i (leadingEmbedding h j) = frameColumn U j i := by
  rw [completedFrameMatrix, Basis.toMatrix_apply,
    completedFrameBasis_leading]
  exact EuclideanSpace.basisFun_repr (Fin n) ℂ (frameColumn U j) i

/-- Diagonal amplification: `lambda` on the first `r` completed frame
directions and `lambda^{-1}` on the others. -/
def amplificationDiagonal {n : ℕ} (r : ℕ) (lambda : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => if i.val < r then lambda else lambda⁻¹

/-- Equation (9.47): the artificial boundary relation associated with two
arbitrary frames. -/
def artificialTheta {r n : ℕ} (U V : ComplexFrame r n) (h : r ≤ n)
    (lambda : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  completedFrameMatrix V h * amplificationDiagonal r lambda *
    (completedFrameMatrix U h)ᴴ

theorem amplificationDiagonal_det_isUnit {n r : ℕ} (lambda : ℂ)
    (hlambda : lambda ≠ 0) :
    IsUnit (amplificationDiagonal (n := n) r lambda).det := by
  rw [amplificationDiagonal, Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by
    split_ifs
    · exact hlambda
    · exact inv_ne_zero hlambda

/-- The artificial relation is invertible for every nonzero amplification
parameter. -/
theorem artificialTheta_det_isUnit {r n : ℕ} (U V : ComplexFrame r n)
    (h : r ≤ n) (lambda : ℂ) (hlambda : lambda ≠ 0) :
    IsUnit (artificialTheta U V h lambda).det := by
  rw [artificialTheta, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose]
  exact ((completedFrameMatrix_det_isUnit V h).mul
    (amplificationDiagonal_det_isUnit lambda hlambda)).mul
      (completedFrameMatrix_det_isUnit U h).star

section DiagonalCompound

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

theorem minor_diagonal_apply (k : ℕ) (d : ι → ℂ)
    (s t : powersetCard ι k) :
    minor k (Matrix.diagonal d) s t =
      if s = t then ∏ i : Fin k, d (ofFinEmbEquiv.symm s i) else 0 := by
  classical
  by_cases hst : s = t
  · subst t
    simp only [if_pos rfl, minor]
    rw [Matrix.submatrix_diagonal d _ (ofFinEmbEquiv.symm s).injective,
      Matrix.det_diagonal]
    rfl
  · rw [if_neg hst]
    have hnot : ¬t.val ⊆ s.val := by
      intro hsub
      apply hst
      apply Subtype.ext
      exact (Finset.eq_of_subset_of_card_le hsub (by simpa [s.prop, t.prop])).symm
    rcases Finset.not_subset.mp hnot with ⟨x, hxt, hxs⟩
    rcases (mem_range_ofFinEmbEquiv_symm_iff_mem t x).mpr hxt with ⟨j, hj⟩
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i
    simp only [minor, Matrix.submatrix_apply, Matrix.diagonal_apply]
    rw [if_neg]
    intro heq
    apply hxs
    have hi_mem : ofFinEmbEquiv.symm s i ∈ s.val := by
      simpa [ofFinEmbEquiv_symm_apply] using
        (Finset.orderEmbOfFin_mem s.val s.prop i)
    simpa [← hj, ← heq] using hi_mem

theorem compound_diagonal_apply (k : ℕ) (d : ι → ℂ)
    (s t : powersetCard ι k) :
    compound k (Matrix.diagonal d) s t =
      if s = t then ∏ i : Fin k, d (ofFinEmbEquiv.symm s i) else 0 := by
  rw [compound_apply, minor_diagonal_apply]

end DiagonalCompound

section NormalizedCompounds

/-- The number `a(I)` of selected coordinates among the first `r`
coordinates, in the coordinate model for exterior powers. -/
def leadingCount {n k : ℕ} (r : ℕ) (s : powersetCard (Fin n) k) : ℕ :=
  (Finset.univ.filter fun i : Fin k =>
    (ofFinEmbEquiv.symm s i).val < r).card

theorem amplification_product_eq {n k r : ℕ}
    (s : powersetCard (Fin n) k) (x : ℂ) :
    (∏ i : Fin k,
      if (ofFinEmbEquiv.symm s i).val < r then x⁻¹ else x) =
      x⁻¹ ^ leadingCount r s * x ^ (k - leadingCount r s) := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  congr 2
  unfold leadingCount
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k)))
    (fun i : Fin k => (ofFinEmbEquiv.symm s i).val < r)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  have hle := Finset.card_filter_le (Finset.univ : Finset (Fin k))
    (fun i : Fin k => (ofFinEmbEquiv.symm s i).val < r)
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  omega

theorem normalized_amplification_product_eq {n k r : ℕ}
    (s : powersetCard (Fin n) k) (x : ℂ) (hx : x ≠ 0)
    (ha : leadingCount r s ≤ r) :
    x ^ r * (∏ i : Fin k,
      if (ofFinEmbEquiv.symm s i).val < r then x⁻¹ else x) =
      x ^ ((r - leadingCount r s) + (k - leadingCount r s)) := by
  rw [amplification_product_eq]
  rw [← mul_assoc, inv_pow]
  rw [← pow_sub₀ x hx ha]
  rw [← pow_add]

theorem leadingCount_le_rank {n k r : ℕ} (h : r ≤ n)
    (s : powersetCard (Fin n) k) : leadingCount r s ≤ r := by
  classical
  let selected : Finset (Fin n) :=
    (Finset.univ.filter fun i : Fin k =>
      (ofFinEmbEquiv.symm s i).val < r).map
        (ofFinEmbEquiv.symm s).toEmbedding
  have hsub : selected ⊆
      (Finset.univ.filter fun i : Fin n => i.val < r) := by
    intro x hx
    simp only [selected, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    rcases hx with ⟨i, hi, rfl⟩
    exact hi
  have hc := Finset.card_le_card hsub
  have hselected : selected.card = leadingCount r s := by
    simp only [selected, Finset.card_map, leadingCount]
  rw [hselected] at hc
  have htarget :
      (Finset.univ.filter fun i : Fin n => i.val < r).card = r := by
    simpa [min_eq_right h] using (Fin.card_filter_val_lt (n := n) (m := r))
  rwa [htarget] at hc

theorem leadingCount_le_degree {n k r : ℕ}
    (s : powersetCard (Fin n) k) : leadingCount r s ≤ k := by
  unfold leadingCount
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin k))
    (fun i : Fin k => (ofFinEmbEquiv.symm s i).val < r)

/-- The exterior coordinate indexed by the first `r` ambient coordinates. -/
def leadingPowerset {n r : ℕ} (h : r ≤ n) :
    powersetCard (Fin n) r :=
  ⟨Finset.univ.filter (fun i : Fin n => i.val < r), by
    simpa [min_eq_right h] using
      (Fin.card_filter_val_lt (n := n) (m := r))⟩

theorem leadingCount_eq_rank_iff {n r : ℕ} (h : r ≤ n)
    (s : powersetCard (Fin n) r) :
    leadingCount r s = r ↔ s = leadingPowerset h := by
  classical
  constructor
  · intro hc
    have hfilter :
        Finset.univ.filter (fun i : Fin r =>
          (ofFinEmbEquiv.symm s i).val < r) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      simpa only [Finset.card_univ, Fintype.card_fin, leadingCount] using hc.ge
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases (mem_range_ofFinEmbEquiv_symm_iff_mem s x).mpr hx with ⟨i, hi⟩
      have hip : (ofFinEmbEquiv.symm s i).val < r := by
        have : i ∈ Finset.univ.filter (fun j : Fin r =>
            (ofFinEmbEquiv.symm s j).val < r) := by
          rw [hfilter]
          simp
        simpa using (Finset.mem_filter.mp this).2
      change x ∈ (leadingPowerset h).val
      simp only [leadingPowerset, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [← hi] using hip
    · have ht :
          (Finset.univ.filter fun i : Fin n => i.val < r).card = r := by
        simpa [min_eq_right h] using
          (Fin.card_filter_val_lt (n := n) (m := r))
      simpa [leadingPowerset, ht, s.prop]
  · intro hs
    subst s
    unfold leadingCount
    have hall : ∀ i : Fin r,
        (ofFinEmbEquiv.symm (leadingPowerset h) i).val < r := by
      intro i
      have hi_mem : ofFinEmbEquiv.symm (leadingPowerset h) i ∈
          (leadingPowerset h).val := by
        simpa [ofFinEmbEquiv_symm_apply] using
          (Finset.orderEmbOfFin_mem (leadingPowerset h).val
            (leadingPowerset h).prop i)
      simpa [leadingPowerset] using hi_mem
    rw [Finset.filter_eq_self.mpr (fun i _ => hall i)]
    simp

/-- The reciprocal amplification parameter along the cofinal sequence
`lambda_q = q + 1`. -/
def inverseNaturalLambda (q : ℕ) : ℂ := 1 / ((q : ℂ) + 1)

/-- The cofinal amplification sequence `lambda_q = q + 1`, expressed as
the inverse of `inverseNaturalLambda`. -/
def naturalLambda (q : ℕ) : ℂ := (inverseNaturalLambda q)⁻¹

theorem inverseNaturalLambda_ne_zero (q : ℕ) :
    inverseNaturalLambda q ≠ 0 := by
  unfold inverseNaturalLambda
  apply one_div_ne_zero
  exact_mod_cast Nat.succ_ne_zero q

theorem inverseNaturalLambda_tendsto :
    Tendsto inverseNaturalLambda atTop (nhds 0) := by
  change Tendsto (fun q : ℕ => 1 / ((q : ℂ) + 1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The normalized central exterior matrix
`lambda_q^(-r) * compound k D(lambda_q)`. -/
def normalizedDiagonalCompound {n : ℕ} (r k q : ℕ) :
    Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ :=
  (inverseNaturalLambda q) ^ r •
    compound k (amplificationDiagonal (n := n) r (naturalLambda q))

theorem normalizedDiagonalCompound_apply {n r k q : ℕ}
    (h : r ≤ n) (s t : powersetCard (Fin n) k) :
    normalizedDiagonalCompound (n := n) r k q s t =
      if s = t then
        (inverseNaturalLambda q) ^
          ((r - leadingCount r s) + (k - leadingCount r s))
      else 0 := by
  classical
  rw [normalizedDiagonalCompound, Matrix.smul_apply, amplificationDiagonal,
    compound_diagonal_apply]
  by_cases hst : s = t
  · rw [if_pos hst, if_pos hst]
    subst t
    have hx := inverseNaturalLambda_ne_zero q
    simp only [naturalLambda, inv_inv, smul_eq_mul]
    exact normalized_amplification_product_eq s (inverseNaturalLambda q) hx
      (leadingCount_le_rank h s)
  · simp [hst]

/-- The coordinate rank-one projection onto the wedge of the first `r`
coordinate vectors. -/
def leadingExteriorProjection {n r : ℕ} (h : r ≤ n) :
    Matrix (powersetCard (Fin n) r) (powersetCard (Fin n) r) ℂ :=
  fun s t => if s = leadingPowerset h ∧ t = leadingPowerset h then 1 else 0

/-- Equation (9.51), in coordinate/compound form, for every exterior degree
different from `r`.  Entrywise convergence is equivalent to convergence in
any norm because the space is fixed and finite-dimensional. -/
theorem normalizedDiagonalCompound_otherDegree_tendsto {n r k : ℕ}
    (h : r ≤ n) (hkr : k ≠ r) (s t : powersetCard (Fin n) k) :
    Tendsto (fun q => normalizedDiagonalCompound (n := n) r k q s t)
      atTop (nhds 0) := by
  by_cases hst : s = t
  · subst t
    rw [show (fun q => normalizedDiagonalCompound (n := n) r k q s s) =
        (fun q => (inverseNaturalLambda q) ^
          ((r - leadingCount r s) + (k - leadingCount r s))) by
      funext q
      simp [normalizedDiagonalCompound_apply h]]
    have ha_r := leadingCount_le_rank h s
    have ha_k := leadingCount_le_degree (r := r) s
    have he : 0 < (r - leadingCount r s) + (k - leadingCount r s) := by
      omega
    simpa [zero_pow he.ne'] using
      inverseNaturalLambda_tendsto.pow
        ((r - leadingCount r s) + (k - leadingCount r s))
  · rw [show (fun q => normalizedDiagonalCompound (n := n) r k q s t) =
        (fun _ => 0) by
      funext q
      simp [normalizedDiagonalCompound_apply h, hst]]
    exact tendsto_const_nhds

/-- Equation (9.52), in coordinate/compound form: at degree `r`, the
normalized central matrix converges to the projection onto the leading
exterior coordinate. -/
theorem normalizedDiagonalCompound_rankDegree_tendsto {n r : ℕ}
    (h : r ≤ n) (s t : powersetCard (Fin n) r) :
    Tendsto (fun q => normalizedDiagonalCompound (n := n) r r q s t)
      atTop (nhds (leadingExteriorProjection h s t)) := by
  by_cases hst : s = t
  · subst t
    by_cases hs : s = leadingPowerset h
    · subst s
      have hc : leadingCount r (leadingPowerset h) = r :=
        (leadingCount_eq_rank_iff h (leadingPowerset h)).2 rfl
      rw [show (fun q => normalizedDiagonalCompound (n := n) r r q
          (leadingPowerset h) (leadingPowerset h)) = (fun _ => 1) by
        funext q
        rw [normalizedDiagonalCompound_apply h]
        simp [hc]]
      simpa [leadingExteriorProjection] using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1))
    · rw [show (fun q => normalizedDiagonalCompound (n := n) r r q s s) =
          (fun q => (inverseNaturalLambda q) ^
            ((r - leadingCount r s) + (r - leadingCount r s))) by
        funext q
        simp [normalizedDiagonalCompound_apply h]]
      have ha := leadingCount_le_rank h s
      have hane : leadingCount r s ≠ r := by
        simpa [leadingCount_eq_rank_iff h] using hs
      have he : 0 < (r - leadingCount r s) + (r - leadingCount r s) := by
        omega
      have ht := inverseNaturalLambda_tendsto.pow
        ((r - leadingCount r s) + (r - leadingCount r s))
      simpa [zero_pow he.ne', leadingExteriorProjection, hs] using ht
  · rw [show (fun q => normalizedDiagonalCompound (n := n) r r q s t) =
        (fun _ => 0) by
      funext q
      simp [normalizedDiagonalCompound_apply h, hst]]
    have hp : leadingExteriorProjection h s t = 0 := by
      rw [leadingExteriorProjection, if_neg]
      intro hboth
      exact hst (hboth.1.trans hboth.2.symm)
    rw [hp]
    exact
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))

/-- The normalized exterior/compound matrix
`lambda_q^(-r) * compound k Theta(lambda_q)`. -/
def normalizedArtificialCompound {n r : ℕ}
    (U V : ComplexFrame r n) (h : r ≤ n) (k q : ℕ) :
    Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ :=
  (inverseNaturalLambda q) ^ r •
    compound k (artificialTheta U V h (naturalLambda q))

theorem normalizedArtificialCompound_eq {n r : ℕ}
    (U V : ComplexFrame r n) (h : r ≤ n) (k q : ℕ) :
    normalizedArtificialCompound U V h k q =
      compound k (completedFrameMatrix V h) *
        normalizedDiagonalCompound (n := n) r k q *
          compound k ((completedFrameMatrix U h)ᴴ) := by
  rw [normalizedArtificialCompound, artificialTheta, compound_mul,
    compound_mul, normalizedDiagonalCompound]
  rw [mul_smul_comm, smul_mul_assoc]

theorem tendsto_fixed_mul_entry {d : Type*} [Fintype d]
    (A B L : Matrix d d ℂ) (M : ℕ → Matrix d d ℂ)
    (hM : ∀ i j, Tendsto (fun q => M q i j) atTop (nhds (L i j)))
    (s t : d) :
    Tendsto (fun q => (A * M q * B) s t) atTop
      (nhds ((A * L * B) s t)) := by
  simp only [Matrix.mul_apply]
  apply tendsto_finset_sum Finset.univ
  intro j _
  apply Filter.Tendsto.mul_const
  apply tendsto_finset_sum Finset.univ
  intro i _
  exact (hM i j).const_mul (A s i)

/-- The coordinate matrix of the rank-one exterior operator
`|V-hat><U-hat|`.  Both unitary completions are selected internally. -/
def frameExteriorRankOne {n r : ℕ}
    (U V : ComplexFrame r n) (h : r ≤ n) :
    Matrix (powersetCard (Fin n) r) (powersetCard (Fin n) r) ℂ :=
  compound r (completedFrameMatrix V h) * leadingExteriorProjection h *
    compound r ((completedFrameMatrix U h)ᴴ)

/-- Equation (9.51) for arbitrary complex frames. -/
theorem normalizedArtificialCompound_otherDegree_tendsto {n r k : ℕ}
    (U V : ComplexFrame r n) (h : r ≤ n) (hkr : k ≠ r)
    (s t : powersetCard (Fin n) k) :
    Tendsto (fun q => normalizedArtificialCompound U V h k q s t)
      atTop (nhds 0) := by
  rw [show (fun q => normalizedArtificialCompound U V h k q s t) =
      (fun q => (compound k (completedFrameMatrix V h) *
        normalizedDiagonalCompound (n := n) r k q *
        compound k ((completedFrameMatrix U h)ᴴ)) s t) by
    funext q
    rw [normalizedArtificialCompound_eq]]
  have ht := tendsto_fixed_mul_entry
    (compound k (completedFrameMatrix V h))
    (compound k ((completedFrameMatrix U h)ᴴ))
    (0 : Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ)
    (fun q => normalizedDiagonalCompound (n := n) r k q)
    (fun i j => normalizedDiagonalCompound_otherDegree_tendsto h hkr i j) s t
  simpa using ht

/-- Equation (9.52) for arbitrary complex frames. -/
theorem normalizedArtificialCompound_rankDegree_tendsto {n r : ℕ}
    (U V : ComplexFrame r n) (h : r ≤ n)
    (s t : powersetCard (Fin n) r) :
    Tendsto (fun q => normalizedArtificialCompound U V h r q s t)
      atTop (nhds (frameExteriorRankOne U V h s t)) := by
  rw [show (fun q => normalizedArtificialCompound U V h r q s t) =
      (fun q => (compound r (completedFrameMatrix V h) *
        normalizedDiagonalCompound (n := n) r r q *
        compound r ((completedFrameMatrix U h)ᴴ)) s t) by
    funext q
    rw [normalizedArtificialCompound_eq]]
  exact tendsto_fixed_mul_entry
    (compound r (completedFrameMatrix V h))
    (compound r ((completedFrameMatrix U h)ᴴ))
    (leadingExteriorProjection h)
    (fun q => normalizedDiagonalCompound (n := n) r r q)
    (fun i j => normalizedDiagonalCompound_rankDegree_tendsto h i j) s t

/-! The paper states (9.51)--(9.52) in operator norm.  The entrywise limits
above are the convenient algebraic form; the next two theorems make the
finite-dimensional passage to the Euclidean operator norm explicit. -/

open scoped Matrix.Norms.L2Operator in
theorem normalizedArtificialCompound_otherDegree_opNorm_tendsto
    {n r k : ℕ}
    (U V : ComplexFrame r n) (h : r ≤ n) (hkr : k ≠ r) :
    Tendsto
      (fun q => ‖normalizedArtificialCompound U V h k q‖)
      atTop (nhds 0) := by
  classical
  have hmatrix :
      Tendsto
        (fun q => normalizedArtificialCompound U V h k q)
        atTop
        (nhds
          (0 : Matrix (powersetCard (Fin n) k)
            (powersetCard (Fin n) k) ℂ)) := by
    apply tendsto_pi_nhds.mpr
    intro s
    apply tendsto_pi_nhds.mpr
    intro t
    exact normalizedArtificialCompound_otherDegree_tendsto
      U V h hkr s t
  simpa using hmatrix.norm

open scoped Matrix.Norms.L2Operator in
theorem normalizedArtificialCompound_rankDegree_opNorm_tendsto
    {n r : ℕ}
    (U V : ComplexFrame r n) (h : r ≤ n) :
    Tendsto
      (fun q =>
        ‖normalizedArtificialCompound U V h r q -
          frameExteriorRankOne U V h‖)
      atTop (nhds 0) := by
  classical
  have hmatrix :
      Tendsto
        (fun q => normalizedArtificialCompound U V h r q)
        atTop
        (nhds (frameExteriorRankOne U V h)) := by
    apply tendsto_pi_nhds.mpr
    intro s
    apply tendsto_pi_nhds.mpr
    intro t
    exact normalizedArtificialCompound_rankDegree_tendsto U V h s t
  have hconst :
      Tendsto
        (fun _ : ℕ => frameExteriorRankOne U V h)
        atTop
        (nhds (frameExteriorRankOne U V h)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconst).norm

end NormalizedCompounds

section FiniteCoefficientLimits

/-- The real reciprocal amplification parameter used in the graph-volume
identity (9.54). -/
def inverseNaturalLambdaReal (q : ℕ) : ℝ := 1 / ((q : ℝ) + 1)

theorem inverseNaturalLambdaReal_tendsto :
    Tendsto inverseNaturalLambdaReal atTop (nhds 0) := by
  change Tendsto (fun q : ℕ => 1 / ((q : ℝ) + 1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The exact normalized graph-volume expression on the right side of
(9.54), for ambient dimension `2 * W` and `lambda_q = q + 1`. -/
def normalizedGraphProduct (W q : ℕ) : ℝ :=
  (1 + inverseNaturalLambdaReal q ^ 2) ^ W

/-- The square of the normalized graph-volume product, written directly
from `r` singular values `lambda_q` and `2 * W - r` singular values
`lambda_q⁻¹`. -/
def normalizedGraphMultiplicityProduct (W r q : ℕ) : ℝ :=
  inverseNaturalLambdaReal q ^ (2 * r) *
    (1 + (inverseNaturalLambdaReal q)⁻¹ ^ 2) ^ r *
      (1 + inverseNaturalLambdaReal q ^ 2) ^ (2 * W - r)

private theorem graph_scalar_identity (x : ℝ) (hx : x ≠ 0) (r : ℕ) :
    x ^ (2 * r) * (1 + x⁻¹ ^ 2) ^ r = (1 + x ^ 2) ^ r := by
  rw [show x ^ (2 * r) = (x ^ 2) ^ r by exact pow_mul x 2 r,
    ← mul_pow]
  congr 1
  field_simp
  ring

/-- The exact multiplicity computation underlying (9.54). -/
theorem normalizedGraphMultiplicityProduct_eq (W r q : ℕ)
    (hr : r ≤ 2 * W) :
    normalizedGraphMultiplicityProduct W r q =
      (1 + inverseNaturalLambdaReal q ^ 2) ^ (2 * W) := by
  rw [normalizedGraphMultiplicityProduct,
    graph_scalar_identity _ (by
      unfold inverseNaturalLambdaReal
      positivity)]
  rw [← pow_add]
  congr 2
  omega

/-- Thus `normalizedGraphProduct` is exactly the nonnegative square root
of the normalized graph-volume square coming from the prescribed singular
value multiplicities. -/
theorem normalizedGraphProduct_sq_eq_multiplicityProduct (W r q : ℕ)
    (hr : r ≤ 2 * W) :
    normalizedGraphProduct W q ^ 2 =
      normalizedGraphMultiplicityProduct W r q := by
  rw [normalizedGraphMultiplicityProduct_eq W r q hr,
    normalizedGraphProduct]
  calc
    ((1 + inverseNaturalLambdaReal q ^ 2) ^ W) ^ 2 =
        (1 + inverseNaturalLambdaReal q ^ 2) ^ (W * 2) :=
      (pow_mul _ W 2).symm
    _ = (1 + inverseNaturalLambdaReal q ^ 2) ^ (2 * W) := by
      rw [Nat.mul_comm W 2]

/-- The deterministic graph-volume limit (9.54). -/
theorem normalizedGraphProduct_tendsto (W : ℕ) :
    Tendsto (normalizedGraphProduct W) atTop (nhds 1) := by
  have ht : Tendsto (fun q => 1 + inverseNaturalLambdaReal q ^ 2)
      atTop (nhds (1 + 0 ^ 2)) :=
    tendsto_const_nhds.add (inverseNaturalLambdaReal_tendsto.pow 2)
  change Tendsto (fun q =>
    (1 + inverseNaturalLambdaReal q ^ 2) ^ W) atTop (nhds 1)
  simpa using ht.pow W

/-- Coordinatewise convergence in a fixed finite-dimensional coefficient
space implies convergence of its Euclidean norm. -/
theorem finiteCoefficientNorm_tendsto {a : Type*} [Fintype a]
    (c : ℕ → a → ℂ) (c₀ : a → ℂ)
    (hc : ∀ i, Tendsto (fun q => c q i) atTop (nhds (c₀ i))) :
    Tendsto
      (fun q => ‖(WithLp.toLp 2 (c q) : EuclideanSpace ℂ a)‖)
      atTop (nhds ‖(WithLp.toLp 2 c₀ : EuclideanSpace ℂ a)‖) := by
  simp_rw [EuclideanSpace.norm_eq]
  apply Real.continuous_sqrt.continuousAt.tendsto.comp
  apply tendsto_finset_sum Finset.univ
  intro i _
  exact (hc i).norm.pow 2

theorem tendsto_trace_mul {d : Type*} [Fintype d]
    (A L : Matrix d d ℂ) (M : ℕ → Matrix d d ℂ)
    (hM : ∀ i j, Tendsto (fun q => M q i j) atTop (nhds (L i j))) :
    Tendsto (fun q => Matrix.trace (A * M q)) atTop
      (nhds (Matrix.trace (A * L))) := by
  simp only [Matrix.trace, Matrix.mul_apply]
  apply tendsto_finset_sum Finset.univ
  intro i _
  apply tendsto_finset_sum Finset.univ
  intro j _
  exact (hM j i).const_mul (A i j)

/-- The coefficient of a normalized artificial exterior polynomial.  The
finite type `a` indexes its monomials and `Q k b` is the `k`th exterior
coefficient tensor of monomial `b`. -/
def normalizedExteriorCoefficient {a : Type*} [Fintype a]
    {n r : ℕ} (U V : ComplexFrame r n) (h : r ≤ n)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ)
    (q : ℕ) (b : a) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k *
    Matrix.trace (Q k b * normalizedArtificialCompound U V h k q)

/-- The target coefficient `(-1)^r <U-hat, Q^(r) V-hat>` in coordinate
trace form. -/
def limitingFrameCoefficient {a : Type*} [Fintype a]
    {n r : ℕ} (U V : ComplexFrame r n) (h : r ≤ n)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ)
    (b : a) : ℂ :=
  (-1 : ℂ) ^ r * Matrix.trace (Q r b * frameExteriorRankOne U V h)

/-- Equation (9.53): every monomial coefficient of the normalized artificial
polynomial converges to its arbitrary-frame coefficient. -/
theorem normalizedExteriorCoefficient_tendsto {a : Type*} [Fintype a]
    {n r : ℕ} (U V : ComplexFrame r n) (h : r ≤ n)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ)
    (b : a) :
    Tendsto (fun q => normalizedExteriorCoefficient U V h Q q b)
      atTop (nhds (limitingFrameCoefficient U V h Q b)) := by
  let z : ℂ := limitingFrameCoefficient U V h Q b
  have hterm : ∀ k ∈ Finset.range (n + 1),
      Tendsto
        (fun q => (-1 : ℂ) ^ k *
          Matrix.trace
            (Q k b * normalizedArtificialCompound U V h k q))
        atTop (nhds (if k = r then z else 0)) := by
    intro k hk
    by_cases hkr : k = r
    · subst k
      have ht := tendsto_trace_mul (Q r b) (frameExteriorRankOne U V h)
        (fun q => normalizedArtificialCompound U V h r q)
        (fun i j => normalizedArtificialCompound_rankDegree_tendsto U V h i j)
      simpa [z, limitingFrameCoefficient] using
        ht.const_mul ((-1 : ℂ) ^ r)
    · have ht := tendsto_trace_mul (Q k b)
        (0 : Matrix (powersetCard (Fin n) k)
          (powersetCard (Fin n) k) ℂ)
        (fun q => normalizedArtificialCompound U V h k q)
        (fun i j =>
          normalizedArtificialCompound_otherDegree_tendsto U V h hkr i j)
      simpa [hkr] using ht.const_mul ((-1 : ℂ) ^ k)
  have hsum := tendsto_finset_sum (Finset.range (n + 1)) hterm
  have hrmem : r ∈ Finset.range (n + 1) := by
    simpa [Finset.mem_range, Nat.lt_succ_iff] using h
  simpa [normalizedExteriorCoefficient, limitingFrameCoefficient,
    z, hrmem] using hsum

/-- Equation (9.55): because the monomial index is finite, the normalized
artificial coefficient norm converges to the arbitrary-frame coefficient
norm. -/
theorem normalizedExteriorCoefficientNorm_tendsto
    {a : Type*} [Fintype a] {n r : ℕ}
    (U V : ComplexFrame r n) (h : r ≤ n)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ) :
    Tendsto
      (fun q => ‖(WithLp.toLp 2
        (fun b => normalizedExteriorCoefficient U V h Q q b) :
          EuclideanSpace ℂ a)‖)
      atTop
      (nhds ‖(WithLp.toLp 2
        (fun b => limitingFrameCoefficient U V h Q b) :
          EuclideanSpace ℂ a)‖) := by
  exact finiteCoefficientNorm_tendsto _ _
    (fun b => normalizedExteriorCoefficient_tendsto U V h Q b)

end FiniteCoefficientLimits

end BernoulliSection9
