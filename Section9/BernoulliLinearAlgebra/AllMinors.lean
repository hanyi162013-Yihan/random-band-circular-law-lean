import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Complex.Basic

/-!
# All-minor and compound-matrix identities

This file formalizes the exact linear-algebraic core of Lemma 7.5 and
equations (9.46), (9.84), and (9.85) of the paper.  The `k`th compound matrix
is constructed as the matrix of the induced map on the `k`th exterior
power.  Its entries are proved to be the corresponding minors, so
functoriality of exterior powers gives Cauchy--Binet without any
invertibility assumption.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Module Set Set.powersetCard

section Compound

variable {R : Type*} [CommRing R]
variable {ι κ μ : Type*}
variable [Fintype ι] [DecidableEq ι] [LinearOrder ι]
variable [Fintype κ] [DecidableEq κ] [LinearOrder κ]
variable [Fintype μ] [DecidableEq μ] [LinearOrder μ]

/-- The minor with row set `s` and column set `t`, both put in increasing order. -/
def minor (k : ℕ) (A : Matrix κ ι R)
    (s : powersetCard κ k) (t : powersetCard ι k) : R :=
  (A.submatrix (ofFinEmbEquiv.symm s) (ofFinEmbEquiv.symm t)).det

/-- The `k`th compound matrix, defined intrinsically using the exterior-power functor. -/
def compound (k : ℕ) (A : Matrix κ ι R) :
    Matrix (powersetCard κ k) (powersetCard ι k) R :=
  LinearMap.toMatrix
    ((Pi.basisFun R ι).exteriorPower k)
    ((Pi.basisFun R κ).exteriorPower k)
    (exteriorPower.map k (Matrix.toLin' A))

omit [DecidableEq κ] in
/-- Entries of the compound matrix are the corresponding minors. -/
theorem compound_apply (k : ℕ) (A : Matrix κ ι R)
    (s : powersetCard κ k) (t : powersetCard ι k) :
    compound k A s t = minor k A s t := by
  simp only [compound, LinearMap.toMatrix_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.basis_repr_apply]
  rw [exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti]
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Matrix.toLin'_apply]

omit [DecidableEq κ] in
/-- Functoriality of compound matrices. -/
theorem compound_mul (k : ℕ) (A : Matrix κ ι R) (B : Matrix ι μ R) :
    compound k (A * B) = compound k A * compound k B := by
  simp only [compound, Matrix.toLin'_mul, exteriorPower.map_comp]
  exact LinearMap.toMatrix_comp
    ((Pi.basisFun R μ).exteriorPower k)
    ((Pi.basisFun R ι).exteriorPower k)
    ((Pi.basisFun R κ).exteriorPower k)
    (exteriorPower.map k (Matrix.toLin' A))
    (exteriorPower.map k (Matrix.toLin' B))

omit [DecidableEq κ] in
/-- Cauchy--Binet, indexed by increasing row/column subsets. -/
theorem minor_mul (k : ℕ) (A : Matrix κ ι R) (B : Matrix ι μ R)
    (s : powersetCard κ k) (t : powersetCard μ k) :
    minor k (A * B) s t =
      ∑ u : powersetCard ι k, minor k A s u * minor k B u t := by
  have h := congr_fun₂ (compound_mul k A B) s t
  simpa only [compound_apply, Matrix.mul_apply] using h

end Compound

section ComplexCompound

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A minor of a conjugate transpose is the conjugate of the transposed minor. -/
theorem minor_conjTranspose (k : ℕ) (A : Matrix ι ι ℂ)
    (s t : powersetCard ι k) :
    minor k Aᴴ s t = star (minor k A t s) := by
  unfold minor
  rw [← Matrix.det_conjTranspose]
  congr 1

/-- Squared Hilbert--Schmidt energy of the `k`th compound matrix. -/
def compoundEnergy (k : ℕ) (A : Matrix ι ι ℂ) : ℂ :=
  ∑ s : powersetCard ι k, ∑ t : powersetCard ι k,
    star (minor k A s t) * minor k A s t

/-- Cauchy--Binet for a Gram principal minor: it is the sum of squared minors
with the prescribed column set. -/
theorem gram_minor_eq_sum_sq (k : ℕ) (A : Matrix ι ι ℂ)
    (t : powersetCard ι k) :
    minor k (Aᴴ * A) t t =
      ∑ s : powersetCard ι k, star (minor k A s t) * minor k A s t := by
  rw [minor_mul]
  simp_rw [minor_conjTranspose]

omit [LinearOrder ι] in
/-- Principal-minor expansion of `det (I + M)`. -/
theorem det_one_add_eq_sum_principalMinors (M : Matrix ι ι ℂ) :
    det (1 + M) =
      ∑ s : Finset ι,
        (M.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det := by
  let D := (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ)
  rw [add_comm]
  change D (fun i => M i + (1 : Matrix ι ι ℂ) i) = _
  conv_lhs =>
    rw [show (fun i => M i + (1 : Matrix ι ι ℂ) i) =
      (fun i => M i) + (fun i => (1 : Matrix ι ι ℂ) i) from rfl]
  rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  change det (Matrix.of (s.piecewise M.row (1 : Matrix ι ι ℂ).row)) = _
  exact Matrix.det_piecewise_one_eq_submatrix_det M s

omit [Fintype ι] in
/-- Reindexing an increasing minor by the subtype of its underlying finset
does not change its determinant. -/
theorem minor_self_eq_principal (k : ℕ) (M : Matrix ι ι ℂ)
    (s : powersetCard ι k) :
    minor k M s s =
      (M.submatrix (Subtype.val : s.val → ι) (Subtype.val : s.val → ι)).det := by
  unfold minor
  rw [← Matrix.det_submatrix_equiv_self (orderIsoOfFin s).toEquiv
    (M.submatrix (Subtype.val : s.val → ι) (Subtype.val : s.val → ι))]
  congr 1

/-- The sum of squared absolute values of all square minors, with the degree
bundled by the cardinality of the column finset.  This is definitionally the
paper's triple sum over `k`, row sets, and column sets. -/
def allMinorEnergy (A : Matrix ι ι ℂ) : ℂ :=
  ∑ t : Finset ι,
    ∑ s : powersetCard ι t.card,
      star (minor t.card A s (ofCard rfl)) * minor t.card A s (ofCard rfl)

/-- The determinant of `I + Aᴴ A` is the sum of the squared
Hilbert--Schmidt energies of all compound matrices.  This is (9.84), and
`compound_apply` is (9.85). -/
theorem det_one_add_gram_eq_sum_compoundEnergy (A : Matrix ι ι ℂ) :
    det (1 + Aᴴ * A) = allMinorEnergy A := by
  unfold allMinorEnergy
  rw [det_one_add_eq_sum_principalMinors]
  apply Finset.sum_congr rfl
  intro t _
  let t' : powersetCard ι t.card := ofCard rfl
  change
    ((Aᴴ * A).submatrix (Subtype.val : t'.val → ι)
      (Subtype.val : t'.val → ι)).det =
      ∑ s : powersetCard ι t.card,
        star (minor t.card A s t') * minor t.card A s t'
  rw [← minor_self_eq_principal t.card (Aᴴ * A) t']
  exact gram_minor_eq_sum_sq t.card A t'

omit [DecidableEq ι] in
/-- The bundled all-minor energy is exactly the degree-by-degree sum of
Hilbert--Schmidt energies of the compound matrices.  This theorem exposes
the literal `k = 0, …, card ι` form used in equation (9.84). -/
theorem allMinorEnergy_eq_sum_compoundEnergy (A : Matrix ι ι ℂ) :
    allMinorEnergy A =
      ∑ k ∈ Finset.range (Fintype.card ι + 1), compoundEnergy k A := by
  unfold allMinorEnergy
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.range (Fintype.card ι + 1))
    (g := Finset.card) (fun t : Finset ι => by
      intro _
      simp only [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.card_le_univ t))]
  apply Finset.sum_congr rfl
  intro k _
  unfold compoundEnergy
  rw [Finset.sum_comm]
  refine Finset.sum_bij
    (s := Finset.univ.filter (fun t : Finset ι => t.card = k))
    (t := Finset.univ)
    (fun t ht =>
      (⟨t, (Finset.mem_filter.mp ht).2⟩ : powersetCard ι k)) ?_ ?_ ?_ ?_
  · intro _ _
    simp
  · intro t₁ _ t₂ _ h
    exact congr_arg Subtype.val h
  · intro t' _
    refine ⟨t'.val, ?_, ?_⟩
    · simp
    · apply Subtype.ext
      rfl
  · intro t ht
    have hcard : t.card = k := (Finset.mem_filter.mp ht).2
    subst k
    rfl

/-- Equation (9.84), written exactly as the finite sum over exterior degree. -/
theorem det_one_add_gram_eq_sum_compoundEnergy_byDegree
    (A : Matrix ι ι ℂ) :
    det (1 + Aᴴ * A) =
      ∑ k ∈ Finset.range (Fintype.card ι + 1), compoundEnergy k A := by
  rw [det_one_add_gram_eq_sum_compoundEnergy,
    allMinorEnergy_eq_sum_compoundEnergy]

/-- Equation (9.46): the same identity written as one sum over all minors. -/
theorem all_minors_cauchy_binet (A : Matrix ι ι ℂ) :
    det (1 + Aᴴ * A) = allMinorEnergy A :=
  det_one_add_gram_eq_sum_compoundEnergy A

/-- The exterior-degree trace sum, bundled by the underlying finset.  It is
the finite sum `Σ k, (-1)^k tr(∧^k A)` used in (9.70). -/
def signedCompoundTrace (A : Matrix ι ι ℂ) : ℂ :=
  ∑ s : Finset ι, (-1 : ℂ) ^ s.card *
    compound s.card A (ofCard rfl) (ofCard rfl)

/-- The standard exterior identity
`det (I - A) = Σ k, (-1)^k tr(∧^k A)`, in bundled finite form. -/
theorem det_one_sub_eq_signedCompoundTrace (A : Matrix ι ι ℂ) :
    det (1 - A) = signedCompoundTrace A := by
  rw [show (1 - A) = 1 + (-A) by abel,
    det_one_add_eq_sum_principalMinors]
  unfold signedCompoundTrace
  apply Finset.sum_congr rfl
  intro s _
  rw [compound_apply, minor_self_eq_principal]
  rw [Matrix.submatrix_neg]
  change det (-(A.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι))) = _
  rw [Matrix.det_neg, Fintype.card_coe]
  rfl

end ComplexCompound

end BernoulliLinearAlgebra
