import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Complex.Basic

/-!
# Finite exterior powers in coordinates

This file supplies the coordinate model used throughout the formalization:
the matrix of `exteriorPower.map k A` is the `k`th compound matrix of `A`.
Its entries are minors.  This avoids introducing an inner product on the
abstract exterior algebra and follows exactly the coordinates used in
Section 4 of the manuscript.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Module Set Set.powersetCard

section Compound

variable {R : Type*} [CommRing R]
variable {ι κ μ : Type*}
variable [Fintype ι] [DecidableEq ι] [LinearOrder ι]
variable [Fintype κ] [DecidableEq κ] [LinearOrder κ]
variable [Fintype μ] [DecidableEq μ] [LinearOrder μ]

/-- The minor with row and column sets put in increasing order. -/
def minor (k : ℕ) (A : Matrix κ ι R)
    (s : powersetCard κ k) (t : powersetCard ι k) : R :=
  (A.submatrix (ofFinEmbEquiv.symm s) (ofFinEmbEquiv.symm t)).det

/-- Matrix of the induced map on the `k`th exterior power. -/
def compound (k : ℕ) (A : Matrix κ ι R) :
    Matrix (powersetCard κ k) (powersetCard ι k) R :=
  LinearMap.toMatrix
    ((Pi.basisFun R ι).exteriorPower k)
    ((Pi.basisFun R κ).exteriorPower k)
    (exteriorPower.map k (Matrix.toLin' A))

omit [DecidableEq κ] in
/-- A compound-matrix entry is the corresponding minor. -/
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
/-- Functoriality of exterior powers, in compound coordinates. -/
theorem compound_mul (k : ℕ) (A : Matrix κ ι R) (B : Matrix ι μ R) :
    compound k (A * B) = compound k A * compound k B := by
  simp only [compound, Matrix.toLin'_mul, exteriorPower.map_comp]
  exact LinearMap.toMatrix_comp
    ((Pi.basisFun R μ).exteriorPower k)
    ((Pi.basisFun R ι).exteriorPower k)
    ((Pi.basisFun R κ).exteriorPower k)
    (exteriorPower.map k (Matrix.toLin' A))
    (exteriorPower.map k (Matrix.toLin' B))

end Compound

section SignedTrace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

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
/-- Reindexing an increasing principal minor by its underlying subtype. -/
theorem minor_self_eq_principal (k : ℕ) (M : Matrix ι ι ℂ)
    (s : powersetCard ι k) :
    minor k M s s =
      (M.submatrix (Subtype.val : s.val → ι)
        (Subtype.val : s.val → ι)).det := by
  unfold minor
  rw [← Matrix.det_submatrix_equiv_self (orderIsoOfFin s).toEquiv
    (M.submatrix (Subtype.val : s.val → ι) (Subtype.val : s.val → ι))]
  congr 1

/-- The alternating sum of traces of all exterior powers.  Bundling the
degree by a finset avoids casts between the different compound dimensions. -/
def signedCompoundTrace (A : Matrix ι ι ℂ) : ℂ :=
  ∑ s : Finset ι, (-1 : ℂ) ^ s.card *
    compound s.card A (ofCard rfl) (ofCard rfl)

/-- The standard full-exterior identity
`det (I - A) = sum_k (-1)^k tr (wedge^k A)`. -/
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

end SignedTrace

end CircularLawSection4
