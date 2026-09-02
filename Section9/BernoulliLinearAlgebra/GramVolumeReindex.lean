import BernoulliLinearAlgebra.VolumeComparison

/-!
# Reindexing invariance of Gram volume

The concrete three-block terminal uses Boolean-tagged outer coordinates,
while the boundary relation uses a sum type.  This file proves that a
simultaneous row/column equivalence changes neither Gram energy nor Gram
volume.
-/

open scoped Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [LinearOrder ι]
variable [Fintype κ] [DecidableEq κ] [LinearOrder κ]

omit [LinearOrder ι] [LinearOrder κ] in
/-- Simultaneous reindexing carries the Gram matrix to the simultaneous
reindexing of the original Gram matrix. -/
theorem one_add_gram_submatrix_equiv
    (e : κ ≃ ι) (A : Matrix ι ι ℂ) :
    1 + (A.submatrix e e)ᴴ * A.submatrix e e =
      (1 + Aᴴ * A).submatrix e e := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.mul_apply, ← e.sum_comp]
  · have he : e i ≠ e j := fun hij => h (e.injective hij)
    simp [Matrix.mul_apply, ← e.sum_comp, h, he]

omit [LinearOrder ι] [LinearOrder κ] in
/-- Gram energy is invariant under a simultaneous basis reindexing. -/
theorem gramEnergy_submatrix_equiv
    (e : κ ≃ ι) (A : Matrix ι ι ℂ) :
    gramEnergy (A.submatrix e e) = gramEnergy A := by
  unfold gramEnergy
  rw [one_add_gram_submatrix_equiv,
    Matrix.det_submatrix_equiv_self]

omit [LinearOrder ι] [LinearOrder κ] in
/-- Gram volume is invariant under a simultaneous basis reindexing. -/
theorem gramVolume_submatrix_equiv
    (e : κ ≃ ι) (A : Matrix ι ι ℂ) :
    gramVolume (A.submatrix e e) = gramVolume A := by
  unfold gramVolume
  rw [gramEnergy_submatrix_equiv]

end BernoulliLinearAlgebra
