import CircularLawSection4.PaperIndicatorFreshRows
import CircularLawSection4.OperatorAffineLog

/-!
# Frozen one-row interface for the paper pressure argument

After all rows except one are frozen, the left and right transfer histories
turn every ordered exterior row coefficient into a deterministic sandwich
`L * K_ell * R`.  This module identifies the resulting full row exactly with
the operator-affine expression used by the logarithmic small-ball argument.
The same frozen coefficient family and the same scale work for an original
row and an independently replaced row.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace PaperIndicatorWeights

variable {d : ℕ} {c₀ C₀ : ℝ}

/-- The deterministic coefficient matrix obtained by sandwiching one ordered
row coefficient between the frozen left and right histories. -/
def paperPressureFrozenCoefficient
    (q : ExteriorDegree (d + 1))
    (L R : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (ell : ResetLabel (d + 1)) :
    Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ :=
  L * orderedCoefficient d q ell * R

/-- The same frozen coefficient, regarded as a continuous operator on the
finite-dimensional Euclidean exterior space. -/
def paperPressureFrozenCoefficientCLM
    (q : ExteriorDegree (d + 1))
    (L R : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (ell : ResetLabel (d + 1)) :
    EuclideanSpace ℂ (ExteriorIndex (d + 1) q) →L[ℂ]
      EuclideanSpace ℂ (ExteriorIndex (d + 1) q) :=
  Matrix.toEuclideanCLM (n := ExteriorIndex (d + 1) q) (𝕜 := ℂ)
    (paperPressureFrozenCoefficient q L R ell)

/-- Matrix-level operator-affine row after the outside histories are frozen.
The distinguished `-z` coefficient is the reset label representing the
diagonal band slot. -/
def paperPressureRowAffineMatrix
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (rowAtoms : ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (L R : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ) :
    Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ :=
  (∑ ell : ResetLabel (d + 1),
      (profile.orderedResetWeight ell * rowAtoms ell) •
        paperPressureFrozenCoefficient q L R ell) -
    z • paperPressureFrozenCoefficient q L R (some center)

/-- Exact leave-one-row identity at matrix level. -/
theorem mul_freshExteriorRow_mul_eq_paperPressureRowAffineMatrix
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1)) (t : Fin (d + 1))
    (L R : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ) :
    L * profile.freshExteriorRow center z atoms q t * R =
      profile.paperPressureRowAffineMatrix center z (atoms t) q L R := by
  classical
  simp [freshExteriorRow, paperPressureRowAffineMatrix,
    paperPressureFrozenCoefficient, freshSpectralShift,
    Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul,
    sub_eq_add_neg]

/-- The matrix identity transported to continuous operators is literally the
generic `operatorAffine` expression used by `OperatorAffineLog`. -/
theorem toEuclideanCLM_mul_freshExteriorRow_mul_eq_operatorAffine
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1)) (t : Fin (d + 1))
    (L R : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ) :
    Matrix.toEuclideanCLM (n := ExteriorIndex (d + 1) q) (𝕜 := ℂ)
        (L * profile.freshExteriorRow center z atoms q t * R) =
      operatorAffine profile.orderedResetWeight (atoms t)
        (paperPressureFrozenCoefficientCLM q L R) z
        (paperPressureFrozenCoefficientCLM q L R (some center)) := by
  rw [profile.mul_freshExteriorRow_mul_eq_paperPressureRowAffineMatrix]
  simp [paperPressureRowAffineMatrix, paperPressureFrozenCoefficientCLM,
    operatorAffine]

/-- Both an original row and a replacement row use the same frozen
coefficient family.  Only their atom vectors differ. -/
theorem old_new_freshExteriorRow_eq_same_operatorAffine
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (oldAtoms newAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1)) (t : Fin (d + 1))
    (L R : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ) :
    Matrix.toEuclideanCLM (n := ExteriorIndex (d + 1) q) (𝕜 := ℂ)
        (L * profile.freshExteriorRow center z oldAtoms q t * R) =
        operatorAffine profile.orderedResetWeight (oldAtoms t)
          (paperPressureFrozenCoefficientCLM q L R) z
          (paperPressureFrozenCoefficientCLM q L R (some center)) ∧
      Matrix.toEuclideanCLM (n := ExteriorIndex (d + 1) q) (𝕜 := ℂ)
        (L * profile.freshExteriorRow center z newAtoms q t * R) =
        operatorAffine profile.orderedResetWeight (newAtoms t)
          (paperPressureFrozenCoefficientCLM q L R) z
          (paperPressureFrozenCoefficientCLM q L R (some center)) := by
  exact ⟨profile.toEuclideanCLM_mul_freshExteriorRow_mul_eq_operatorAffine
      center z oldAtoms q t L R,
    profile.toEuclideanCLM_mul_freshExteriorRow_mul_eq_operatorAffine
      center z newAtoms q t L R⟩

/-- The common logarithmic reference scale for the original and replacement
rows.  It depends only on the deterministic profile and the frozen histories,
not on either atom vector or on `z`. -/
def paperPressureRowScale
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1))
    (q : ExteriorDegree (d + 1))
    (L R : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ) : ℝ :=
  operatorAffineScale (some center) profile.orderedResetWeight
    (paperPressureFrozenCoefficientCLM q L R)

/-- The common scale is positive whenever its distinguished diagonal frozen
coefficient is nonzero. -/
theorem paperPressureRowScale_pos_of_center_ne_zero
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1))
    (q : ExteriorDegree (d + 1))
    (L R : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (hcenter : paperPressureFrozenCoefficient q L R (some center) ≠ 0) :
    0 < profile.paperPressureRowScale center q L R := by
  have hclm : paperPressureFrozenCoefficientCLM q L R (some center) ≠ 0 := by
    intro hzero
    apply hcenter
    apply (Matrix.toEuclideanCLM
      (n := ExteriorIndex (d + 1) q) (𝕜 := ℂ)).injective
    simpa [paperPressureFrozenCoefficientCLM] using hzero
  exact (norm_pos_iff.mpr hclm).trans_le
    (distinguished_operator_norm_le_scale (some center)
      profile.orderedResetWeight (paperPressureFrozenCoefficientCLM q L R))

/-- Positive profile weights make the common scale positive as soon as one
frozen coefficient in the family is nonzero. -/
theorem paperPressureRowScale_pos_of_exists_ne_zero
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1))
    (q : ExteriorDegree (d + 1))
    (L R : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (hne : ∃ ell : ResetLabel (d + 1),
      paperPressureFrozenCoefficient q L R ell ≠ 0) :
    0 < profile.paperPressureRowScale center q L R := by
  obtain ⟨ell, hell⟩ := hne
  have hweight : profile.orderedResetWeight ell ≠ 0 := by
    cases ell with
    | none => exact profile.b_ne_zero hc₀ (Fin.last (d + 1))
    | some j => exact profile.b_ne_zero hc₀ j.castSucc
  have hclm : paperPressureFrozenCoefficientCLM q L R ell ≠ 0 := by
    intro hzero
    apply hell
    apply (Matrix.toEuclideanCLM
      (n := ExteriorIndex (d + 1) q) (𝕜 := ℂ)).injective
    simpa [paperPressureFrozenCoefficientCLM] using hzero
  have hpositive :
      0 < ‖profile.orderedResetWeight ell‖ *
        ‖paperPressureFrozenCoefficientCLM q L R ell‖ :=
    mul_pos (norm_pos_iff.mpr hweight) (norm_pos_iff.mpr hclm)
  exact hpositive.trans_le
    (weighted_operator_norm_le_scale (some center)
      profile.orderedResetWeight (paperPressureFrozenCoefficientCLM q L R) ell)

end PaperIndicatorWeights

end CircularLawSection4
