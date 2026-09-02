import CircularLawSection4.OrderedCoefficientL2Contraction

/-!
# Row-linearity in the ordered exterior coefficient family

This module packages the exact row-linearity identity in the same notation
as the ordered reset/star coefficient matrices.  In particular, the reset
minus sign is absorbed into `orderedCoefficient`, so the affine expansion is
a sum over the actual one-step operators used by the reset word.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

/-- The denominator-cleared companion compound is exactly the affine
combination of the ordered star/reset coefficient matrices. -/
theorem clearedRowCompanionCompound_eq_orderedCoefficient
    (d : ℕ) (q : ExteriorDegree (d + 1)) (β : ℂ)
    (c : Fin (d + 1) → ℂ) (hβ : β ≠ 0) :
    clearedRowCompanionCompound q.val (finLeftShift d) (Fin.last d) β c =
      β • orderedCoefficient d q none +
        ∑ j, c j • orderedCoefficient d q (some j) := by
  rw [clearedRowCompanionCompound_eq_affine q.val
    (finLeftShift d) (Fin.last d) β c hβ]
  simp only [orderedCoefficient, smul_neg]
  simp [sub_eq_add_neg]

/-- Manuscript-ready packaging of the ordered row-linearity formula together
with the Euclidean contraction of every coefficient operator. -/
theorem orderedRowLinearity_with_l2_contraction
    (d : ℕ) (q : ExteriorDegree (d + 1)) (β : ℂ)
    (c : Fin (d + 1) → ℂ) (hβ : β ≠ 0) :
    clearedRowCompanionCompound q.val (finLeftShift d) (Fin.last d) β c =
        β • orderedCoefficient d q none +
          ∑ j, c j • orderedCoefficient d q (some j) ∧
      ∀ ell : ResetLabel (d + 1), ‖orderedCoefficient d q ell‖ ≤ 1 := by
  exact ⟨clearedRowCompanionCompound_eq_orderedCoefficient d q β c hβ,
    orderedCoefficient_l2_opNorm_le_one d q⟩

end CircularLawSection4
