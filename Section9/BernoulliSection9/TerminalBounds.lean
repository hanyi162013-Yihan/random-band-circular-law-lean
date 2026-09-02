import BernoulliSection9.TerminalCUR
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# Quantitative bounds for the terminal CUR residual

These estimates are the term-by-term norm check following equation (9.21).
They are consequences of the literal `F` formula and submultiplicativity;
no probability or RRQR certificate enters this module.
-/

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

variable {p q : Type*}
variable [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

theorem G21_norm_le (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    ‖G21 S Delta‖ ≤
      ‖delta21 Delta‖ + ‖S.Yskel‖ * ‖delta11 Delta‖ := by
  calc
    ‖G21 S Delta‖ =
        ‖delta21 Delta - S.Yskel * delta11 Delta‖ := rfl
    _ ≤ ‖delta21 Delta‖ + ‖S.Yskel * delta11 Delta‖ := norm_sub_le _ _
    _ ≤ ‖delta21 Delta‖ + ‖S.Yskel‖ * ‖delta11 Delta‖ :=
      by simpa [add_comm] using
        add_le_add_left (Matrix.l2_opNorm_mul S.Yskel (delta11 Delta))
          ‖delta21 Delta‖

theorem G12_norm_le (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    ‖G12 S Delta‖ ≤
      ‖delta12 Delta‖ + ‖delta11 Delta‖ * ‖S.Xskel‖ := by
  calc
    ‖G12 S Delta‖ =
        ‖delta12 Delta - delta11 Delta * S.Xskel‖ := rfl
    _ ≤ ‖delta12 Delta‖ + ‖delta11 Delta * S.Xskel‖ := norm_sub_le _ _
    _ ≤ ‖delta12 Delta‖ + ‖delta11 Delta‖ * ‖S.Xskel‖ :=
      by simpa [add_comm] using
        add_le_add_left (Matrix.l2_opNorm_mul (delta11 Delta) S.Xskel)
          ‖delta12 Delta‖

/-- The five summands in (9.20), before replacing each product by the product
of its norms. -/
theorem F_norm_le_sum_of_term_norms (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    ‖F S Delta‖ ≤
      ‖S.E0‖ + ‖S.Yskel * delta12 Delta‖ +
        ‖delta21 Delta * S.Xskel‖ +
        ‖S.Yskel * delta11 Delta * S.Xskel‖ +
        ‖G21 S Delta * (KDelta S Delta)⁻¹ * G12 S Delta‖ := by
  have h1 :
      ‖S.E0 - S.Yskel * delta12 Delta‖ ≤
        ‖S.E0‖ + ‖S.Yskel * delta12 Delta‖ := norm_sub_le _ _
  have h2 :
      ‖S.E0 - S.Yskel * delta12 Delta - delta21 Delta * S.Xskel‖ ≤
        ‖S.E0 - S.Yskel * delta12 Delta‖ +
          ‖delta21 Delta * S.Xskel‖ := norm_sub_le _ _
  have h3 :
      ‖S.E0 - S.Yskel * delta12 Delta - delta21 Delta * S.Xskel +
          S.Yskel * delta11 Delta * S.Xskel‖ ≤
        ‖S.E0 - S.Yskel * delta12 Delta - delta21 Delta * S.Xskel‖ +
          ‖S.Yskel * delta11 Delta * S.Xskel‖ := norm_add_le _ _
  have h4 := norm_sub_le
    (S.E0 - S.Yskel * delta12 Delta - delta21 Delta * S.Xskel +
      S.Yskel * delta11 Delta * S.Xskel)
    (G21 S Delta * (KDelta S Delta)⁻¹ * G12 S Delta)
  rw [F]
  linarith

/-- Fully scalar form of the norm check.  Substituting polynomial bounds for
the displayed norms immediately produces a fixed polynomial bound for `F`. -/
theorem F_norm_le (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ) :
    ‖F S Delta‖ ≤
      ‖S.E0‖ + ‖S.Yskel‖ * ‖delta12 Delta‖ +
        ‖delta21 Delta‖ * ‖S.Xskel‖ +
        ‖S.Yskel‖ * ‖delta11 Delta‖ * ‖S.Xskel‖ +
        ‖G21 S Delta‖ * ‖(KDelta S Delta)⁻¹‖ * ‖G12 S Delta‖ := by
  have hY12 : ‖S.Yskel * delta12 Delta‖ ≤
      ‖S.Yskel‖ * ‖delta12 Delta‖ :=
    Matrix.l2_opNorm_mul _ _
  have h21X : ‖delta21 Delta * S.Xskel‖ ≤
      ‖delta21 Delta‖ * ‖S.Xskel‖ :=
    Matrix.l2_opNorm_mul _ _
  have hY11 : ‖S.Yskel * delta11 Delta‖ ≤
      ‖S.Yskel‖ * ‖delta11 Delta‖ :=
    Matrix.l2_opNorm_mul _ _
  have hY11X0 : ‖S.Yskel * delta11 Delta * S.Xskel‖ ≤
      ‖S.Yskel * delta11 Delta‖ * ‖S.Xskel‖ :=
    Matrix.l2_opNorm_mul _ _
  have hY11X : ‖S.Yskel * delta11 Delta * S.Xskel‖ ≤
      ‖S.Yskel‖ * ‖delta11 Delta‖ * ‖S.Xskel‖ :=
    hY11X0.trans (mul_le_mul_of_nonneg_right hY11 (norm_nonneg _))
  have hGK : ‖G21 S Delta * (KDelta S Delta)⁻¹‖ ≤
      ‖G21 S Delta‖ * ‖(KDelta S Delta)⁻¹‖ :=
    Matrix.l2_opNorm_mul _ _
  have hGKG0 : ‖G21 S Delta * (KDelta S Delta)⁻¹ * G12 S Delta‖ ≤
      ‖G21 S Delta * (KDelta S Delta)⁻¹‖ * ‖G12 S Delta‖ :=
    Matrix.l2_opNorm_mul _ _
  have hGKG : ‖G21 S Delta * (KDelta S Delta)⁻¹ * G12 S Delta‖ ≤
      ‖G21 S Delta‖ * ‖(KDelta S Delta)⁻¹‖ * ‖G12 S Delta‖ :=
    hGKG0.trans (mul_le_mul_of_nonneg_right hGK (norm_nonneg _))
  exact (F_norm_le_sum_of_term_norms S Delta).trans (by linarith)

/-- Combine the exact determinant factorization with independent lower
bounds for its pivot and residual factors. -/
theorem det_skeleton_add_lower
    (S : BlockSkeletonData p q)
    (Delta : Matrix (p ⊕ q) (p ⊕ q) ℂ)
    (hK : IsUnit (KDelta S Delta).det)
    {pivotLower residualLower : ℝ}
    (hresidual_nonneg : 0 ≤ residualLower)
    (hpivot : pivotLower ≤ ‖(KDelta S Delta).det‖)
    (hresidual : residualLower ≤ ‖(delta22 Delta + F S Delta).det‖) :
    pivotLower * residualLower ≤ ‖(skeletonMatrix S + Delta).det‖ := by
  rw [det_skeleton_add_eq_det_KDelta_mul_det_residual S Delta hK, norm_mul]
  exact mul_le_mul hpivot hresidual hresidual_nonneg (norm_nonneg _)

end BernoulliSection9
