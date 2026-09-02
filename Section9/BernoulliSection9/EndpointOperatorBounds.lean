import BernoulliSection9.TerminalSpectralBridge
import BernoulliSection9.TerminalConcreteBounds
import BernoulliLinearAlgebra.ConcreteBoundaryFinal
import Mathlib.Tactic

/-!
# Quantitative endpoint bounds from the interface event

The interface theorem controls the two endpoint blocks in Euclidean
operator norm.  This file turns that control into a single explicit Gram
volume bound.  No exterior-conditioning or compound-matrix certificate is
an input.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

open BernoulliLinearAlgebra

local instance endpointOperatorSumLinearOrder (W : Nat) :
    LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift'
    (fun x : Fin W ⊕ Fin W => (toLex x : Fin W ⊕ₗ Fin W))
    toLex.injective

/-- A deliberately generous operator-norm bound for
`diag(C_L,B_R)`. -/
def endpointOperatorCrudeBound (W : Nat) (B : Real) : Real :=
  ((2 * W : Nat) : Real) ^ 2 * B

/-- The corresponding uniform bound for every exterior degree, obtained
below through Gram volume. -/
def endpointCompoundCrudeBound (W : Nat) (B : Real) : Real :=
  (2 * max 1 (endpointOperatorCrudeBound W B)) ^ (2 * W)

/-- The operator-norm part of the paper's endpoint good event.  This
definition fixes the Euclidean operator norm at its declaration site, so it
can be used from modules whose compound matrices carry the Frobenius norm. -/
def EndpointOperatorGood {W : Nat}
    (CL BR : Matrix (Fin W) (Fin W) Complex) (B : Real) : Prop :=
  ‖CL‖ <= B ∧ ‖BR‖ <= B

/-- Operator-norm control of both diagonal endpoint blocks implies an
explicit operator-norm bound for their block diagonal sum. -/
theorem norm_endpointFactor_le_endpointOperatorCrudeBound
    {W : Nat} (CL BR : Matrix (Fin W) (Fin W) Complex)
    (B : Real) (hCL : ‖CL‖ <= B) (hBR : ‖BR‖ <= B) :
    ‖endpointFactor CL BR‖ <= endpointOperatorCrudeBound W B := by
  have hB : 0 <= B := (norm_nonneg CL).trans hCL
  have hentry : ∀ i j : Fin W ⊕ Fin W,
      ‖endpointFactor CL BR i j‖ <= B := by
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · simpa [endpointFactor] using
        (norm_matrix_entry_le_l2_opNorm CL i j).trans hCL
    · simp [endpointFactor, hB]
    · simp [endpointFactor, hB]
    · simpa [endpointFactor] using
        (norm_matrix_entry_le_l2_opNorm BR i j).trans hBR
  calc
    ‖endpointFactor CL BR‖ <=
        ∑ i, ∑ j, ‖endpointFactor CL BR i j‖ :=
      matrix_l2_opNorm_le_sum_entry_norm _
    _ <= ∑ _i : Fin W ⊕ Fin W, ∑ _j : Fin W ⊕ Fin W, B := by
      gcongr with i _ j
      exact hentry i j
    _ = endpointOperatorCrudeBound W B := by
      simp [endpointOperatorCrudeBound, pow_two]
      ring

/-- The interface operator-norm event bounds the endpoint Gram volume by a
fixed explicit scalar.  The next module uses the all-minor energy identity
to dominate every Frobenius compound by this same scalar. -/
theorem gramVolume_endpointFactor_le_endpointCompoundCrudeBound
    {W : Nat} (CL BR : Matrix (Fin W) (Fin W) Complex)
    (B : Real) (hCL : ‖CL‖ <= B) (hBR : ‖BR‖ <= B) :
    gramVolume (endpointFactor CL BR) <=
      endpointCompoundCrudeBound W B := by
  have hnorm := norm_endpointFactor_le_endpointOperatorCrudeBound
    CL BR B hCL hBR
  have hmax : max 1 ‖endpointFactor CL BR‖ <=
      max 1 (endpointOperatorCrudeBound W B) := by
    exact max_le (le_max_left _ _)
      (hnorm.trans (le_max_right _ _))
  have hbase : 0 <= 2 * max 1 ‖endpointFactor CL BR‖ := by positivity
  calc
    gramVolume (endpointFactor CL BR) <=
        (2 * max 1 ‖endpointFactor CL BR‖) ^
          Fintype.card (Fin W ⊕ Fin W) :=
      gramVolume_le_two_mul_max_one_norm_pow _
    _ <= (2 * max 1 (endpointOperatorCrudeBound W B)) ^
          Fintype.card (Fin W ⊕ Fin W) := by
      exact pow_le_pow_left₀ hbase
        (mul_le_mul_of_nonneg_left hmax (by norm_num)) _
    _ = endpointCompoundCrudeBound W B := by
      unfold endpointCompoundCrudeBound
      congr 1
      simp [two_mul]

/-- Bundled-paper-event form of the preceding Gram-volume estimate. -/
theorem gramVolume_endpointFactor_le_of_endpointOperatorGood
    {W : Nat} (CL BR : Matrix (Fin W) (Fin W) Complex)
    (B : Real) (hgood : EndpointOperatorGood CL BR B) :
    gramVolume (endpointFactor CL BR) <=
      endpointCompoundCrudeBound W B :=
  gramVolume_endpointFactor_le_endpointCompoundCrudeBound
    CL BR B hgood.1 hgood.2

end BernoulliSection9
