import BernoulliLinearAlgebra.DoubleEliminationConcrete
import BernoulliLinearAlgebra.VolumeComparison
import BernoulliLinearAlgebra.JacobiConcrete
import Mathlib.Tactic

/-!
# A certificate-free conditioning constant

For a concrete invertible finite matrix, all exterior degrees form a finite
family.  Their norms and the norms of the inverse compounds therefore have
the explicit common constant defined below.  This removes
`ExteriorConditioning` as an application-level certificate even before using
the sharper Hodge--Jacobi estimate from the paper.
-/

open scoped BigOperators Matrix Matrix.Norms.Frobenius

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard

section ExactConstant

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- A completely explicit finite common bound for every exterior degree of
`E` and `E⁻¹`.  Degrees above the dimension have zero-dimensional compound
matrices. -/
def exactExteriorConditioningConstant (E : Matrix ι ι ℂ) : ℝ :=
  1 + ∑ k ∈ Finset.range (Fintype.card ι + 1),
    (‖compound k E‖ + ‖compound k E⁻¹‖)

theorem one_le_exactExteriorConditioningConstant (E : Matrix ι ι ℂ) :
    1 ≤ exactExteriorConditioningConstant E := by
  unfold exactExteriorConditioningConstant
  exact le_add_of_nonneg_right <|
    Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem compound_norm_le_exactExteriorConditioningConstant
    (E : Matrix ι ι ℂ) (k : ℕ) :
    ‖compound k E‖ ≤ exactExteriorConditioningConstant E := by
  by_cases hk : k ≤ Fintype.card ι
  · have hmem : k ∈ Finset.range (Fintype.card ι + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    calc
      ‖compound k E‖ ≤ ‖compound k E‖ + ‖compound k E⁻¹‖ :=
        le_add_of_nonneg_right (norm_nonneg _)
      _ ≤ ∑ q ∈ Finset.range (Fintype.card ι + 1),
          (‖compound q E‖ + ‖compound q E⁻¹‖) := by
        exact Finset.single_le_sum
          (f := fun q => ‖compound q E‖ + ‖compound q E⁻¹‖)
          (fun q _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hmem
      _ ≤ exactExteriorConditioningConstant E := by
        unfold exactExteriorConditioningConstant
        exact le_add_of_nonneg_left zero_le_one
  · have hcard : Fintype.card ι < k := Nat.lt_of_not_ge hk
    have hzero : compound k E = 0 := by
      ext s
      exact ((not_le_of_gt hcard) (by
        rw [← s.prop]
        exact Finset.card_le_univ s.val)).elim
    rw [hzero, norm_zero]
    exact le_trans zero_le_one (one_le_exactExteriorConditioningConstant E)

theorem compound_inv_norm_le_exactExteriorConditioningConstant
    (E : Matrix ι ι ℂ) (k : ℕ) :
    ‖compound k E⁻¹‖ ≤ exactExteriorConditioningConstant E := by
  by_cases hk : k ≤ Fintype.card ι
  · have hmem : k ∈ Finset.range (Fintype.card ι + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    calc
      ‖compound k E⁻¹‖ ≤ ‖compound k E‖ + ‖compound k E⁻¹‖ :=
        le_add_of_nonneg_left (norm_nonneg _)
      _ ≤ ∑ q ∈ Finset.range (Fintype.card ι + 1),
          (‖compound q E‖ + ‖compound q E⁻¹‖) := by
        exact Finset.single_le_sum
          (f := fun q => ‖compound q E‖ + ‖compound q E⁻¹‖)
          (fun q _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hmem
      _ ≤ exactExteriorConditioningConstant E := by
        unfold exactExteriorConditioningConstant
        exact le_add_of_nonneg_left zero_le_one
  · have hcard : Fintype.card ι < k := Nat.lt_of_not_ge hk
    have hzero : compound k E⁻¹ = 0 := by
      ext s
      exact ((not_le_of_gt hcard) (by
        rw [← s.prop]
        exact Finset.card_le_univ s.val)).elim
    rw [hzero, norm_zero]
    exact le_trans zero_le_one (one_le_exactExteriorConditioningConstant E)

/-- Every concrete nonsingular matrix has `ExteriorConditioning` with the
explicit finite constant above; no Jacobi certificate is an input. -/
theorem exactExteriorConditioning (E : Matrix ι ι ℂ)
    (hE : IsUnit E.det) :
    ExteriorConditioning E (exactExteriorConditioningConstant E) where
  det_isUnit := hE
  one_le := one_le_exactExteriorConditioningConstant E
  forward := compound_norm_le_exactExteriorConditioningConstant E
  inverse := compound_inv_norm_le_exactExteriorConditioningConstant E

end ExactConstant

section EndpointFactor

variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

local instance endpointConditioningSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W => (toLex x : W ⊕ₗ W)) toLex.injective

omit [LinearOrder W] in
@[simp]
theorem endpointFactor_det (CL BR : Matrix W W ℂ) :
    (endpointFactor CL BR).det = CL.det * BR.det := by
  simp [endpointFactor]

/-- Concrete conditioning for `E = diag(C_L,B_R)` on the endpoint
invertibility event. -/
theorem endpointFactor_exactConditioning
    (CL BR : Matrix W W ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det) :
    ExteriorConditioning (endpointFactor CL BR)
      (exactExteriorConditioningConstant (endpointFactor CL BR)) := by
  apply exactExteriorConditioning
  rw [endpointFactor_det]
  exact hCL.mul hBR

/-- Quantitative version of the endpoint conditioning used in the paper.
The determinant and forward-compound estimates are the probabilistic event
bounds; the inverse-compound estimates are now derived internally from the
general Jacobi theorem rather than supplied as certificates. -/
theorem endpointFactor_conditioning_of_hodgeBounds
    (CL BR : Matrix W W ℂ) {D L : ℝ}
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (hD : 0 ≤ D)
    (hdet : ‖(endpointFactor CL BR).det‖⁻¹ ≤ D)
    (hforward : ∀ q : ℕ, ‖compound q (endpointFactor CL BR)‖ ≤ L) :
    ExteriorConditioning (endpointFactor CL BR)
      (max 1 (max L (D * L))) := by
  apply exteriorConditioning_of_hodgeBounds_isUnit
  · rw [endpointFactor_det]
    exact hCL.mul hBR
  · exact hD
  · exact hdet
  · exact hforward

end EndpointFactor

end BernoulliLinearAlgebra
