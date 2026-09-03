/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/Section5Formalization/BlockEnergy.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Section5Formalization.VolumetricNet

open scoped BigOperators

namespace Section5Formalization

/-! # Large-block energy selection -/

/-- Some block carries at least the average squared norm. -/
theorem exists_block_sq_norm_ge_average
    {E : Type*} [SeminormedAddCommGroup E] {L : Nat} (hL : 0 < L)
    (v : Fin L -> E) (henergy : (∑ q, ‖v q‖ ^ 2) = 1) :
    ∃ j : Fin L, 1 / (L : Real) <= ‖v j‖ ^ 2 := by
  letI : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp hL
  obtain ⟨j, hj⟩ := Finite.exists_max (fun q : Fin L => ‖v q‖ ^ 2)
  refine ⟨j, (div_le_iff₀ (Nat.cast_pos.mpr hL)).2 ?_⟩
  have hsum : (∑ q, ‖v q‖ ^ 2) <= ∑ _q : Fin L, ‖v j‖ ^ 2 :=
    Finset.sum_le_sum fun q _ => hj q
  rw [henergy] at hsum
  simpa [mul_comm] using hsum

/-- A unit block vector has a block of norm at least `L^(-1/2)`. -/
theorem exists_block_norm_ge_inv_sqrt
    {E : Type*} [SeminormedAddCommGroup E] {L : Nat} (hL : 0 < L)
    (v : Fin L -> E) (henergy : (∑ q, ‖v q‖ ^ 2) = 1) :
    ∃ j : Fin L, 1 / Real.sqrt (L : Real) <= ‖v j‖ := by
  obtain ⟨j, hj⟩ := exists_block_sq_norm_ge_average hL v henergy
  refine ⟨j, ?_⟩
  have hsqrt : 0 < Real.sqrt (L : Real) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hL)
  apply (sq_le_sq₀ (by positivity) (norm_nonneg (v j))).mp
  have hsquare : (1 / Real.sqrt (L : Real)) ^ 2 = 1 / (L : Real) := by
    field_simp [hsqrt.ne']
    rw [Real.sq_sqrt (Nat.cast_nonneg L)]
  rw [hsquare]
  exact hj

section OrthogonalDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Coefficient of `b` along a nonzero real vector `a`. -/
noncomputable def realOrthogonalCoefficient (a b : E) : Real :=
  inner Real a b / ‖a‖ ^ 2

/-- Remainder after removing the component of `b` parallel to `a`. -/
noncomputable def realOrthogonalRemainder (a b : E) : E :=
  b - realOrthogonalCoefficient a b • a

/-- Exact decomposition used in the nearly-real block-net argument. -/
theorem real_orthogonal_decomposition (a b : E) :
    b = realOrthogonalCoefficient a b • a + realOrthogonalRemainder a b := by
  simp [realOrthogonalRemainder]

/-- The remainder in the decomposition is orthogonal to the leading component. -/
theorem inner_realOrthogonalRemainder_eq_zero {a b : E} (ha : a ≠ 0) :
    inner Real a (realOrthogonalRemainder a b) = 0 := by
  rw [realOrthogonalRemainder, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  unfold realOrthogonalCoefficient
  field_simp [norm_ne_zero_iff.mpr ha] <;> ring

/-- If `a` is the larger real/imaginary component, its coefficient has absolute value at most one. -/
theorem abs_realOrthogonalCoefficient_le_one {a b : E} (hba : ‖b‖ <= ‖a‖) :
    |realOrthogonalCoefficient a b| <= 1 := by
  by_cases ha : a = 0
  · have hbNorm : ‖b‖ = 0 := by
      apply le_antisymm
      · simpa [ha] using hba
      · exact norm_nonneg b
    have hb : b = 0 := norm_eq_zero.mp hbNorm
    simp [realOrthogonalCoefficient, ha, hb]
  · have hinner : |inner Real a b| <= ‖a‖ ^ 2 := by
      calc
        |inner Real a b| <= ‖a‖ * ‖b‖ := abs_real_inner_le_norm a b
        _ <= ‖a‖ * ‖a‖ := mul_le_mul_of_nonneg_left hba (norm_nonneg a)
        _ = ‖a‖ ^ 2 := by ring
    rw [realOrthogonalCoefficient, abs_div, abs_of_nonneg (sq_nonneg ‖a‖)]
    exact div_le_one_of_le₀ hinner (sq_nonneg ‖a‖)

end OrthogonalDecomposition

end Section5Formalization

