import CircularLawSection4.IsolatedMaxEntry
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Euclidean operator norm versus a largest matrix coordinate

This module supplies the finite-dimensional comparison left open in
`IsolatedMaxEntry.lean`.  The constants are deliberately elementary: for a
square matrix indexed by `m`, its Euclidean operator norm is bounded by
`card m ^ 2` times any common bound on its entries.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

section EuclideanCoordinates

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The Euclidean norm is at most the sum of the coordinate norms.  This
intentionally loose estimate avoids introducing square-root constants. -/
theorem euclidean_norm_le_sum_coordinate_norm (x : EuclideanSpace ℂ m) :
    ‖x‖ ≤ ∑ i, ‖x i‖ := by
  have hx : x = ∑ i, (PiLp.single 2 i (x i) : EuclideanSpace ℂ m) := by
    ext j
    simp
  calc
    ‖x‖ = ‖∑ i, (PiLp.single 2 i (x i) : EuclideanSpace ℂ m)‖ :=
      congrArg norm hx
    _ ≤ ∑ i, ‖(PiLp.single 2 i (x i) : EuclideanSpace ℂ m)‖ :=
      norm_sum_le _ _
    _ = ∑ i, ‖x i‖ := by simp

end EuclideanCoordinates

section MatrixBound

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A common entry bound controls the complex Euclidean operator norm.  The
constant `card m ^ 2` is loose but completely explicit. -/
theorem l2_opNorm_le_card_sq_mul_of_entrywise_le
    (A : Matrix m m ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hentry : ∀ i j, ‖A i j‖ ≤ M) :
    ‖A‖ ≤ (Fintype.card m : ℝ) ^ 2 * M := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A).opNorm_le_bound
    (mul_nonneg (sq_nonneg _) hM) ?_
  intro x
  change ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)‖ ≤
    (Fintype.card m : ℝ) ^ 2 * M * ‖x‖
  calc
    ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)‖
        ≤ ∑ i, ‖(A *ᵥ WithLp.ofLp x) i‖ :=
      euclidean_norm_le_sum_coordinate_norm _
    _ ≤ ∑ _i : m, ∑ _j : m, M * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖(A *ᵥ WithLp.ofLp x) i‖
            ≤ ∑ j, ‖A i j * WithLp.ofLp x j‖ := norm_sum_le _ _
        _ ≤ ∑ _j : m, M * ‖x‖ := by
          apply Finset.sum_le_sum
          intro j _
          rw [norm_mul]
          exact mul_le_mul (hentry i j) (PiLp.norm_apply_le x j)
            (norm_nonneg _) hM
    _ = (Fintype.card m : ℝ) ^ 2 * M * ‖x‖ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end MatrixBound

section ExteriorFamily

/-- Maximum Euclidean operator norm over all exterior degrees. -/
noncomputable def exteriorFamilyMaxL2OpNorm {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun q : ExteriorDegree d => ‖B q‖

/-- Every exterior-family entry is bounded by the global maximum entry used
in `IsolatedMaxEntry`. -/
theorem norm_entry_le_exteriorFamilyMaxEntryNorm {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (q : ExteriorDegree d) (I J : ExteriorIndex d q) :
    ‖B q J I‖ ≤ exteriorFamilyMaxEntryNorm B := by
  classical
  unfold exteriorFamilyMaxEntryNorm
  exact Finset.le_sup'
    (fun e : ExteriorFamilyEntry d => ‖B e.1 e.2.2 e.2.1‖)
    (Finset.mem_univ ⟨q, I, J⟩)

theorem exteriorFamilyMaxEntryNorm_nonneg {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ) :
    0 ≤ exteriorFamilyMaxEntryNorm B := by
  let I := emptyExteriorIndex d
  exact (norm_nonneg (B 0 I I)).trans
    (norm_entry_le_exteriorFamilyMaxEntryNorm B 0 I I)

/-- The entries in one degree inject into all dependent family entries. -/
theorem exteriorIndex_card_sq_le_familyEntry_card {d : ℕ}
    (q : ExteriorDegree d) :
    Fintype.card (ExteriorIndex d q) ^ 2 ≤
      Fintype.card (ExteriorFamilyEntry d) := by
  let f : (ExteriorIndex d q × ExteriorIndex d q) → ExteriorFamilyEntry d :=
    fun p => ⟨q, p⟩
  have hf : Function.Injective f := by
    intro a b hab
    cases hab
    rfl
  simpa [pow_two, Fintype.card_prod] using
    Fintype.card_le_of_injective f hf

/-- The maximum Euclidean operator norm of the exterior family is controlled
by the maximum coordinate entry.  The constant is the total number of
dependent family entries, hence dominates the square dimension at every
degree. -/
theorem exteriorFamilyMaxL2OpNorm_le_familyEntryCard_mul_maxEntry {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ) :
    exteriorFamilyMaxL2OpNorm B ≤
      (Fintype.card (ExteriorFamilyEntry d) : ℝ) *
        exteriorFamilyMaxEntryNorm B := by
  classical
  unfold exteriorFamilyMaxL2OpNorm
  apply Finset.sup'_le
  intro q _
  have hentry : ∀ I J, ‖B q I J‖ ≤ exteriorFamilyMaxEntryNorm B := by
    intro I J
    exact norm_entry_le_exteriorFamilyMaxEntryNorm B q J I
  calc
    ‖B q‖ ≤ (Fintype.card (ExteriorIndex d q) : ℝ) ^ 2 *
          exteriorFamilyMaxEntryNorm B :=
      l2_opNorm_le_card_sq_mul_of_entrywise_le _ _
        (exteriorFamilyMaxEntryNorm_nonneg B) hentry
    _ ≤ (Fintype.card (ExteriorFamilyEntry d) : ℝ) *
          exteriorFamilyMaxEntryNorm B := by
      apply mul_le_mul_of_nonneg_right _ (exteriorFamilyMaxEntryNorm_nonneg B)
      exact_mod_cast exteriorIndex_card_sq_le_familyEntry_card q

/-- Division form of the family comparison. -/
theorem exteriorFamilyMaxL2OpNorm_div_familyEntryCard_le_maxEntry {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ) :
    exteriorFamilyMaxL2OpNorm B /
        (Fintype.card (ExteriorFamilyEntry d) : ℝ) ≤
      exteriorFamilyMaxEntryNorm B := by
  have hcardNat : 0 < Fintype.card (ExteriorFamilyEntry d) := Fintype.card_pos
  have hcard : 0 < (Fintype.card (ExteriorFamilyEntry d) : ℝ) := by
    exact_mod_cast hcardNat
  apply (div_le_iff₀ hcard).2
  simpa [mul_comm] using
    exteriorFamilyMaxL2OpNorm_le_familyEntryCard_mul_maxEntry B

/-- Some exterior coordinate is at least the maximal Euclidean operator norm
divided by the explicit total-entry cardinality. -/
theorem exists_entry_ge_exteriorFamilyMaxL2OpNorm_div_card {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ) :
    ∃ q : ExteriorDegree d, ∃ I J : ExteriorIndex d q,
      exteriorFamilyMaxL2OpNorm B /
          (Fintype.card (ExteriorFamilyEntry d) : ℝ) ≤ ‖B q J I‖ := by
  obtain ⟨q, I, J, hentry⟩ := exists_entry_eq_exteriorFamilyMaxEntryNorm B
  refine ⟨q, I, J, ?_⟩
  rw [hentry]
  exact exteriorFamilyMaxL2OpNorm_div_familyEntryCard_le_maxEntry B

/-- End-to-end Boolean singleton isolation lower bound stated using the
maximum Euclidean operator norm of the exterior family. -/
theorem exists_isolated_booleanSupport_maxL2OpNorm_lower_bound {d : ℕ}
    (weight : ResetLabel d → ℂ)
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (bmin : ℝ) (hbmin : 0 ≤ bmin)
    (hweight : ∀ ℓ : ResetLabel d, bmin ≤ ‖weight ℓ‖) :
    ∃ r : ExteriorDegree d, ∃ I J : ExteriorIndex d r,
      bmin ^ d *
          (exteriorFamilyMaxL2OpNorm B /
            (Fintype.card (ExteriorFamilyEntry d) : ℝ)) ≤
        ‖weightedFullMonomialCoefficient weight B booleanSupportK
          (arbitrarySupportWord I J)‖ := by
  obtain ⟨r, I, J, hcoefficient⟩ :=
    exists_isolated_booleanSupport_maxEntry_lower_bound
      weight B bmin hbmin hweight
  refine ⟨r, I, J, ?_⟩
  apply le_trans _ hcoefficient
  exact mul_le_mul_of_nonneg_left
    (exteriorFamilyMaxL2OpNorm_div_familyEntryCard_le_maxEntry B)
    (pow_nonneg hbmin d)

end ExteriorFamily

end CircularLawSection4
