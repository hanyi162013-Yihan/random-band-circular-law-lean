import CircularLawSection4.OperatorNormMaxEntry
import CircularLawSection4.OperatorAffineLog

/-!
# Coordinate extraction for projective observability

The projective argument chooses large basis coordinates of two Euclidean
vectors.  The estimates here intentionally use the elementary factor
`card m` rather than the sharp square-root factor; this is sufficient for
the logarithmic-size losses in the manuscript and avoids importing a
separate finite-dimensional Parseval development.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace CircularLawSection4

section Coordinates

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-- Some Euclidean coordinate carries at least a `1 / card` fraction of the
vector norm. -/
theorem exists_coordinate_norm_ge_norm_div_card
    (x : EuclideanSpace ℂ m) :
    ∃ i : m, ‖x‖ / (Fintype.card m : ℝ) ≤ ‖x i‖ := by
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty fun i : m => ‖x i‖
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset m).Nonempty)
    (fun j : m => ‖x j‖)
  have hcoord : ∀ j : m, ‖x j‖ ≤ M := by
    intro j
    exact Finset.le_sup' (fun k : m => ‖x k‖) (Finset.mem_univ j)
  have hnorm : ‖x‖ ≤ (Fintype.card m : ℝ) * M := by
    calc
      ‖x‖ ≤ ∑ j, ‖x j‖ := euclidean_norm_le_sum_coordinate_norm x
      _ ≤ ∑ _j : m, M := Finset.sum_le_sum fun j _ => hcoord j
      _ = (Fintype.card m : ℝ) * M := by simp
  have hcard : 0 < (Fintype.card m : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card m)
  refine ⟨i, ?_⟩
  rw [← hi]
  exact (div_le_iff₀ hcard).2 (by simpa [mul_comm] using hnorm)

/-- Two Euclidean vectors admit a pair of coordinates whose product loses
at most two elementary cardinality factors. -/
theorem exists_coordinate_product_norm_ge
    (x v : EuclideanSpace ℂ m) :
    ∃ i j : m,
      (‖x‖ / (Fintype.card m : ℝ)) *
          (‖v‖ / (Fintype.card m : ℝ)) ≤ ‖x i * v j‖ := by
  obtain ⟨i, hi⟩ := exists_coordinate_norm_ge_norm_div_card x
  obtain ⟨j, hj⟩ := exists_coordinate_norm_ge_norm_div_card v
  refine ⟨i, j, ?_⟩
  rw [norm_mul]
  exact mul_le_mul hi hj (by positivity) (norm_nonneg _)

/-- Unit-vector specialization in the form used to lower-bound an isolated
projective coefficient. -/
theorem exists_unit_coordinate_product_ge_card_sq_inv
    (x v : EuclideanSpace ℂ m) (hx : ‖x‖ = 1) (hv : ‖v‖ = 1) :
    ∃ i j : m,
      1 / (Fintype.card m : ℝ) ^ 2 ≤ ‖x i * v j‖ := by
  obtain ⟨i, j, hij⟩ := exists_coordinate_product_norm_ge x v
  refine ⟨i, j, ?_⟩
  rw [hx, hv] at hij
  have hcard : (Fintype.card m : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card m ≠ 0)
  have heq :
      1 / (Fintype.card m : ℝ) ^ 2 =
        (1 / (Fintype.card m : ℝ)) * (1 / (Fintype.card m : ℝ)) := by
    field_simp [hcard]
  rw [heq]
  exact hij

/-- A matrix and a unit input vector admit a completely coordinate-based
projective coefficient.  Compared with a singular-vector proof this loses a
deliberately loose third cardinality factor, but it only requires choosing
maxima from finite coordinate sets.  This is useful for the conditional
version of projective observability, where such finite choices can be given
a measurable tie-breaking rule. -/
theorem exists_matrixEntry_mul_unitCoordinate_ge_opNorm_div_card_cube
    (B : Matrix m m ℂ) (v : EuclideanSpace ℂ m) (hv : ‖v‖ = 1) :
    ∃ o i j : m,
      ‖B‖ / (Fintype.card m : ℝ) ^ 3 ≤ ‖B o i * v j‖ := by
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun p : m × m => ‖B p.1 p.2‖)
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset (m × m)).Nonempty)
    (fun q : m × m => ‖B q.1 q.2‖)
  have hentry : ∀ o i : m, ‖B o i‖ ≤ M := by
    intro o i
    exact Finset.le_sup' (fun q : m × m => ‖B q.1 q.2‖)
      (Finset.mem_univ (o, i))
  have hM : 0 ≤ M := by
    dsimp [M]
    rw [hp]
    exact norm_nonneg _
  have hB : ‖B‖ ≤ (Fintype.card m : ℝ) ^ 2 * M :=
    l2_opNorm_le_card_sq_mul_of_entrywise_le B M hM hentry
  have hcard : 0 < (Fintype.card m : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card m)
  have hpLower :
      ‖B‖ / (Fintype.card m : ℝ) ^ 2 ≤ ‖B p.1 p.2‖ := by
    rw [← hp]
    apply (div_le_iff₀ (sq_pos_of_pos hcard)).2
    simpa [M, mul_comm] using hB
  obtain ⟨j, hj⟩ := exists_coordinate_norm_ge_norm_div_card v
  have hjLower : 1 / (Fintype.card m : ℝ) ≤ ‖v j‖ := by
    simpa only [hv] using hj
  refine ⟨p.1, p.2, j, ?_⟩
  rw [norm_mul]
  have hproduct :
      (‖B‖ / (Fintype.card m : ℝ) ^ 2) *
          (1 / (Fintype.card m : ℝ)) ≤ ‖B p.1 p.2‖ * ‖v j‖ :=
    mul_le_mul hpLower hjLower (by positivity) (norm_nonneg _)
  convert hproduct using 1
  field_simp [hcard.ne']

/-- If a family of scalar coefficients has total norm at least `M`, then
after pairing with a unit vector one singleton coefficient is at least
`M / card²`. -/
theorem exists_singleton_scalar_coefficient_ge_of_le_sum
    (a : m → ℂ) (v : EuclideanSpace ℂ m) (M : ℝ)
    (_hM : 0 ≤ M) (hsum : M ≤ ∑ i, ‖a i‖) (hv : ‖v‖ = 1) :
    ∃ i j : m,
      M / (Fintype.card m : ℝ) ^ 2 ≤ ‖a i * v j‖ := by
  let Amax : ℝ := Finset.univ.sup' Finset.univ_nonempty fun i : m => ‖a i‖
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset m).Nonempty)
    (fun k : m => ‖a k‖)
  have ha : ∀ k : m, ‖a k‖ ≤ Amax := by
    intro k
    exact Finset.le_sup' (fun l : m => ‖a l‖) (Finset.mem_univ k)
  have hMA : M ≤ (Fintype.card m : ℝ) * Amax := by
    calc
      M ≤ ∑ k, ‖a k‖ := hsum
      _ ≤ ∑ _k : m, Amax := Finset.sum_le_sum fun k _ => ha k
      _ = (Fintype.card m : ℝ) * Amax := by simp
  have hcard : 0 < (Fintype.card m : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card m)
  have hiLower : M / (Fintype.card m : ℝ) ≤ ‖a i‖ := by
    rw [← hi]
    exact (div_le_iff₀ hcard).2 (by simpa [mul_comm] using hMA)
  obtain ⟨j, hj⟩ := exists_coordinate_norm_ge_norm_div_card v
  have hjLower : 1 / (Fintype.card m : ℝ) ≤ ‖v j‖ := by
    simpa only [hv] using hj
  refine ⟨i, j, ?_⟩
  rw [norm_mul]
  have hproduct :
      (M / (Fintype.card m : ℝ)) *
          (1 / (Fintype.card m : ℝ)) ≤ ‖a i‖ * ‖v j‖ :=
    mul_le_mul hiLower hjLower (by positivity) (norm_nonneg _)
  have hcard_ne : (Fintype.card m : ℝ) ≠ 0 := hcard.ne'
  convert hproduct using 1
  field_simp [hcard_ne]

/-- Norming-sum form of the projective coordinate extraction.  In the
manuscript one takes `a i = ⟪u, B e_i⟫` and the hypothesis comes from a
left/right norming pair for `B`. -/
theorem exists_projective_singleton_coefficient_ge_of_norming_sum
    (a : m → ℂ) (x v : EuclideanSpace ℂ m) (M : ℝ)
    (hM : 0 ≤ M) (hx : ‖x‖ ≤ 1) (hv : ‖v‖ = 1)
    (hnorming : M ≤ ‖∑ i, a i * x i‖) :
    ∃ i j : m,
      M / (Fintype.card m : ℝ) ^ 2 ≤ ‖a i * v j‖ := by
  have hsum : M ≤ ∑ i, ‖a i‖ := by
    calc
      M ≤ ‖∑ i, a i * x i‖ := hnorming
      _ ≤ ∑ i, ‖a i * x i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖a i‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        calc
          ‖a i‖ * ‖x i‖ ≤ ‖a i‖ * ‖x‖ := by
            gcongr
            exact PiLp.norm_apply_le x i
          _ ≤ ‖a i‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
          _ = ‖a i‖ := mul_one _
  exact exists_singleton_scalar_coefficient_ge_of_le_sum a v M hM hsum hv

/-- An actual nonzero continuous operator admits a Hahn--Banach norming
test whose singleton coordinate coefficient is quantitatively large.  This
is the deterministic coefficient-selection core of projective
observability, with an elementary `card²` loss. -/
theorem exists_large_projective_singleton_coefficient
    (T : EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m)
    (v : EuclideanSpace ℂ m) (hv : ‖v‖ = 1)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hT : 0 < ‖T‖) :
    ∃ x : EuclideanSpace ℂ m, ∃ ell : StrongDual ℂ (EuclideanSpace ℂ m),
      ∃ i j : m,
        ‖x‖ < 1 ∧ ‖ell‖ ≤ 1 ∧
          κ * ‖T‖ / (Fintype.card m : ℝ) ^ 2 ≤
            ‖ell (T (PiLp.single 2 i 1)) * v j‖ := by
  obtain ⟨x, ell, hx, hell, htest⟩ :=
    exists_approx_operator_norming_test T hκ0 hκ1 hT
  let a : m → ℂ := fun i => ell (T (PiLp.single 2 i 1))
  have hxsum :
      x = ∑ i, (PiLp.single 2 i (x i) : EuclideanSpace ℂ m) := by
    ext j
    simp
  have hscalar : ell (T x) = ∑ i, a i * x i := by
    calc
      ell (T x) = ell (T
          (∑ i, (PiLp.single 2 i (x i) : EuclideanSpace ℂ m))) := by
        rw [← hxsum]
      _ = ∑ i, ell (T (PiLp.single 2 i (x i))) := by
        simp only [map_sum]
      _ = ∑ i, a i * x i := by
        apply Finset.sum_congr rfl
        intro i _
        have hsingle :
            (PiLp.single 2 i (x i) : EuclideanSpace ℂ m) =
              (x i) • (PiLp.single 2 i 1 : EuclideanSpace ℂ m) := by
          ext j
          simp [PiLp.single_apply]
        rw [hsingle, map_smul, map_smul]
        dsimp [a]
        ring
  have hnorming : κ * ‖T‖ ≤ ‖∑ i, a i * x i‖ := by
    rw [← hscalar]
    exact htest.le
  obtain ⟨i, j, hij⟩ :=
    exists_projective_singleton_coefficient_ge_of_norming_sum
      a x v (κ * ‖T‖) (mul_nonneg hκ0 hT.le) hx.le hv hnorming
  exact ⟨x, ell, i, j, hx, hell, hij⟩

end Coordinates

end CircularLawSection4
