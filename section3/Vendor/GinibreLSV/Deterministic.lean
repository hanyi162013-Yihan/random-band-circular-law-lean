/- Source snapshot: upstream-sources/i-2/work/ginibre-lsv-lean/GinibreLSV/Deterministic.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.SLT.MatrixInfra.CourantFischer
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The deterministic distance-to-span reduction

This file develops the deterministic core of the square least-singular-value
argument.  It is stated over `ℂ`, matching the random matrices in
arXiv:2606.01664.
-/

open Module
open scoped BigOperators

noncomputable section

namespace GinibreLSV

/-- Assemble a matrix from a family of Euclidean column vectors. -/
def matrixOfColumns {n : ℕ} (C : Fin n → EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => C j i

/-- The smallest domain-indexed singular value of a square complex matrix. -/
def leastSingularValue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  A.singularValues (n - 1)

/-- A column, regarded as a vector in complex Euclidean space. -/
def column {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    EuclideanSpace ℂ (Fin n) :=
  A.toEuclideanLin (EuclideanSpace.single j 1)

@[simp]
theorem column_matrixOfColumns {n : ℕ}
    (C : Fin n → EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    column (matrixOfColumns C) j = C j := by
  ext i
  simp [column, matrixOfColumns, Matrix.toLpLin_apply]

/-- The span of every column except column `j`. -/
def columnSpanExcept {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  Submodule.span ℂ (Set.range fun k : {k : Fin n // k ≠ j} => column A k)

/-- Distance of column `j` from the span of all other columns.

In finite dimension this is the norm of its orthogonal projection onto the
orthogonal complement of the other-column span.
-/
def columnDistance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : ℝ :=
  ‖(columnSpanExcept A j)ᗮ.starProjection (column A j)‖

/-- The span of all columns except one is a proper subspace: it is generated
by only `n - 1` vectors inside an `n`-dimensional complex space. -/
theorem columnSpanExcept_ne_top {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    columnSpanExcept A j ≠ ⊤ := by
  intro htop
  have hle : n ≤ Fintype.card {k : Fin n // k ≠ j} := by
    simpa [columnSpanExcept] using
      (finrank_le_of_span_eq_top (R := ℂ) (M := EuclideanSpace ℂ (Fin n)) htop)
  have hcard : Fintype.card {k : Fin n // k ≠ j} = n - 1 := by simp
  rw [hcard] at hle
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  omega

/-- Distance to the span is below `r` exactly when some linear combination
of the other columns approximates the exposed column within `r`.  This form
also makes the moving-span event visibly open. -/
theorem columnDistance_lt_iff_exists_coeff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) (r : ℝ) :
    columnDistance A j < r ↔
      ∃ a : {k : Fin n // k ≠ j} → ℂ,
        ‖column A j - ∑ k, a k • column A k‖ < r := by
  let H := columnSpanExcept A j
  let z := column A j
  constructor
  · intro hsmall
    have hv : H.starProjection z ∈ H := H.starProjection_apply_mem z
    obtain ⟨a, ha⟩ :=
      (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mp hv
    refine ⟨a, ?_⟩
    have hdecomp := H.starProjection_add_starProjection_orthogonal z
    have hresidual : z - H.starProjection z = Hᗮ.starProjection z := by
      calc
        z - H.starProjection z =
            (H.starProjection z + Hᗮ.starProjection z) - H.starProjection z :=
          congrArg (fun w => w - H.starProjection z) hdecomp.symm
        _ = Hᗮ.starProjection z := by abel
    rw [ha, hresidual]
    exact hsmall
  · rintro ⟨a, ha⟩
    let v := ∑ k, a k • column A k
    have hv : v ∈ H :=
      (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mpr ⟨a, rfl⟩
    have hprojv : Hᗮ.starProjection v = 0 :=
      Submodule.starProjection_orthogonal_apply_eq_zero hv
    have hproj : Hᗮ.starProjection z = Hᗮ.starProjection (z - v) := by
      rw [map_sub, hprojv, sub_zero]
    calc
      columnDistance A j = ‖Hᗮ.starProjection z‖ := rfl
      _ = ‖Hᗮ.starProjection (z - v)‖ := by rw [hproj]
      _ ≤ ‖z - v‖ := Hᗮ.norm_starProjection_apply_le _
      _ < r := ha

theorem toEuclideanLin_eq_sum_columns {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    A.toEuclideanLin x = ∑ j, x j • column A j := by
  ext i
  simp [column, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem column_mem_columnSpanExcept {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {j k : Fin n} (hkj : k ≠ j) :
    column A k ∈ columnSpanExcept A j := by
  apply Submodule.subset_span
  exact ⟨⟨k, hkj⟩, rfl⟩

theorem starProjection_orthogonal_toEuclideanLin {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n)
    (x : EuclideanSpace ℂ (Fin n)) :
    (columnSpanExcept A j)ᗮ.starProjection (A.toEuclideanLin x) =
      x j • (columnSpanExcept A j)ᗮ.starProjection (column A j) := by
  rw [toEuclideanLin_eq_sum_columns]
  simp_rw [map_sum, map_smul]
  rw [Finset.sum_eq_single j]
  · intro k _ hkj
    rw [Submodule.starProjection_orthogonal_apply_eq_zero
      (column_mem_columnSpanExcept A hkj)]
    simp
  · simp

/-- Projecting onto the orthogonal complement of the other columns gives the
basic distance-to-span estimate for a chosen coordinate. -/
theorem norm_coordinate_mul_columnDistance_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖x j‖ * columnDistance A j ≤ ‖A.toEuclideanLin x‖ := by
  calc
    ‖x j‖ * columnDistance A j =
        ‖x j • (columnSpanExcept A j)ᗮ.starProjection (column A j)‖ := by
      simp only [columnDistance, norm_smul]
    _ = ‖(columnSpanExcept A j)ᗮ.starProjection (A.toEuclideanLin x)‖ := by
      rw [starProjection_orthogonal_toEuclideanLin]
    _ ≤ ‖A.toEuclideanLin x‖ :=
      (columnSpanExcept A j)ᗮ.norm_starProjection_apply_le _

/-- A deliberately elementary coordinate bound.  The sharper factor is
`sqrt n`; the factor `n` here avoids any analytic overhead and is already
enough for a polynomial square-matrix lower bound. -/
theorem exists_norm_div_nat_le_norm_coordinate {n : ℕ} (hn : 0 < n)
    (x : EuclideanSpace ℂ (Fin n)) :
    ∃ j : Fin n, ‖x‖ / (n : ℝ) ≤ ‖x j‖ := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨j, hj⟩ := Finite.exists_max (fun i : Fin n => ‖x i‖)
  refine ⟨j, (div_le_iff₀ (Nat.cast_pos.mpr hn)).2 ?_⟩
  have hxsum : x = ∑ i, x i • EuclideanSpace.single i (1 : ℂ) := by
    ext k
    simp [Pi.single_apply]
  calc
    ‖x‖ = ‖∑ i, x i • EuclideanSpace.single i (1 : ℂ)‖ := congrArg norm hxsum
    _ ≤ ∑ i, ‖x i • EuclideanSpace.single i (1 : ℂ)‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ := by
      simp only [norm_smul, PiLp.norm_single, norm_one, mul_one]
    _ ≤ ∑ _i : Fin n, ‖x j‖ := Finset.sum_le_sum fun i _ => hj i
    _ = ‖x j‖ * (n : ℝ) := by simp [mul_comm]

theorem delta_div_nat_le_singularQuotient {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) {δ : ℝ}
    (hcols : ∀ j, δ ≤ columnDistance A j)
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ≠ 0) :
    δ / (n : ℝ) ≤ LinearMap.singularQuotient A.toEuclideanLin x := by
  obtain ⟨j, hj⟩ := exists_norm_div_nat_le_norm_coordinate hn x
  have hdist : 0 ≤ columnDistance A j := norm_nonneg _
  have hprod : δ * (‖x‖ / (n : ℝ)) ≤ ‖A.toEuclideanLin x‖ := by
    calc
      δ * (‖x‖ / (n : ℝ)) ≤ columnDistance A j * ‖x j‖ := by
        exact mul_le_mul (hcols j) hj
          (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) hdist
      _ = ‖x j‖ * columnDistance A j := by ring
      _ ≤ ‖A.toEuclideanLin x‖ := norm_coordinate_mul_columnDistance_le A j x
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [LinearMap.singularQuotient]
  calc
    δ / (n : ℝ) = (δ * (‖x‖ / (n : ℝ))) / ‖x‖ := by
      field_simp
    _ ≤ ‖A.toEuclideanLin x‖ / ‖x‖ :=
      (div_le_div_iff_of_pos_right hxnorm).2 hprod

theorem leastSingularValue_eq_iInf_singularQuotient {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    leastSingularValue A =
      ⨅ x : {x : EuclideanSpace ℂ (Fin n) // x ≠ 0},
        LinearMap.singularQuotient A.toEuclideanLin x := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let i : Fin (Fintype.card (Fin n)) := ⟨n - 1, by simp; omega⟩
  have hi : i.1 + 1 = Fintype.card (Fin n) := by
    dsimp [i]
    simp
    omega
  calc
    leastSingularValue A = A.toEuclideanLin.singularValues i := by rfl
    _ = LinearMap.singularCourantFischerMaxMin A.toEuclideanLin (i.1 + 1) :=
      LinearMap.singularValues_eq_singularCourantFischerMaxMin_succ
        A.toEuclideanLin finrank_euclideanSpace i
    _ = LinearMap.singularCourantFischerMaxMin A.toEuclideanLin
        (finrank ℂ (EuclideanSpace ℂ (Fin n))) := by
      rw [finrank_euclideanSpace, hi]
    _ = ⨅ x : {x : EuclideanSpace ℂ (Fin n) // x ≠ 0},
        LinearMap.singularQuotient A.toEuclideanLin x :=
      LinearMap.singularCourantFischerMaxMin_finrank A.toEuclideanLin

/-- Deterministic square-matrix reduction: if every column is at distance at
least `δ` from the span of the other columns, then the least singular value is
at least `δ / n`.

The familiar sharper statement has `sqrt n` in place of `n`.  This weaker
version is enough to turn a one-column small-ball estimate into a genuine
polynomial least-singular-value bound.
-/
theorem delta_div_nat_le_leastSingularValue {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) {δ : ℝ}
    (hcols : ∀ j, δ ≤ columnDistance A j) :
    δ / (n : ℝ) ≤ leastSingularValue A := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let j : Fin n := ⟨0, hn⟩
  letI : Nonempty {x : EuclideanSpace ℂ (Fin n) // x ≠ 0} :=
    ⟨⟨EuclideanSpace.single j 1, by simp⟩⟩
  rw [leastSingularValue_eq_iInf_singularQuotient hn]
  exact le_ciInf fun x =>
    delta_div_nat_le_singularQuotient hn A hcols x x.property

end GinibreLSV

