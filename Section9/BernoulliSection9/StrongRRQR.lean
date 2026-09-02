import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import BernoulliSection9.SingularValueMinMax
import BernoulliSection9.TerminalCUR

/-!
# Algebraic groundwork for the two-sided strong RRQR step

This module contains only proved finite-dimensional algebra.  It does **not**
postulate an RRQR output or package an RRQR certificate as an assumption.

The first part constructs the lexicographically first maximum-volume complex
coordinate minor.  The second part proves the complex Gram-volume swap bounds,
and two compatible selections produce the threshold pivot.  Using the proved
Courant--Fischer and product toolkit from `SingularValueMinMax`, the final part
derives the singular-value comparison, literal skeleton identity, polynomial
coefficient and residual bounds, and the empty-pivot convention.  No RRQR
certificate or unproved linear-algebra input occurs in the public theorem.

For arXiv:2609.01295v1 this is a quantitative variant of Lemma 9.1: the
checked bounds use `strongRRQRExponent = 16`, while the paper fixes exponent
4. The coordinate and block identities are literal; the quantitative bound
is not claimed to prove the paper's sharper fixed-4 statement.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace BernoulliSection9

open Matrix

/-! ## Finite maximum-volume coordinate minors -/

/-- An unordered coordinate subset of `Fin n` having exactly `r` elements. -/
abbrev CoordinateSubset (n r : ℕ) :=
  {s : Finset (Fin n) // s.card = r}

/-- Colexicographic order on fixed-cardinality coordinate subsets.  On a
fixed cardinality layer this is a standard lexicographic coordinate choice. -/
noncomputable instance coordinateSubsetLinearOrder (n r : ℕ) :
    LinearOrder (CoordinateSubset n r) :=
  LinearOrder.lift'
    (fun s : CoordinateSubset n r => toColex s.val)
    (fun a b h => Subtype.ext (congrArg ofColex h))

/-- The canonical coordinate subset `{0, ..., r-1}`, used only to prove that
the finite search space is nonempty when `r ≤ n`. -/
def initialCoordinateSubset {n r : ℕ} (hrn : r ≤ n) : CoordinateSubset n r :=
  ⟨Finset.univ.map (Fin.castLEEmb hrn), by simp⟩

instance coordinateSubsetNonempty {n r : ℕ} [h : Fact (r ≤ n)] :
    Nonempty (CoordinateSubset n r) :=
  ⟨initialCoordinateSubset h.out⟩

/-- A row/column pair indexing an `r × r` coordinate minor. -/
abbrev MinorSelection (n r : ℕ) :=
  CoordinateSubset n r × CoordinateSubset n r

/-- Row sets are compared first and column sets second. -/
noncomputable instance minorSelectionLinearOrder (n r : ℕ) :
    LinearOrder (MinorSelection n r) :=
  LinearOrder.lift'
    (fun selection : MinorSelection n r => toLex selection)
    (fun a b h => congrArg ofLex h)

/-- The square complex coordinate minor indexed by increasing enumerations of
the selected row and column sets. -/
def coordinateMinor {n r : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (selection : MinorSelection n r) : Matrix (Fin r) (Fin r) ℂ :=
  Q.submatrix
    (selection.1.val.orderEmbOfFin selection.1.property)
    (selection.2.val.orderEmbOfFin selection.2.property)

/-- Euclidean volume of a square complex coordinate minor.  For a square
minor this is the absolute value of its determinant. -/
def complexMinorVolume {n r : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (selection : MinorSelection n r) : ℝ :=
  ‖(coordinateMinor Q selection).det‖

/-- The largest volume among all `r × r` coordinate minors. -/
def maxComplexMinorVolume {n r : ℕ} (hrn : r ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℂ) : ℝ := by
  letI : Fact (r ≤ n) := ⟨hrn⟩
  exact (Finset.univ : Finset (MinorSelection n r)).sup'
    Finset.univ_nonempty (complexMinorVolume Q)

/-- Every coordinate minor is bounded by the finite maximum. -/
theorem complexMinorVolume_le_max {n r : ℕ} (hrn : r ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℂ) (selection : MinorSelection n r) :
    complexMinorVolume Q selection ≤ maxComplexMinorVolume hrn Q := by
  letI : Fact (r ≤ n) := ⟨hrn⟩
  exact Finset.le_sup' (f := complexMinorVolume Q) (Finset.mem_univ selection)

/-- The finite set of selections attaining the maximum minor volume. -/
def maximizingMinorSelections {n r : ℕ} (hrn : r ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℂ) : Finset (MinorSelection n r) := by
  letI : Fact (r ≤ n) := ⟨hrn⟩
  exact Finset.univ.filter fun selection =>
    complexMinorVolume Q selection = maxComplexMinorVolume hrn Q

theorem maximizingMinorSelections_nonempty {n r : ℕ} (hrn : r ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℂ) :
    (maximizingMinorSelections hrn Q).Nonempty := by
  letI : Fact (r ≤ n) := ⟨hrn⟩
  obtain ⟨selection, _hmem, hmax⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (MinorSelection n r)))
      Finset.univ_nonempty (complexMinorVolume Q)
  refine ⟨selection, ?_⟩
  simp only [maximizingMinorSelections, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hmax.symm

/-- The lexicographically first maximum-volume row/column pair.  This is a
canonical finite choice, not a caller-supplied certificate. -/
def lexFirstMaxMinorSelection {n r : ℕ} (hrn : r ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℂ) : MinorSelection n r :=
  (maximizingMinorSelections hrn Q).min'
    (maximizingMinorSelections_nonempty hrn Q)

theorem lexFirstMaxMinorSelection_mem {n r : ℕ} (hrn : r ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℂ) :
    lexFirstMaxMinorSelection hrn Q ∈ maximizingMinorSelections hrn Q :=
  Finset.min'_mem _ _

theorem lexFirstMaxMinorSelection_volume {n r : ℕ} (hrn : r ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℂ) :
    complexMinorVolume Q (lexFirstMaxMinorSelection hrn Q) =
      maxComplexMinorVolume hrn Q := by
  letI : Fact (r ≤ n) := ⟨hrn⟩
  simpa only [maximizingMinorSelections, Finset.mem_filter, Finset.mem_univ,
    true_and] using lexFirstMaxMinorSelection_mem hrn Q

/-- Lexicographic minimality among all maximum-volume selections. -/
theorem lexFirstMaxMinorSelection_le {n r : ℕ} (hrn : r ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℂ) (selection : MinorSelection n r)
    (hselection : complexMinorVolume Q selection = maxComplexMinorVolume hrn Q) :
    @LE.le (MinorSelection n r) (minorSelectionLinearOrder n r).toLE
      (lexFirstMaxMinorSelection hrn Q) selection := by
  letI : Fact (r ≤ n) := ⟨hrn⟩
  apply Finset.min'_le
  simp only [maximizingMinorSelections, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact hselection

/-- In exterior degree zero there is only the empty row/column selection. -/
theorem coordinateSubset_zero_eq {n : ℕ} (s : CoordinateSubset n 0) :
    s = ⟨∅, rfl⟩ := by
  apply Subtype.ext
  exact Finset.card_eq_zero.mp s.property

/-- The `0 × 0` coordinate minor has determinant and volume one. -/
theorem complexMinorVolume_zero {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (selection : MinorSelection n 0) :
    complexMinorVolume Q selection = 1 := by
  rcases selection with ⟨rows, cols⟩
  rw [coordinateSubset_zero_eq rows, coordinateSubset_zero_eq cols]
  simp [complexMinorVolume, coordinateMinor]

/-! ## Ordered maximum-volume search and determinant swaps

For quantitative swaps it is convenient to retain an ordering of the chosen
coordinates.  Repeated coordinates are allowed in the finite search space;
they automatically have zero determinant.  Once a positive maximal minor is
available, its row and column maps are therefore injective.
-/

abbrev OrderedMinorSelection (n r : ℕ) :=
  (Fin r → Fin n) × (Fin r → Fin n)

def orderedMinorVolume {n r : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (selection : OrderedMinorSelection n r) : ℝ :=
  ‖(Q.submatrix selection.1 selection.2).det‖

def initialOrderedMinorSelection {n r : ℕ} (hrn : r ≤ n) : OrderedMinorSelection n r :=
  (Fin.castLE hrn, Fin.castLE hrn)

/-- A maximum-volume ordered coordinate minor exists by finite search. -/
theorem exists_maximal_orderedMinorSelection {n r : ℕ} (hrn : r ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℂ) :
    ∃ selection : OrderedMinorSelection n r,
      ∀ other : OrderedMinorSelection n r,
        orderedMinorVolume Q other ≤ orderedMinorVolume Q selection := by
  let initial := initialOrderedMinorSelection hrn
  have hne : (Finset.univ : Finset (OrderedMinorSelection n r)).Nonempty :=
    ⟨initial, Finset.mem_univ initial⟩
  obtain ⟨selection, _hsel, hmax⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (OrderedMinorSelection n r)))
      hne (orderedMinorVolume Q)
  refine ⟨selection, fun other => ?_⟩
  rw [hmax.symm]
  exact Finset.le_sup' (f := orderedMinorVolume Q) (Finset.mem_univ other)

/-- The internally chosen maximum-volume ordered minor.  This is not data
supplied by a caller. -/
def maximalOrderedMinorSelection {n r : ℕ} (hrn : r ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℂ) : OrderedMinorSelection n r :=
  Classical.choose (exists_maximal_orderedMinorSelection hrn Q)

theorem maximalOrderedMinorSelection_spec {n r : ℕ} (hrn : r ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℂ) (other : OrderedMinorSelection n r) :
    orderedMinorVolume Q other ≤ orderedMinorVolume Q (maximalOrderedMinorSelection hrn Q) :=
  Classical.choose_spec (exists_maximal_orderedMinorSelection hrn Q) other

theorem maximalOrderedMinorSelection_global_bound {n r : ℕ} (hrn : r ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℂ) (rows cols : Fin r → Fin n) :
    ‖(Q.submatrix rows cols).det‖ ≤
      ‖(Q.submatrix (maximalOrderedMinorSelection hrn Q).1
        (maximalOrderedMinorSelection hrn Q).2).det‖ := by
  simpa only [orderedMinorVolume] using
    maximalOrderedMinorSelection_spec hrn Q (rows, cols)

/-- A maximum ordered minor is nonzero as soon as any ordered minor of the
same size is nonzero. -/
theorem maximalOrderedMinorSelection_det_ne_zero_of_exists {n r : ℕ}
    (hrn : r ≤ n) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hexists : ∃ rows cols : Fin r → Fin n, (Q.submatrix rows cols).det ≠ 0) :
    (Q.submatrix (maximalOrderedMinorSelection hrn Q).1
      (maximalOrderedMinorSelection hrn Q).2).det ≠ 0 := by
  obtain ⟨rows, cols, hdet⟩ := hexists
  intro hzero
  have hbound := maximalOrderedMinorSelection_global_bound hrn Q rows cols
  rw [hzero, norm_zero] at hbound
  exact hdet (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _)))

theorem rows_injective_of_isUnit_submatrix_det {n r : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℂ) (rows cols : Fin r → Fin n)
    (hK : IsUnit (Q.submatrix rows cols).det) : Function.Injective rows := by
  intro a b hab
  by_contra habne
  have hrow : (Q.submatrix rows cols) a = (Q.submatrix rows cols) b := by
    funext k
    simp [hab]
  have hzero : (Q.submatrix rows cols).det = 0 :=
    Matrix.det_zero_of_row_eq habne hrow
  exact hK.ne_zero hzero

theorem cols_injective_of_isUnit_submatrix_det {n r : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℂ) (rows cols : Fin r → Fin n)
    (hK : IsUnit (Q.submatrix rows cols).det) : Function.Injective cols := by
  intro a b hab
  by_contra habne
  have hcol : (Q.submatrix rows cols).col a = (Q.submatrix rows cols).col b := by
    funext k
    simp [Matrix.col, hab]
  have hzero : (Q.submatrix rows cols).det = 0 :=
    Matrix.det_zero_of_column_eq habne fun k => congrFun hcol k
  exact hK.ne_zero hzero

theorem maximalOrderedMinorSelection_isUnit_det_of_exists {n r : ℕ}
    (hrn : r ≤ n) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hexists : ∃ rows cols : Fin r → Fin n, (Q.submatrix rows cols).det ≠ 0) :
    IsUnit (Q.submatrix (maximalOrderedMinorSelection hrn Q).1
      (maximalOrderedMinorSelection hrn Q).2).det :=
  isUnit_iff_ne_zero.mpr
    (maximalOrderedMinorSelection_det_ne_zero_of_exists hrn Q hexists)

/-- Complex Cramer's rule in the exact form used by a column swap. -/
theorem det_updateCol_eq_det_mul_inv_mulVec {r : Type*}
    [Fintype r] [DecidableEq r]
    (K : Matrix r r ℂ) (b : r → ℂ) (i : r)
    (hK : IsUnit K.det) :
    (K.updateCol i b).det = K.det * (K⁻¹ *ᵥ b) i := by
  have h := congrFun (K.det_smul_inv_mulVec_eq_cramer b hK) i
  simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply] using h.symm

/-- Maximality of a single column replacement bounds the corresponding
inverse coefficient by one. -/
theorem inv_mulVec_entry_norm_le_one_of_maximal_update {r : Type*}
    [Fintype r] [DecidableEq r]
    (K : Matrix r r ℂ) (b : r → ℂ) (i : r)
    (hK : IsUnit K.det) (hmax : ‖(K.updateCol i b).det‖ ≤ ‖K.det‖) :
    ‖(K⁻¹ *ᵥ b) i‖ ≤ 1 := by
  rw [det_updateCol_eq_det_mul_inv_mulVec K b i hK, norm_mul] at hmax
  have hdet : 0 < ‖K.det‖ := norm_pos_iff.mpr hK.ne_zero
  nlinarith

theorem updateCol_submatrix {n r : Type*} [Fintype r] [DecidableEq r]
    (Q : Matrix n n ℂ)
    (rows cols : r → n) (i : r) (j : n) :
    (Q.submatrix rows cols).updateCol i (fun a => Q (rows a) j) =
      Q.submatrix rows (Function.update cols i j) := by
  ext a b
  by_cases hbi : b = i
  · subst b
    simp
  · simp [hbi]

/-- Every coefficient obtained by solving a maximum-volume pivot against an
arbitrary ambient column has modulus at most one. -/
theorem inverse_times_external_column_entry_norm_le_one {n r : Type*}
    [Fintype r] [DecidableEq r]
    (Q : Matrix n n ℂ) (rows cols : r → n)
    (hmax : ∀ rows' cols' : r → n,
      ‖(Q.submatrix rows' cols').det‖ ≤ ‖(Q.submatrix rows cols).det‖)
    (hK : IsUnit (Q.submatrix rows cols).det) (i : r) (j : n) :
    ‖((Q.submatrix rows cols)⁻¹ *ᵥ (fun a => Q (rows a) j)) i‖ ≤ 1 := by
  apply inv_mulVec_entry_norm_le_one_of_maximal_update _ _ _ hK
  rw [updateCol_submatrix]
  exact hmax rows (Function.update cols i j)

/-- Row version of the complex determinant-swap identity. -/
theorem det_updateRow_eq_det_mul_vecMul_inv {r : Type*}
    [Fintype r] [DecidableEq r]
    (K : Matrix r r ℂ) (b : r → ℂ) (i : r)
    (hK : IsUnit K.det) :
    (K.updateRow i b).det = K.det * (b ᵥ* K⁻¹) i := by
  have h := congrFun (K.det_smul_inv_vecMul_eq_cramer_transpose b hK) i
  simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_transpose_apply] using h.symm

theorem vecMul_inverse_entry_norm_le_one_of_maximal_update {r : Type*}
    [Fintype r] [DecidableEq r]
    (K : Matrix r r ℂ) (b : r → ℂ) (i : r)
    (hK : IsUnit K.det) (hmax : ‖(K.updateRow i b).det‖ ≤ ‖K.det‖) :
    ‖(b ᵥ* K⁻¹) i‖ ≤ 1 := by
  rw [det_updateRow_eq_det_mul_vecMul_inv K b i hK, norm_mul] at hmax
  have hdet : 0 < ‖K.det‖ := norm_pos_iff.mpr hK.ne_zero
  nlinarith

theorem updateRow_submatrix {n r : Type*} [Fintype r] [DecidableEq r]
    (Q : Matrix n n ℂ)
    (rows cols : r → n) (i : r) (j : n) :
    (Q.submatrix rows cols).updateRow i (fun b => Q j (cols b)) =
      Q.submatrix (Function.update rows i j) cols := by
  ext a b
  by_cases hai : a = i
  · subst a
    simp
  · simp [hai]

/-- Every coefficient obtained by solving an ambient row against a
maximum-volume pivot has modulus at most one. -/
theorem external_row_times_inverse_entry_norm_le_one {n r : Type*}
    [Fintype r] [DecidableEq r]
    (Q : Matrix n n ℂ) (rows cols : r → n)
    (hmax : ∀ rows' cols' : r → n,
      ‖(Q.submatrix rows' cols').det‖ ≤ ‖(Q.submatrix rows cols).det‖)
    (hK : IsUnit (Q.submatrix rows cols).det) (i : r) (j : n) :
    ‖((fun b => Q j (cols b)) ᵥ* (Q.submatrix rows cols)⁻¹) i‖ ≤ 1 := by
  apply vecMul_inverse_entry_norm_le_one_of_maximal_update _ _ _ hK
  rw [updateRow_submatrix]
  exact hmax (Function.update rows i j) cols

/-! ## From entrywise Cramer bounds to operator-norm bounds -/

/-- The Euclidean operator norm is at most the sum of the norms of all
matrix entries.  This deliberately crude finite-dimensional bound is useful
for turning maximum-volume Cramer estimates into a polynomial RRQR bound. -/
theorem matrix_l2_opNorm_le_sum_entry_norm
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) :
    ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  let y : EuclideanSpace ℂ m := Matrix.toEuclideanLin A x
  calc
    ‖Matrix.toEuclideanLin A x‖ =
        ‖∑ i, (EuclideanSpace.basisFun m ℂ).repr y i •
          EuclideanSpace.basisFun m ℂ i‖ := by
      rw [(EuclideanSpace.basisFun m ℂ).sum_repr y]
    _ ≤ ∑ i, ‖(EuclideanSpace.basisFun m ℂ).repr y i •
          EuclideanSpace.basisFun m ℂ i‖ := norm_sum_le _ _
    _ = ∑ i, ‖y i‖ := by
      congr with i
      rw [EuclideanSpace.basisFun_repr, norm_smul,
        (EuclideanSpace.basisFun m ℂ).norm_eq_one, mul_one]
    _ ≤ ∑ i, ∑ j, ‖A i j * x j‖ := by
      gcongr with i
      change ‖∑ j, A i j * x j‖ ≤ _
      exact norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖x‖ := by
      gcongr with i _ j
      rw [norm_mul]
      gcongr
      exact PiLp.norm_apply_le x j
    _ = (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by
      simp only [Finset.sum_mul]

/-- If all entries have modulus at most one, the Euclidean operator norm is
bounded by the product of the row and column cardinalities. -/
theorem matrix_l2_opNorm_le_card_mul_card_of_entry_norm_le_one
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (hA : ∀ i j, ‖A i j‖ ≤ 1) :
    ‖A‖ ≤ (Fintype.card m : ℝ) * Fintype.card n := by
  calc
    ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := matrix_l2_opNorm_le_sum_entry_norm A
    _ ≤ ∑ _i : m, ∑ _j : n, (1 : ℝ) := by
      gcongr with i _ j
      exact hA i j
    _ = (Fintype.card m : ℝ) * Fintype.card n := by simp

/-- If every entrywise cross-product of two complex matrices is at most
one, the product of their Euclidean operator norms is bounded by the
product of the four dimensions. -/
theorem matrix_l2_opNorm_mul_le_card_product_of_pairwise_entry
    {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin c) (Fin d) ℂ)
    (hpair : ∀ i j k l, ‖A i j‖ * ‖B k l‖ ≤ 1) :
    ‖A‖ * ‖B‖ ≤ (a * b * c * d : ℕ) := by
  calc
    ‖A‖ * ‖B‖ ≤
        (∑ i, ∑ j, ‖A i j‖) * (∑ k, ∑ l, ‖B k l‖) := by
      apply mul_le_mul (matrix_l2_opNorm_le_sum_entry_norm A)
        (matrix_l2_opNorm_le_sum_entry_norm B)
      · positivity
      · exact Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => norm_nonneg _
    _ = ∑ k, ∑ l, ∑ i, ∑ j, ‖A i j‖ * ‖B k l‖ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ ≤ ∑ _k : Fin c, ∑ _l : Fin d, ∑ _i : Fin a,
        ∑ _j : Fin b, (1 : ℝ) := by
      exact Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j k l
    _ = (a * b * c * d : ℕ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, Nat.cast_mul]
      ring

/-- Matrix form of the left singular-value product inequality used by the
RRQR construction. -/
theorem rrqr_matrix_singularValue_mul_le_l2OpNorm_mul {m k n : ℕ}
    (A : Matrix (Fin m) (Fin k) ℂ) (B : Matrix (Fin k) (Fin n) ℂ)
    (i : Fin n) :
    (Matrix.toEuclideanLin (A * B)).singularValues i ≤
      ‖A‖ * (Matrix.toEuclideanLin B).singularValues i := by
  let i' : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin n))) :=
    ⟨i, by simpa using i.isLt⟩
  have h := singularValue_comp_le_opNorm_mul
    (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) i'
  rw [← Matrix.toLpLin_mul_same] at h
  simpa [Matrix.l2_opNorm_def, i'] using h

theorem norm_left_le_norm_add_of_inner_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) (hxy : inner ℂ x y = 0) :
    ‖x‖ ≤ ‖x + y‖ := by
  rw [← sq_le_sq₀ (norm_nonneg x) (norm_nonneg (x + y)),
    pow_two, pow_two,
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y hxy]
  nlinarith [sq_nonneg ‖y‖]

theorem norm_right_le_norm_add_of_inner_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) (hxy : inner ℂ x y = 0) :
    ‖y‖ ≤ ‖x + y‖ := by
  rw [← sq_le_sq₀ (norm_nonneg y) (norm_nonneg (x + y)),
    pow_two, pow_two,
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y hxy]
  nlinarith [sq_nonneg ‖x‖]

theorem inner_matrix_mulVec_eq_zero_of_conjTranspose_mul_eq_zero
    {m r n : ℕ} (C : Matrix (Fin m) (Fin r) ℂ)
    (H : Matrix (Fin m) (Fin n) ℂ) (horth : Cᴴ * H = 0)
    (u : EuclideanSpace ℂ (Fin r)) (v : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (Matrix.toEuclideanLin C u) (Matrix.toEuclideanLin H v) = 0 := by
  rw [← LinearMap.adjoint_inner_right,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, horth]
  simp

theorem norm_le_l2OpNorm_mul_norm_apply_of_leftInverse
    {m r : ℕ} (L : Matrix (Fin r) (Fin m) ℂ)
    (C : Matrix (Fin m) (Fin r) ℂ) (hLC : L * C = 1)
    (u : EuclideanSpace ℂ (Fin r)) :
    ‖u‖ ≤ ‖L‖ * ‖Matrix.toEuclideanLin C u‖ := by
  have hu : u = Matrix.toEuclideanLin L (Matrix.toEuclideanLin C u) := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hLC,
      Matrix.toLpLin_one, LinearMap.id_apply]
  calc
    ‖u‖ = ‖Matrix.toEuclideanLin L (Matrix.toEuclideanLin C u)‖ :=
      congrArg norm hu
    _ ≤ ‖L‖ * ‖Matrix.toEuclideanLin C u‖ :=
      (Matrix.toEuclideanLin L).toContinuousLinearMap.le_opNorm _

theorem rrqr_matrix_l2OpNorm_le_firstSingularValue {m n : ℕ}
    (H : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n) :
    ‖H‖ ≤ (Matrix.toEuclideanLin H).singularValues 0 := by
  let T := Matrix.toEuclideanLin H
  let i : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin n))) :=
    ⟨0, by simpa using hn⟩
  have htail : singularSpectralTail T i = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_singularSpectralTail]
    simp [i]
  rw [Matrix.l2_opNorm_def]
  apply T.toContinuousLinearMap.opNorm_le_bound (T.singularValues_nonneg i)
  intro x
  apply norm_apply_le_singularValue_mul_norm_of_mem_singularSpectralTail T i
  rw [htail]
  exact Submodule.mem_top

theorem exists_vector_l2OpNorm_mul_norm_le_apply {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    ∃ v : EuclideanSpace ℂ (Fin n), v ≠ 0 ∧
      ‖H‖ * ‖v‖ ≤ ‖Matrix.toEuclideanLin H v‖ := by
  let T := Matrix.toEuclideanLin H
  let i : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin n))) :=
    ⟨0, by simpa using hn⟩
  have hhead_ne : singularSpectralHead T i ≠ ⊥ := by
    intro hbot
    have hfin := finrank_singularSpectralHead T i
    rw [hbot, finrank_bot] at hfin
    simp [i] at hfin
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hhead_ne
  refine ⟨v, hv0, ?_⟩
  exact (mul_le_mul_of_nonneg_right
      (rrqr_matrix_l2OpNorm_le_firstSingularValue H hn) (norm_nonneg v)).trans
    (singularValue_mul_norm_le_norm_apply_of_mem_singularSpectralHead T i hv)

/-- Scaled range-parametrized lower min--max principle. -/
theorem scaled_le_mul_singularValue_of_injective_parametrization
    {E F D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    [FiniteDimensional ℂ D]
    (T : E →ₗ[ℂ] F) (i : Fin (Module.finrank ℂ E))
    (Φ : D →ₗ[ℂ] E) (c scale : ℝ)
    (hdim : Module.finrank ℂ D = i + 1) (hΦ : Function.Injective Φ)
    (hscale : 0 < scale)
    (hbound : ∀ z : D, c * ‖Φ z‖ ≤ scale * ‖T (Φ z)‖) :
    c ≤ scale * T.singularValues i := by
  have hlower : c / scale ≤ T.singularValues i := by
    apply le_singularValue_of_submodule_lower_bound T i Φ.range (c / scale)
    · rw [LinearMap.finrank_range_of_inj hΦ, hdim]
    · intro x hx
      rcases hx with ⟨z, rfl⟩
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hscale).2 (by simpa [mul_comm] using hbound z)
  have heq : scale * (c / scale) = c := by
    field_simp
  rw [← heq]
  exact mul_le_mul_of_nonneg_left hlower hscale.le

/-! ## Exact complex Gram-volume swap

This is the determinant identity underlying the Gu--Eisenstat column swap.
It is proved here for genuinely complex rectangular matrices. -/

section GramSwap

variable {r : Type*} [Fintype r] [DecidableEq r]

/-- The elementary column operation whose `i`-th column is `t`. -/
def replacementCoordinates (i : r) (t : r → ℂ) : Matrix r r ℂ :=
  (1 : Matrix r r ℂ).updateCol i t

theorem det_replacementCoordinates (i : r) (t : r → ℂ) :
    (replacementCoordinates i t).det = t i := by
  simpa [replacementCoordinates] using
    det_updateCol_eq_det_mul_inv_mulVec (1 : Matrix r r ℂ) t i
      (by simpa using (isUnit_one : IsUnit (1 : ℂ)))

theorem replacementCoordinates_apply_of_ne (i : r) (t : r → ℂ)
    {a b : r} (hb : b ≠ i) :
    replacementCoordinates i t a b = if a = b then 1 else 0 := by
  simp [replacementCoordinates, hb, Matrix.one_apply]

theorem replacementCoordinates_conjTranspose_mul_apply_of_ne
    (G : Matrix r r ℂ) (i : r) (t : r → ℂ)
    {a b : r} (ha : a ≠ i) (hb : b ≠ i) :
    ((replacementCoordinates i t)ᴴ * G * replacementCoordinates i t) a b = G a b := by
  simp only [Matrix.mul_apply, replacementCoordinates, updateCol_apply,
    if_neg ha, if_neg hb, conjTranspose_apply]
  simp [Matrix.one_apply]

abbrev coordinateVector (i : r) : r → ℂ := Pi.single i 1

def normalizeCoordinate (A : Matrix r r ℂ) (i : r) : Matrix r r ℂ :=
  (A.updateRow i (coordinateVector i)).updateCol i (coordinateVector i)

theorem det_updateCol_coordinateVector_eq_det_updateRow
    (A : Matrix r r ℂ) (i : r) :
    (A.updateCol i (coordinateVector i)).det =
      (A.updateRow i (coordinateVector i)).det := by
  simp only [coordinateVector]
  calc
    (A.updateCol i (coordinateVector i)).det =
        ((A.updateCol i (coordinateVector i))ᵀ).det := by
      rw [Matrix.det_transpose]
    _ = ((Aᵀ).updateRow i (coordinateVector i)).det := by
      rw [Matrix.updateRow_transpose]
    _ = (Aᵀ).adjugate i i := by
      rw [Matrix.adjugate_apply]
    _ = A.adjugate i i := by
      rw [← Matrix.adjugate_transpose]
      rfl
    _ = (A.updateRow i (coordinateVector i)).det := by
      rw [Matrix.adjugate_apply]

theorem det_normalizeCoordinate_eq_det_updateRow
    (A : Matrix r r ℂ) (i : r) :
    (normalizeCoordinate A i).det =
      (A.updateRow i (coordinateVector i)).det := by
  let H := A.updateRow i (coordinateVector i)
  let c : r → ℂ := fun k => if k = i then 0 else -H k i
  apply Matrix.det_eq_of_forall_row_eq_smul_add_const c i
  · simp [c]
  · intro k j
    by_cases hki : k = i
    · subst k
      by_cases hji : j = i
      · subst j
        simp [normalizeCoordinate, H, c, coordinateVector]
      · simp [normalizeCoordinate, H, c, coordinateVector, hji]
    · by_cases hji : j = i
      · subst j
        simp [normalizeCoordinate, H, c, coordinateVector, hki]
      · simp [normalizeCoordinate, H, c, coordinateVector, hki, hji]

theorem det_normalizeCoordinate_eq_det_updateCol
    (A : Matrix r r ℂ) (i : r) :
    (normalizeCoordinate A i).det =
      (A.updateCol i (coordinateVector i)).det := by
  rw [det_normalizeCoordinate_eq_det_updateRow,
    ← det_updateCol_coordinateVector_eq_det_updateRow]

theorem det_updateCol_coordinateVector_eq_of_eq_off
    (A B : Matrix r r ℂ) (i : r)
    (hAB : ∀ a b, a ≠ i → b ≠ i → A a b = B a b) :
    (A.updateCol i (coordinateVector i)).det =
      (B.updateCol i (coordinateVector i)).det := by
  rw [← det_normalizeCoordinate_eq_det_updateCol A i,
    ← det_normalizeCoordinate_eq_det_updateCol B i]
  congr 1
  ext a b
  by_cases ha : a = i
  · subst a
    by_cases hb : b = i
    · subst b
      simp [normalizeCoordinate, coordinateVector]
    · simp [normalizeCoordinate, coordinateVector, hb]
  · by_cases hb : b = i
    · subst b
      simp [normalizeCoordinate, coordinateVector, ha]
    · simp [normalizeCoordinate, coordinateVector, ha, hb, hAB a b ha hb]

/-- Determinant of a congruence by one elementary column operation, followed
by a diagonal rank-one update.  This version does not assume invertibility. -/
theorem det_congruence_add_coordinate
    (G : Matrix r r ℂ) (i : r) (t : r → ℂ) (c : ℂ) :
    (((replacementCoordinates i t)ᴴ * G * replacementCoordinates i t) +
      Matrix.single i i c).det =
      star (t i) * G.det * t i +
        c * (G.updateCol i (coordinateVector i)).det := by
  let M := (replacementCoordinates i t)ᴴ * G * replacementCoordinates i t
  have hmatrix : M + Matrix.single i i c =
      M.updateCol i (M.col i + c • coordinateVector i) := by
    ext a b
    by_cases hb : b = i
    · subst b
      by_cases ha : a = i
      · subst a
        simp [M, coordinateVector, Matrix.single]
      · simp [M, coordinateVector, Matrix.single, ha, Ne.symm ha]
    · simp [M, coordinateVector, Matrix.single, hb, Ne.symm hb]
  rw [hmatrix, Matrix.det_updateCol_add]
  have hself : M.updateCol i (M.col i) = M := by
    ext a b
    by_cases hb : b = i
    · subst b
      simp [Matrix.col, Matrix.transpose_apply]
    · simp [Matrix.col, hb]
  rw [hself, Matrix.det_updateCol_smul]
  have hcofactor :
      (M.updateCol i (coordinateVector i)).det =
        (G.updateCol i (coordinateVector i)).det := by
    apply det_updateCol_coordinateVector_eq_of_eq_off
    intro a b ha hb
    exact replacementCoordinates_conjTranspose_mul_apply_of_ne G i t ha hb
  rw [hcofactor]
  simp only [M, Matrix.det_mul, Matrix.det_conjTranspose,
    det_replacementCoordinates]

/-- Invertible form of the exact Gram determinant swap. -/
theorem det_congruence_add_coordinate_of_isUnit
    (G : Matrix r r ℂ) (i : r) (t : r → ℂ) (c : ℂ)
    (hG : IsUnit G.det) :
    (((replacementCoordinates i t)ᴴ * G * replacementCoordinates i t) +
      Matrix.single i i c).det =
      G.det * (star (t i) * t i + c * G⁻¹ i i) := by
  rw [det_congruence_add_coordinate]
  have hcramer := det_updateCol_eq_det_mul_inv_mulVec
    G (coordinateVector i) i hG
  simp [coordinateVector] at hcramer
  unfold coordinateVector
  rw [hcramer]
  ring

theorem gram_updateCol_mulVec_add_of_orthogonal
    {m : Type*} [Fintype m]
    (C : Matrix m r ℂ) (i : r) (t : r → ℂ) (h : m → ℂ)
    (horth : Cᴴ *ᵥ h = 0) :
    (C.updateCol i (C *ᵥ t + h))ᴴ * (C.updateCol i (C *ᵥ t + h)) =
      (replacementCoordinates i t)ᴴ * (Cᴴ * C) * replacementCoordinates i t +
        Matrix.single i i (star h ⬝ᵥ h) := by
  let S := replacementCoordinates i t
  let e : r → ℂ := coordinateVector i
  let D : Matrix m r ℂ := C * S
  have hCS : C * S = C.updateCol i (C *ᵥ t) := by
    dsimp [S]
    rw [replacementCoordinates, Matrix.mul_updateCol, Matrix.mul_one]
  have hB : C.updateCol i (C *ᵥ t + h) = D + Matrix.vecMulVec h e := by
    ext a b
    by_cases hb : b = i
    · subst b
      simp [D, hCS, e, coordinateVector, Matrix.vecMulVec_apply]
    · simp [D, hCS, e, coordinateVector, Matrix.vecMulVec_apply, hb]
  have hDorth : Dᴴ *ᵥ h = 0 := by
    dsimp [D]
    rw [Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, horth,
      Matrix.mulVec_zero]
  have hleft : star h ᵥ* D = 0 := by
    have hc := Matrix.mulVec_conjTranspose D h
    rw [hDorth] at hc
    have hc' := congrArg star hc
    simpa using hc'.symm
  have hcrossRight : Dᴴ * Matrix.vecMulVec h e = 0 := by
    rw [Matrix.mul_vecMulVec, hDorth, Matrix.zero_vecMulVec]
  have hcrossLeft : (Matrix.vecMulVec h e)ᴴ * D = 0 := by
    rw [Matrix.conjTranspose_vecMulVec]
    have hstare : star e = e := by
      funext a
      by_cases ha : a = i
      · subst a
        simp [e, coordinateVector]
      · simp [e, coordinateVector, ha, Ne.symm ha]
    rw [hstare, Matrix.vecMulVec_mul, hleft, Matrix.vecMulVec_zero]
  have hself :
      (Matrix.vecMulVec h e)ᴴ * Matrix.vecMulVec h e =
        Matrix.single i i (star h ⬝ᵥ h) := by
    rw [Matrix.conjTranspose_vecMulVec]
    have hstare : star e = e := by
      funext a
      by_cases ha : a = i
      · subst a
        simp [e, coordinateVector]
      · simp [e, coordinateVector, ha, Ne.symm ha]
    rw [hstare, Matrix.vecMulVec_mul_vecMulVec]
    ext a b
    by_cases ha : a = i <;> by_cases hb : b = i
    · subst a
      subst b
      simp [e, coordinateVector, Matrix.vecMulVec_apply, Matrix.single]
    · subst a
      simp [e, coordinateVector, Matrix.vecMulVec_apply, Matrix.single, hb, Ne.symm hb]
    · subst b
      simp [e, coordinateVector, Matrix.vecMulVec_apply, Matrix.single, ha,
        Ne.symm ha]
    · simp [e, coordinateVector, Matrix.vecMulVec_apply, Matrix.single, ha, hb,
        Ne.symm ha, Ne.symm hb]
  have hgramD : Dᴴ * D = Sᴴ * (Cᴴ * C) * S := by
    simp [D, Matrix.mul_assoc]
  rw [hB]
  simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  rw [hcrossRight, hcrossLeft, hself, hgramD, add_zero, zero_add]

/-- The exact complex Gram determinant swap for an orthogonal residual. -/
theorem det_gram_updateCol_mulVec_add_of_orthogonal
    {m : Type*} [Fintype m]
    (C : Matrix m r ℂ) (i : r) (t : r → ℂ) (h : m → ℂ)
    (horth : Cᴴ *ᵥ h = 0) (hGram : IsUnit (Cᴴ * C).det) :
    ((C.updateCol i (C *ᵥ t + h))ᴴ *
      (C.updateCol i (C *ᵥ t + h))).det =
      (Cᴴ * C).det *
        (star (t i) * t i + (star h ⬝ᵥ h) * (Cᴴ * C)⁻¹ i i) := by
  rw [gram_updateCol_mulVec_add_of_orthogonal C i t h horth]
  exact det_congruence_add_coordinate_of_isUnit
    (Cᴴ * C) i t (star h ⬝ᵥ h) hGram

/-- Least-squares coordinates against a full-column-rank complex matrix. -/
def leastSquaresCoordinates {m : Type*} [Fintype m]
    (C : Matrix m r ℂ) (b : m → ℂ) : r → ℂ :=
  (Cᴴ * C)⁻¹ *ᵥ (Cᴴ *ᵥ b)

/-- Orthogonal least-squares residual. -/
def leastSquaresResidual {m : Type*} [Fintype m]
    (C : Matrix m r ℂ) (b : m → ℂ) : m → ℂ :=
  b - C *ᵥ leastSquaresCoordinates C b

theorem leastSquaresResidual_orthogonal {m : Type*} [Fintype m]
    (C : Matrix m r ℂ) (b : m → ℂ)
    (hGram : IsUnit (Cᴴ * C).det) :
    Cᴴ *ᵥ leastSquaresResidual C b = 0 := by
  rw [leastSquaresResidual, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  unfold leastSquaresCoordinates
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGram,
    Matrix.one_mulVec, sub_self]

theorem leastSquares_reconstruction {m : Type*} [Fintype m]
    (C : Matrix m r ℂ) (b : m → ℂ) :
    C *ᵥ leastSquaresCoordinates C b + leastSquaresResidual C b = b := by
  simp [leastSquaresResidual]

/-- Exact least-squares form of the complex maximum-volume swap ratio. -/
theorem det_gram_updateCol_leastSquares {m : Type*} [Fintype m]
    (C : Matrix m r ℂ) (b : m → ℂ) (i : r)
    (hGram : IsUnit (Cᴴ * C).det) :
    ((C.updateCol i b)ᴴ * (C.updateCol i b)).det =
      (Cᴴ * C).det *
        (star (leastSquaresCoordinates C b i) * leastSquaresCoordinates C b i +
          (star (leastSquaresResidual C b) ⬝ᵥ leastSquaresResidual C b) *
            (Cᴴ * C)⁻¹ i i) := by
  have hcol : C.updateCol i b =
      C.updateCol i
        (C *ᵥ leastSquaresCoordinates C b + leastSquaresResidual C b) := by
    rw [leastSquares_reconstruction]
  rw [hcol]
  exact det_gram_updateCol_mulVec_add_of_orthogonal
    C i (leastSquaresCoordinates C b) (leastSquaresResidual C b)
      (leastSquaresResidual_orthogonal C b hGram) hGram

end GramSwap

/-! ## Finite maximum Gram-volume column selection -/

abbrev OrderedColumnSelection (n r : ℕ) := Fin r → Fin n

theorem matrix_rank_eq_finrank_range_toEuclideanLin {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    A.rank = Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin A)) := by
  exact A.rank_eq_finrank_range_toLin
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis

/-- A positive `k`-th singular value supplies at least `k+1` independent
columns. -/
theorem succ_le_matrix_rank_of_singularValue_pos {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hpos : 0 < (Matrix.toEuclideanLin A).singularValues k) :
    k + 1 ≤ A.rank := by
  rw [matrix_rank_eq_finrank_range_toEuclideanLin]
  exact Nat.add_one_le_iff.mpr
    ((Matrix.toEuclideanLin A).singularValues_pos_iff_lt_finrank_range.mp hpos)

/-- Coordinate indices of singular values strictly above the RRQR threshold. -/
def largeSingularValueIndices {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (tau : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => tau < (Matrix.toEuclideanLin A).singularValues i

/-- `r = #{j : s_j(A) > tau}` in zero-based Lean notation. -/
def largeSingularValueCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (tau : ℝ) : ℕ := (largeSingularValueIndices A tau).card

theorem largeSingularValueCount_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (tau : ℝ) : largeSingularValueCount A tau ≤ n := by
  simpa [largeSingularValueCount, largeSingularValueIndices] using
    Finset.card_le_card (Finset.filter_subset
      (fun i : Fin n => tau < (Matrix.toEuclideanLin A).singularValues i) Finset.univ)

/-- If the threshold count is nonzero, the last singular value in that
initial segment is still strictly above the threshold. -/
theorem singularValue_pred_count_gt {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ)
    (hcount : 0 < largeSingularValueCount A tau) :
    tau < (Matrix.toEuclideanLin A).singularValues
      (largeSingularValueCount A tau - 1) := by
  let S := largeSingularValueIndices A tau
  let r := largeSingularValueCount A tau
  have hrn : r ≤ n := largeSingularValueCount_le A tau
  have hklt : r - 1 < n := by omega
  let k : Fin n := ⟨r - 1, hklt⟩
  change tau < (Matrix.toEuclideanLin A).singularValues (r - 1)
  by_contra hnot
  have hsk : (Matrix.toEuclideanLin A).singularValues k ≤ tau := by
    exact le_of_not_gt hnot
  have hlt : ∀ x : {i // i ∈ S}, x.val.val < r - 1 := by
    intro x
    by_contra hx
    have hkx : k ≤ x.val := by
      exact Fin.mk_le_mk.mpr (le_of_not_gt hx)
    have hsvle := (Matrix.toEuclideanLin A).singularValues_antitone hkx
    have hxmem : tau < (Matrix.toEuclideanLin A).singularValues x.val := by
      simpa [S, largeSingularValueIndices] using x.property
    linarith
  let emb : {i // i ∈ S} → Fin (r - 1) := fun x => ⟨x.val.val, hlt x⟩
  have hemb : Function.Injective emb := by
    intro x y hxy
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin (r - 1) => z.val) hxy
  have hcard := Fintype.card_le_of_injective emb hemb
  have hScard : Fintype.card {i // i ∈ S} = r := by
    simp [S, r, largeSingularValueCount]
  rw [hScard] at hcard
  simp at hcard
  omega

/-- The singular value immediately after the strictly-above-threshold
initial segment is at most the threshold. -/
theorem singularValue_count_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ)
    (hcount : largeSingularValueCount A tau < n) :
    (Matrix.toEuclideanLin A).singularValues
      (largeSingularValueCount A tau) ≤ tau := by
  let S := largeSingularValueIndices A tau
  let r := largeSingularValueCount A tau
  by_contra hnot
  have hgt : tau < (Matrix.toEuclideanLin A).singularValues r :=
    lt_of_not_ge hnot
  have hrn : r + 1 ≤ n := by omega
  let emb : Fin (r + 1) → {i // i ∈ S} := fun k =>
    ⟨⟨k, lt_of_lt_of_le k.isLt hrn⟩, by
      dsimp [S]
      simp only [largeSingularValueIndices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hgt.trans_le
        ((Matrix.toEuclideanLin A).singularValues_antitone
          (Nat.le_of_lt_succ k.isLt))⟩
  have hemb : Function.Injective emb := by
    intro x y hxy
    apply Fin.ext
    exact congrArg (fun z : {i // i ∈ S} => z.val.val) hxy
  have hcard := Fintype.card_le_of_injective emb hemb
  have hScard : Fintype.card {i // i ∈ S} = r := by
    simp [S, r, largeSingularValueCount]
  rw [hScard] at hcard
  simp at hcard

theorem largeSingularValueCount_le_rank {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    largeSingularValueCount A tau ≤ A.rank := by
  by_cases hzero : largeSingularValueCount A tau = 0
  · simp [hzero]
  · have hcount : 0 < largeSingularValueCount A tau := Nat.pos_of_ne_zero hzero
    have hsv := singularValue_pred_count_gt A tau hcount
    have hpos : 0 < (Matrix.toEuclideanLin A).singularValues
        (largeSingularValueCount A tau - 1) := htau.trans_lt hsv
    have hrank := succ_le_matrix_rank_of_singularValue_pos A hpos
    omega

def selectedColumns {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (cols : OrderedColumnSelection n r) : Matrix (Fin m) (Fin r) ℂ :=
  A.submatrix id cols

/-- Coordinate injection matrix associated with an ordered list of columns. -/
def columnSelector {n r : ℕ} (cols : OrderedColumnSelection n r) :
    Matrix (Fin n) (Fin r) ℂ :=
  fun a i => if a = cols i then 1 else 0

/-- Extend a proved injective coordinate selection by an internally chosen
enumeration of its complement.  The selected coordinates are kept in their
original order on the left summand. -/
def injectiveSelectionSumEquiv {n r : ℕ} (f : Fin r → Fin n)
    (hf : Function.Injective f) (hrn : r ≤ n) :
    Fin r ⊕ Fin (n - r) ≃ Fin n := by
  classical
  let eRange : Fin r ≃ Set.range f := Equiv.ofInjective f hf
  have hcompl : Fintype.card (Fin (n - r)) =
      Fintype.card ((Set.range f)ᶜ : Set (Fin n)) := by
    rw [Fintype.card_fin, Fintype.card_compl_set, Fintype.card_fin]
    have hrange : Fintype.card (Set.range f) = r := by
      rw [← Fintype.card_congr eRange]
      simp
    rw [hrange]
  let eCompl : Fin (n - r) ≃ ((Set.range f)ᶜ : Set (Fin n)) :=
    Fintype.equivOfCardEq hcompl
  exact (Equiv.sumCongr eRange eCompl).trans
    (Equiv.Set.sumCompl (Set.range f))

@[simp]
theorem injectiveSelectionSumEquiv_inl {n r : ℕ} (f : Fin r → Fin n)
    (hf : Function.Injective f) (hrn : r ≤ n) (i : Fin r) :
    injectiveSelectionSumEquiv f hf hrn (Sum.inl i) = f i := by
  classical
  simp [injectiveSelectionSumEquiv]

/-- Parametrization of the selected coordinate subspace enlarged by one
complement direction. -/
def selectorSpanMap {n r : ℕ} (S : Matrix (Fin n) (Fin r) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    (EuclideanSpace ℂ (Fin r) × ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) where
  toFun z := Matrix.toEuclideanLin S z.1 + z.2 • x
  map_add' z w := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
    abel
  map_smul' c z := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, smul_smul]
    simp

/-- The same span parametrization, equipped with the Hilbert direct-sum norm.
This is the version used in Courant--Fischer arguments. -/
def selectorSpanL2Map {n r : ℕ} (S : Matrix (Fin n) (Fin r) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    WithLp 2 (EuclideanSpace ℂ (Fin r) × ℂ) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin n) :=
  (selectorSpanMap S x).comp
    (WithLp.linearEquiv 2 ℂ (EuclideanSpace ℂ (Fin r) × ℂ)).toLinearMap

theorem selectorSpanMap_injective {n r : ℕ}
    (S : Matrix (Fin n) (Fin r) ℂ) (hRS : Sᴴ * S = 1)
    (x : EuclideanSpace ℂ (Fin n))
    (hRx : Matrix.toEuclideanLin Sᴴ x = 0) (hx : x ≠ 0) :
    Function.Injective (selectorSpanMap S x) := by
  intro z w hzw
  have hfst : z.1 = w.1 := by
    have h := congrArg (Matrix.toEuclideanLin Sᴴ) hzw
    change Matrix.toEuclideanLin Sᴴ
        (Matrix.toEuclideanLin S z.1 + z.2 • x) =
      Matrix.toEuclideanLin Sᴴ
        (Matrix.toEuclideanLin S w.1 + w.2 • x) at h
    simp only [map_add, map_smul, hRx, smul_zero, add_zero] at h
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hRS,
      Matrix.toLpLin_one, LinearMap.id_apply,
      ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hRS,
      Matrix.toLpLin_one, LinearMap.id_apply] at h
    exact h
  have hs : z.2 • x = w.2 • x := by
    change Matrix.toEuclideanLin S z.1 + z.2 • x =
      Matrix.toEuclideanLin S w.1 + w.2 • x at hzw
    rw [hfst] at hzw
    exact add_left_cancel hzw
  have hs0 : (z.2 - w.2) • x = 0 := by
    rw [sub_smul, hs, sub_self]
  have hsnd : z.2 = w.2 := by
    exact sub_eq_zero.mp ((smul_eq_zero_iff_left hx).mp hs0)
  exact Prod.ext hfst hsnd

theorem selectorSpanL2Map_injective {n r : ℕ}
    (S : Matrix (Fin n) (Fin r) ℂ) (hRS : Sᴴ * S = 1)
    (x : EuclideanSpace ℂ (Fin n))
    (hRx : Matrix.toEuclideanLin Sᴴ x = 0) (hx : x ≠ 0) :
    Function.Injective (selectorSpanL2Map S x) := by
  intro z w hzw
  apply (WithLp.linearEquiv 2 ℂ
    (EuclideanSpace ℂ (Fin r) × ℂ)).injective
  exact selectorSpanMap_injective S hRS x hRx hx hzw

theorem mul_columnSelector {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (cols : OrderedColumnSelection n r) :
    A * columnSelector cols = selectedColumns A cols := by
  ext a i
  simp [columnSelector, selectedColumns, Matrix.mul_apply]

theorem columnSelector_conjTranspose_mul_self {n r : ℕ}
    (cols : OrderedColumnSelection n r) (hcols : Function.Injective cols) :
    (columnSelector cols)ᴴ * columnSelector cols = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [columnSelector, Matrix.mul_apply]
  · have hc : cols i ≠ cols j := fun h => hij (hcols h)
    simp [columnSelector, Matrix.mul_apply, hij, hc, Ne.symm hc]

theorem columnSelector_mulVec_norm {n r : ℕ}
    (cols : OrderedColumnSelection n r) (hcols : Function.Injective cols)
    (x : EuclideanSpace ℂ (Fin r)) :
    ‖Matrix.toEuclideanLin (columnSelector cols) x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [sq, ← @inner_self_eq_norm_sq ℂ]
  rw [← LinearMap.adjoint_inner_left,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
    columnSelector_conjTranspose_mul_self cols hcols, Matrix.toLpLin_one,
    LinearMap.id_apply]

theorem norm_columnSelector_le_one {n r : ℕ}
    (cols : OrderedColumnSelection n r) (hcols : Function.Injective cols) :
    ‖columnSelector cols‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_def]
  apply (Matrix.toEuclideanLin (columnSelector cols)).toContinuousLinearMap.opNorm_le_bound
    zero_le_one
  intro x
  change ‖Matrix.toEuclideanLin (columnSelector cols) x‖ ≤ 1 * ‖x‖
  rw [columnSelector_mulVec_norm cols hcols, one_mul]

theorem submatrix_rows_eq_conjTranspose_columnSelector_mul
    {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (rows : Fin r → Fin m) :
    A.submatrix rows id = (columnSelector rows)ᴴ * A := by
  ext i j
  simp [columnSelector, Matrix.mul_apply]

theorem submatrix_cols_eq_mul_columnSelector
    {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (cols : Fin r → Fin n) :
    A.submatrix id cols = A * columnSelector cols := by
  ext i j
  simp [columnSelector, Matrix.mul_apply]

theorem norm_submatrix_rows_le {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (rows : Fin r → Fin m)
    (hrows : Function.Injective rows) :
    ‖A.submatrix rows id‖ ≤ ‖A‖ := by
  rw [submatrix_rows_eq_conjTranspose_columnSelector_mul]
  calc
    ‖(columnSelector rows)ᴴ * A‖ ≤ ‖(columnSelector rows)ᴴ‖ * ‖A‖ :=
      Matrix.l2_opNorm_mul _ _
    _ = ‖columnSelector rows‖ * ‖A‖ := by
      rw [Matrix.l2_opNorm_conjTranspose]
    _ ≤ 1 * ‖A‖ := mul_le_mul_of_nonneg_right
      (norm_columnSelector_le_one rows hrows) (norm_nonneg A)
    _ = ‖A‖ := one_mul _

theorem norm_submatrix_cols_le {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (cols : Fin r → Fin n)
    (hcols : Function.Injective cols) :
    ‖A.submatrix id cols‖ ≤ ‖A‖ := by
  rw [submatrix_cols_eq_mul_columnSelector]
  calc
    ‖A * columnSelector cols‖ ≤ ‖A‖ * ‖columnSelector cols‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left
      (norm_columnSelector_le_one cols hcols) (norm_nonneg A)
    _ = ‖A‖ := mul_one _

theorem norm_submatrix_le {m n a b : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (rows : Fin a → Fin m)
    (cols : Fin b → Fin n) (hrows : Function.Injective rows)
    (hcols : Function.Injective cols) :
    ‖A.submatrix rows cols‖ ≤ ‖A‖ := by
  have heq : A.submatrix rows cols = (A.submatrix rows id).submatrix id cols := by
    ext i j
    rfl
  rw [heq]
  exact (norm_submatrix_cols_le (A.submatrix rows id) cols hcols).trans
    (norm_submatrix_rows_le A rows hrows)

/-- Squared Euclidean volume of a rectangular complex column submatrix. -/
def columnGramVolume {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (cols : OrderedColumnSelection n r) : ℝ :=
  Complex.re (((selectedColumns A cols)ᴴ * selectedColumns A cols).det)

def initialOrderedColumnSelection {n r : ℕ} (hrn : r ≤ n) :
    OrderedColumnSelection n r := Fin.castLE hrn

theorem exists_maximal_orderedColumnSelection {m n r : ℕ} (hrn : r ≤ n)
    (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ cols : OrderedColumnSelection n r,
      ∀ other : OrderedColumnSelection n r,
        columnGramVolume A other ≤ columnGramVolume A cols := by
  let initial := initialOrderedColumnSelection hrn
  have hne : (Finset.univ : Finset (OrderedColumnSelection n r)).Nonempty :=
    ⟨initial, Finset.mem_univ initial⟩
  obtain ⟨cols, _hcols, hmax⟩ :=
    Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (OrderedColumnSelection n r)))
      hne (columnGramVolume A)
  refine ⟨cols, fun other => ?_⟩
  rw [hmax.symm]
  exact Finset.le_sup' (f := columnGramVolume A) (Finset.mem_univ other)

/-- Internally chosen maximum Gram-volume ordered column set. -/
def maximalOrderedColumnSelection {m n r : ℕ} (hrn : r ≤ n)
    (A : Matrix (Fin m) (Fin n) ℂ) : OrderedColumnSelection n r :=
  Classical.choose (exists_maximal_orderedColumnSelection hrn A)

theorem maximalOrderedColumnSelection_spec {m n r : ℕ} (hrn : r ≤ n)
    (A : Matrix (Fin m) (Fin n) ℂ) (other : OrderedColumnSelection n r) :
    columnGramVolume A other ≤
      columnGramVolume A (maximalOrderedColumnSelection hrn A) :=
  Classical.choose_spec (exists_maximal_orderedColumnSelection hrn A) other

theorem maximalOrderedColumnSelection_gram_isUnit_of_exists_pos
    {m n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hexists : ∃ cols : OrderedColumnSelection n r, 0 < columnGramVolume A cols) :
    IsUnit (((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
      selectedColumns A (maximalOrderedColumnSelection hrn A)).det) := by
  obtain ⟨cols, hcols⟩ := hexists
  have hpos : 0 < columnGramVolume A (maximalOrderedColumnSelection hrn A) :=
    hcols.trans_le (maximalOrderedColumnSelection_spec hrn A cols)
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  simp [columnGramVolume, hzero] at hpos

theorem selectedColumns_updateCol {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (cols : OrderedColumnSelection n r)
    (i : Fin r) (j : Fin n) :
    (selectedColumns A cols).updateCol i (fun a => A a j) =
      selectedColumns A (Function.update cols i j) := by
  ext a b
  by_cases hb : b = i
  · subst b
    simp [selectedColumns]
  · simp [selectedColumns, hb]

/-- Rank at least `r` produces an actual positive Gram-volume `r`-column
selection.  This is the bridge from rank/singular-value data to the finite
maximum-volume search. -/
theorem exists_orderedColumnSelection_pos_of_le_rank {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hrank : r ≤ A.rank) :
    ∃ cols : OrderedColumnSelection n r, 0 < columnGramVolume A cols := by
  rw [A.rank_eq_finrank_span_cols] at hrank
  obtain ⟨f, hfmem, _hfspan, hfLI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range A.col)
  let g : Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range A.col))) → Fin n :=
    fun i => Classical.choose (hfmem i)
  have hg : ∀ i, A.col (g i) = f i := fun i => Classical.choose_spec (hfmem i)
  let inc : Fin r → Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range A.col))) :=
    Fin.castLE hrank
  let cols : OrderedColumnSelection n r := fun i => g (inc i)
  have hLIcomp : LinearIndependent ℂ (fun i : Fin r => f (inc i)) :=
    hfLI.comp inc (Fin.castLE_injective hrank)
  have hcols : (selectedColumns A cols).col = fun i : Fin r => f (inc i) := by
    funext i
    ext a
    exact congrFun (hg (inc i)) a
  have hLI : LinearIndependent ℂ (selectedColumns A cols).col := by
    rw [hcols]
    exact hLIcomp
  have hposDef : ((selectedColumns A cols)ᴴ * selectedColumns A cols).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self _
      (Matrix.mulVec_injective_iff.mpr hLI)
  refine ⟨cols, ?_⟩
  exact (RCLike.pos_iff.mp hposDef.det_pos).1

theorem maximalOrderedColumnSelection_gram_isUnit_of_le_rank
    {m n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hrank : r ≤ A.rank) :
    IsUnit (((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
      selectedColumns A (maximalOrderedColumnSelection hrn A)).det) :=
  maximalOrderedColumnSelection_gram_isUnit_of_exists_pos hrn A
    (exists_orderedColumnSelection_pos_of_le_rank A hrank)

/-- The finite maximum-volume column selection at the paper's threshold
count is automatically full column rank; no selection certificate is exposed. -/
theorem thresholdMaximalColumnSelection_gram_isUnit {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    IsUnit
      (((selectedColumns A
          (maximalOrderedColumnSelection (largeSingularValueCount_le A tau) A))ᴴ *
        selectedColumns A
          (maximalOrderedColumnSelection (largeSingularValueCount_le A tau) A)).det) :=
  maximalOrderedColumnSelection_gram_isUnit_of_le_rank
    (largeSingularValueCount_le A tau) A
    (largeSingularValueCount_le_rank A tau htau)

/-- A nonsingular complex Gram matrix is positive definite. -/
theorem posDef_gram_of_isUnit_det {m r : ℕ}
    (C : Matrix (Fin m) (Fin r) ℂ) (hGram : IsUnit (Cᴴ * C).det) :
    (Cᴴ * C).PosDef := by
  apply Matrix.PosDef.conjTranspose_mul_self C
  intro x y hxy
  have hinj : Function.Injective (Cᴴ * C).mulVec :=
    Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det (Cᴴ * C)).mpr hGram)
  apply hinj
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]

theorem rank_eq_width_of_gram_isUnit {m r : ℕ}
    (C : Matrix (Fin m) (Fin r) ℂ) (hGram : IsUnit (Cᴴ * C).det) :
    C.rank = r := by
  rw [Matrix.rank]
  rw [LinearMap.finrank_range_of_inj]
  · simp
  · change Function.Injective C.mulVec
    intro x y hxy
    have hinj : Function.Injective (Cᴴ * C).mulVec :=
      Matrix.mulVec_injective_of_isUnit
        ((Matrix.isUnit_iff_isUnit_det (Cᴴ * C)).mpr hGram)
    apply hinj
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]

theorem selectedColumns_selection_injective_of_gram_isUnit {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (cols : OrderedColumnSelection n r)
    (hGram : IsUnit (((selectedColumns A cols)ᴴ * selectedColumns A cols).det)) :
    Function.Injective cols := by
  let C := selectedColumns A cols
  have hC : Function.Injective C.mulVec := by
    intro x y hxy
    have hinj : Function.Injective (Cᴴ * C).mulVec :=
      Matrix.mulVec_injective_of_isUnit
        ((Matrix.isUnit_iff_isUnit_det (Cᴴ * C)).mpr hGram)
    apply hinj
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
  intro i j hij
  by_contra hne
  have hv : C *ᵥ Pi.single i 1 = C *ᵥ Pi.single j 1 := by
    rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    ext a
    simp [C, selectedColumns, hij]
  have hsingle := hC hv
  have hat := congrFun hsingle i
  simp [Pi.single_apply, hne] at hat

theorem rank_conjTranspose_eq_width_of_gram_isUnit {m r : ℕ}
    (C : Matrix (Fin m) (Fin r) ℂ) (hGram : IsUnit (Cᴴ * C).det) :
    Cᴴ.rank = r := by
  rw [Matrix.rank_conjTranspose, rank_eq_width_of_gram_isUnit C hGram]

def leastSquaresSwapFactor {m r : ℕ} (C : Matrix (Fin m) (Fin r) ℂ)
    (b : Fin m → ℂ) (i : Fin r) : ℂ :=
  star (leastSquaresCoordinates C b i) * leastSquaresCoordinates C b i +
    (star (leastSquaresResidual C b) ⬝ᵥ leastSquaresResidual C b) *
      (Cᴴ * C)⁻¹ i i

theorem leastSquaresSwapFactor_nonneg {m r : ℕ}
    (C : Matrix (Fin m) (Fin r) ℂ) (b : Fin m → ℂ) (i : Fin r)
    (hGram : IsUnit (Cᴴ * C).det) :
    0 ≤ leastSquaresSwapFactor C b i := by
  apply add_nonneg (star_mul_self_nonneg _)
  apply mul_nonneg (dotProduct_star_self_nonneg _)
  exact (posDef_gram_of_isUnit_det C hGram).inv.diag_pos.le

/-- Maximum Gram volume bounds the real swap factor by one. -/
theorem maximalOrderedColumnSelection_swapFactor_re_le_one
    {m n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hGram : IsUnit
      (((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
        selectedColumns A (maximalOrderedColumnSelection hrn A)).det))
    (i : Fin r) (j : Fin n) :
    Complex.re (leastSquaresSwapFactor
      (selectedColumns A (maximalOrderedColumnSelection hrn A))
      (fun a => A a j) i) ≤ 1 := by
  let cols := maximalOrderedColumnSelection hrn A
  let C := selectedColumns A cols
  let b : Fin m → ℂ := fun a => A a j
  let factor := leastSquaresSwapFactor C b i
  have hmax := maximalOrderedColumnSelection_spec hrn A (Function.update cols i j)
  have hswap := det_gram_updateCol_leastSquares C b i hGram
  have hCupdate : C.updateCol i b =
      selectedColumns A (Function.update cols i j) := by
    exact selectedColumns_updateCol A cols i j
  have hvol : Complex.re (((C.updateCol i b)ᴴ * (C.updateCol i b)).det) ≤
      Complex.re ((Cᴴ * C).det) := by
    simpa only [columnGramVolume, C, cols, b, hCupdate] using hmax
  have hfactor_nonneg : 0 ≤ factor := by
    exact leastSquaresSwapFactor_nonneg C b i hGram
  have hdet_pos : 0 < (Cᴴ * C).det :=
    (posDef_gram_of_isUnit_det C hGram).det_pos
  have hdet_im : Complex.im ((Cᴴ * C).det) = 0 :=
    (RCLike.nonneg_iff.mp hdet_pos.le).2
  have hfactor_im : Complex.im factor = 0 :=
    (RCLike.nonneg_iff.mp hfactor_nonneg).2
  have hdet_re_pos : 0 < Complex.re ((Cᴴ * C).det) :=
    (RCLike.pos_iff.mp hdet_pos).1
  change Complex.re factor ≤ 1
  change ((C.updateCol i b)ᴴ * (C.updateCol i b)).det =
    (Cᴴ * C).det * factor at hswap
  rw [hswap, Complex.mul_re, hdet_im, hfactor_im] at hvol
  norm_num at hvol
  nlinarith

/-- Every least-squares coefficient of the maximum-volume choice has
modulus at most one. -/
theorem maximalOrderedColumnSelection_leastSquares_entry_norm_le_one
    {m n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hGram : IsUnit
      (((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
        selectedColumns A (maximalOrderedColumnSelection hrn A)).det))
    (i : Fin r) (j : Fin n) :
    ‖leastSquaresCoordinates
      (selectedColumns A (maximalOrderedColumnSelection hrn A))
      (fun a => A a j) i‖ ≤ 1 := by
  let C := selectedColumns A (maximalOrderedColumnSelection hrn A)
  let b : Fin m → ℂ := fun a => A a j
  let t := leastSquaresCoordinates C b
  let h := leastSquaresResidual C b
  have hfactor := maximalOrderedColumnSelection_swapFactor_re_le_one
    hrn A hGram i j
  have hdiag : 0 ≤ (Cᴴ * C)⁻¹ i i :=
    (posDef_gram_of_isUnit_det C hGram).inv.diag_pos.le
  have hres : 0 ≤ star h ⬝ᵥ h := dotProduct_star_self_nonneg h
  have hterm : 0 ≤
      Complex.re ((star h ⬝ᵥ h) * (Cᴴ * C)⁻¹ i i) := by
    exact (RCLike.nonneg_iff.mp (mul_nonneg hres hdiag)).1
  have hsq_re : Complex.re (star (t i) * t i) ≤ 1 := by
    change Complex.re
      (star (leastSquaresCoordinates C b i) * leastSquaresCoordinates C b i +
        (star (leastSquaresResidual C b) ⬝ᵥ leastSquaresResidual C b) *
          (Cᴴ * C)⁻¹ i i) ≤ 1 at hfactor
    rw [Complex.add_re] at hfactor
    change 0 ≤ Complex.re
      ((star (leastSquaresResidual C b) ⬝ᵥ leastSquaresResidual C b) *
        (Cᴴ * C)⁻¹ i i) at hterm
    dsimp [t, h]
    exact (le_add_of_nonneg_right hterm).trans hfactor
  have hsq : ‖t i‖ ^ 2 ≤ 1 := by
    have hconj' : ‖t i‖ ^ 2 = Complex.re (star (t i) * t i) := by
      rw [RCLike.norm_sq_eq_def]
      simp [Complex.mul_re]
    rw [hconj']
    exact hsq_re
  nlinarith [norm_nonneg (leastSquaresCoordinates C b i)]

/-- The second Gu--Eisenstat swap term is at most one: squared residual
length times the corresponding diagonal entry of the inverse Gram matrix. -/
theorem maximalOrderedColumnSelection_residual_diagonal_product_re_le_one
    {m n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hGram : IsUnit
      (((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
        selectedColumns A (maximalOrderedColumnSelection hrn A)).det))
    (i : Fin r) (j : Fin n) :
    Complex.re
      ((star (leastSquaresResidual
          (selectedColumns A (maximalOrderedColumnSelection hrn A))
          (fun a => A a j)) ⬝ᵥ
        leastSquaresResidual
          (selectedColumns A (maximalOrderedColumnSelection hrn A))
          (fun a => A a j)) *
        (((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
          selectedColumns A (maximalOrderedColumnSelection hrn A))⁻¹ i i)) ≤ 1 := by
  let C := selectedColumns A (maximalOrderedColumnSelection hrn A)
  let b : Fin m → ℂ := fun a => A a j
  let t := leastSquaresCoordinates C b
  let h := leastSquaresResidual C b
  have hfactor := maximalOrderedColumnSelection_swapFactor_re_le_one
    hrn A hGram i j
  have ht : 0 ≤ Complex.re (star (t i) * t i) :=
    (RCLike.nonneg_iff.mp (star_mul_self_nonneg (t i))).1
  change Complex.re
    ((star (leastSquaresResidual C b) ⬝ᵥ leastSquaresResidual C b) *
      (Cᴴ * C)⁻¹ i i) ≤ 1
  change Complex.re
    (star (leastSquaresCoordinates C b i) * leastSquaresCoordinates C b i +
      (star (leastSquaresResidual C b) ⬝ᵥ leastSquaresResidual C b) *
        (Cᴴ * C)⁻¹ i i) ≤ 1 at hfactor
  rw [Complex.add_re] at hfactor
  change 0 ≤ Complex.re
    (star (leastSquaresCoordinates C b i) * leastSquaresCoordinates C b i) at ht
  exact (le_add_of_nonneg_left ht).trans hfactor

/-- A diagonal entry of the inverse Gram matrix dominates the squared
modulus of every entry in the corresponding row of the matrix inverse.
The identity is algebraic even for a singular matrix (where mathlib's
nonsingular inverse is zero); invertibility is imposed only where this
lemma is used quantitatively. -/
theorem inverseGram_diag_entry_lower_bound {r : ℕ}
    (C : Matrix (Fin r) (Fin r) ℂ) (i k : Fin r) :
    ‖C⁻¹ i k‖ ^ 2 ≤ Complex.re ((Cᴴ * C)⁻¹ i i) := by
  have hEq : (Cᴴ * C)⁻¹ = C⁻¹ * (C⁻¹)ᴴ := by
    rw [Matrix.mul_inv_rev, Matrix.conjTranspose_nonsing_inv]
  rw [hEq, Matrix.mul_apply]
  have hre : Complex.re (∑ j, C⁻¹ i j * (C⁻¹)ᴴ j i) =
      ∑ j, Complex.re (C⁻¹ i j * (C⁻¹)ᴴ j i) := by
    change Complex.reCLM (∑ j, C⁻¹ i j * (C⁻¹)ᴴ j i) = _
    rw [map_sum]
    simp only [Complex.reCLM_apply]
  rw [hre]
  have hsingle : Complex.re (C⁻¹ i k * (C⁻¹)ᴴ k i) ≤
      ∑ j, Complex.re (C⁻¹ i j * (C⁻¹)ᴴ j i) := by
    have hs := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun j => Complex.re (C⁻¹ i j * (C⁻¹)ᴴ j i))
      (fun j _ => by
        simp [Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_re]
        nlinarith [sq_nonneg (C⁻¹ i j).re, sq_nonneg (C⁻¹ i j).im])
      (Finset.mem_univ k)
    simpa using hs
  simpa [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.norm_sq_eq_def]
    using hsingle

/-- The canonical least-squares left inverse of a full-column-rank matrix. -/
def leastSquaresLeftInverse {m r : ℕ} (C : Matrix (Fin m) (Fin r) ℂ) :
    Matrix (Fin r) (Fin m) ℂ :=
  (Cᴴ * C)⁻¹ * Cᴴ

theorem leastSquaresLeftInverse_mul {m r : ℕ}
    (C : Matrix (Fin m) (Fin r) ℂ) (hGram : IsUnit (Cᴴ * C).det) :
    leastSquaresLeftInverse C * C = 1 := by
  rw [leastSquaresLeftInverse, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGram]

/-- The norm of a left inverse times each singular value of the original
matrix is at least one.  We use the last index later, but the stronger
all-index statement costs nothing. -/
theorem one_le_norm_leastSquaresLeftInverse_mul_singularValue
    {m r : ℕ} (C : Matrix (Fin m) (Fin r) ℂ)
    (hGram : IsUnit (Cᴴ * C).det) (i : Fin r) :
    1 ≤ ‖leastSquaresLeftInverse C‖ *
      (Matrix.toEuclideanLin C).singularValues i := by
  have h := rrqr_matrix_singularValue_mul_le_l2OpNorm_mul
    (leastSquaresLeftInverse C) C i
  rw [leastSquaresLeftInverse_mul C hGram] at h
  have hid : (Matrix.toEuclideanLin (1 : Matrix (Fin r) (Fin r) ℂ)).singularValues i =
      1 := by
    rw [Matrix.toLpLin_one]
    let i' : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin r))) :=
      ⟨i, by simpa using i.isLt⟩
    apply le_antisymm
    · apply singularValue_le_of_submodule_bound
        (LinearMap.id : EuclideanSpace ℂ (Fin r) →ₗ[ℂ]
          EuclideanSpace ℂ (Fin r)) i'
        (singularSpectralTail
          (LinearMap.id : EuclideanSpace ℂ (Fin r) →ₗ[ℂ]
            EuclideanSpace ℂ (Fin r)) i') 1
        (finrank_singularSpectralTail
          (LinearMap.id : EuclideanSpace ℂ (Fin r) →ₗ[ℂ]
            EuclideanSpace ℂ (Fin r)) i')
      intro x _
      simp
    · apply le_singularValue_of_submodule_lower_bound
        (LinearMap.id : EuclideanSpace ℂ (Fin r) →ₗ[ℂ]
          EuclideanSpace ℂ (Fin r)) i'
        (singularSpectralHead
          (LinearMap.id : EuclideanSpace ℂ (Fin r) →ₗ[ℂ]
            EuclideanSpace ℂ (Fin r)) i') 1
        (finrank_singularSpectralHead
          (LinearMap.id : EuclideanSpace ℂ (Fin r) →ₗ[ℂ]
            EuclideanSpace ℂ (Fin r)) i')
      intro x _
      simp
  rw [hid] at h
  exact h

theorem leastSquaresLeftInverse_mul_conjTranspose {m r : ℕ}
    (C : Matrix (Fin m) (Fin r) ℂ) (hGram : IsUnit (Cᴴ * C).det) :
    leastSquaresLeftInverse C * (leastSquaresLeftInverse C)ᴴ =
      (Cᴴ * C)⁻¹ := by
  have hHerm : (Cᴴ * C).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self C
  calc
    leastSquaresLeftInverse C * (leastSquaresLeftInverse C)ᴴ =
        (Cᴴ * C)⁻¹ * Cᴴ * (C * ((Cᴴ * C)⁻¹)ᴴ) := by
      simp only [leastSquaresLeftInverse, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    _ = (Cᴴ * C)⁻¹ * (Cᴴ * C) * ((Cᴴ * C)⁻¹)ᴴ := by
      simp only [Matrix.mul_assoc]
    _ = ((Cᴴ * C)⁻¹)ᴴ := by
      rw [Matrix.nonsing_inv_mul _ hGram, Matrix.one_mul]
    _ = (Cᴴ * C)⁻¹ := by
      exact hHerm.inv.eq

/-- Rectangular form of `inverseGram_diag_entry_lower_bound`: a Gram
inverse diagonal dominates each entry square of the canonical left inverse. -/
theorem inverseGram_diag_leftInverse_entry_lower_bound {m r : ℕ}
    (C : Matrix (Fin m) (Fin r) ℂ) (hGram : IsUnit (Cᴴ * C).det)
    (i : Fin r) (a : Fin m) :
    ‖leastSquaresLeftInverse C i a‖ ^ 2 ≤
      Complex.re ((Cᴴ * C)⁻¹ i i) := by
  rw [← leastSquaresLeftInverse_mul_conjTranspose C hGram, Matrix.mul_apply]
  have hre : Complex.re
      (∑ x, leastSquaresLeftInverse C i x *
        (leastSquaresLeftInverse C)ᴴ x i) =
      ∑ x, Complex.re
        (leastSquaresLeftInverse C i x *
          (leastSquaresLeftInverse C)ᴴ x i) := by
    change Complex.reCLM
      (∑ x, leastSquaresLeftInverse C i x *
        (leastSquaresLeftInverse C)ᴴ x i) = _
    rw [map_sum]
    simp only [Complex.reCLM_apply]
  rw [hre]
  have hsingle : Complex.re
      (leastSquaresLeftInverse C i a * (leastSquaresLeftInverse C)ᴴ a i) ≤
      ∑ x, Complex.re
        (leastSquaresLeftInverse C i x *
          (leastSquaresLeftInverse C)ᴴ x i) := by
    have hs := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun x => Complex.re
        (leastSquaresLeftInverse C i x *
          (leastSquaresLeftInverse C)ᴴ x i))
      (fun x _ => by
        simp [Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_re]
        nlinarith [sq_nonneg (leastSquaresLeftInverse C i x).re,
          sq_nonneg (leastSquaresLeftInverse C i x).im])
      (Finset.mem_univ a)
    simpa using hs
  simpa [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.norm_sq_eq_def]
    using hsingle

/-- One coordinate square is bounded by the real squared Euclidean
length of the whole complex vector. -/
theorem norm_entry_sq_le_re_star_dotProduct {m : ℕ}
    (h : Fin m → ℂ) (a : Fin m) :
    ‖h a‖ ^ 2 ≤ Complex.re (star h ⬝ᵥ h) := by
  simp only [dotProduct, Pi.star_apply]
  have hre : Complex.re (∑ x, star (h x) * h x) =
      ∑ x, Complex.re (star (h x) * h x) := by
    change Complex.reCLM (∑ x, star (h x) * h x) = _
    rw [map_sum]
    simp only [Complex.reCLM_apply]
  rw [hre]
  have hsingle : Complex.re (star (h a) * h a) ≤
      ∑ x, Complex.re (star (h x) * h x) := by
    have hs := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun x => Complex.re (star (h x) * h x))
      (fun x _ => by
        simp [RCLike.star_def, Complex.mul_re]
        nlinarith [sq_nonneg (h x).re, sq_nonneg (h x).im])
      (Finset.mem_univ a)
    simpa using hs
  simpa [RCLike.norm_sq_eq_def] using hsingle

/-- The exact maximum-Gram swap inequality gives a pairwise bound between
every residual entry and every entry of the inverse selected square. -/
theorem maximalOrderedColumnSelection_residual_entry_mul_inv_entry_le_one
    {n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin r) (Fin n) ℂ)
    (hGram : IsUnit
      (((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
        selectedColumns A (maximalOrderedColumnSelection hrn A)).det))
    (a : Fin r) (j : Fin n) (i k : Fin r) :
    ‖leastSquaresResidual
        (selectedColumns A (maximalOrderedColumnSelection hrn A))
        (fun x => A x j) a‖ *
      ‖(selectedColumns A (maximalOrderedColumnSelection hrn A))⁻¹ i k‖ ≤ 1 := by
  let C := selectedColumns A (maximalOrderedColumnSelection hrn A)
  let h := leastSquaresResidual C (fun x => A x j)
  have hswap := maximalOrderedColumnSelection_residual_diagonal_product_re_le_one
    hrn A hGram i j
  have hx := norm_entry_sq_le_re_star_dotProduct h a
  have hy := inverseGram_diag_entry_lower_bound C i k
  have hres : 0 ≤ star h ⬝ᵥ h := dotProduct_star_self_nonneg h
  have hdiag : 0 ≤ (Cᴴ * C)⁻¹ i i :=
    (posDef_gram_of_isUnit_det C hGram).inv.diag_pos.le
  have hresRe : 0 ≤ Complex.re (star h ⬝ᵥ h) :=
    (RCLike.nonneg_iff.mp hres).1
  have hdiagRe : 0 ≤ Complex.re ((Cᴴ * C)⁻¹ i i) :=
    (RCLike.nonneg_iff.mp hdiag).1
  have hmul : ‖h a‖ ^ 2 * ‖C⁻¹ i k‖ ^ 2 ≤
      Complex.re (star h ⬝ᵥ h) * Complex.re ((Cᴴ * C)⁻¹ i i) :=
    mul_le_mul hx hy (sq_nonneg _) hresRe
  have hprod : Complex.re (star h ⬝ᵥ h) *
      Complex.re ((Cᴴ * C)⁻¹ i i) ≤ 1 := by
    have hresIm : (star h ⬝ᵥ h).im = 0 :=
      (RCLike.nonneg_iff.mp hres).2
    have hdiagIm : ((Cᴴ * C)⁻¹ i i).im = 0 :=
      (RCLike.nonneg_iff.mp hdiag).2
    change Complex.re
      ((star h ⬝ᵥ h) * (Cᴴ * C)⁻¹ i i) ≤ 1 at hswap
    rw [Complex.mul_re, hresIm, hdiagIm] at hswap
    simpa using hswap
  change ‖h a‖ * ‖C⁻¹ i k‖ ≤ 1
  have hxy0 : 0 ≤ ‖h a‖ * ‖C⁻¹ i k‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [hmul.trans hprod]

/-- Rectangular version of the pairwise residual/left-inverse estimate,
which is the quantitative core used in the first RRQR. -/
theorem maximalOrderedColumnSelection_residual_entry_mul_leftInverse_entry_le_one
    {m n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hGram : IsUnit
      (((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
        selectedColumns A (maximalOrderedColumnSelection hrn A)).det))
    (a : Fin m) (j : Fin n) (i : Fin r) (x : Fin m) :
    ‖leastSquaresResidual
        (selectedColumns A (maximalOrderedColumnSelection hrn A))
        (fun y => A y j) a‖ *
      ‖leastSquaresLeftInverse
        (selectedColumns A (maximalOrderedColumnSelection hrn A)) i x‖ ≤ 1 := by
  let C := selectedColumns A (maximalOrderedColumnSelection hrn A)
  let h := leastSquaresResidual C (fun y => A y j)
  have hswap := maximalOrderedColumnSelection_residual_diagonal_product_re_le_one
    hrn A hGram i j
  have hx := norm_entry_sq_le_re_star_dotProduct h a
  have hy := inverseGram_diag_leftInverse_entry_lower_bound C hGram i x
  have hres : 0 ≤ star h ⬝ᵥ h := dotProduct_star_self_nonneg h
  have hdiag : 0 ≤ (Cᴴ * C)⁻¹ i i :=
    (posDef_gram_of_isUnit_det C hGram).inv.diag_pos.le
  have hresRe : 0 ≤ Complex.re (star h ⬝ᵥ h) :=
    (RCLike.nonneg_iff.mp hres).1
  have hdiagRe : 0 ≤ Complex.re ((Cᴴ * C)⁻¹ i i) :=
    (RCLike.nonneg_iff.mp hdiag).1
  have hmul : ‖h a‖ ^ 2 * ‖leastSquaresLeftInverse C i x‖ ^ 2 ≤
      Complex.re (star h ⬝ᵥ h) * Complex.re ((Cᴴ * C)⁻¹ i i) :=
    mul_le_mul hx hy (sq_nonneg _) hresRe
  have hprod : Complex.re (star h ⬝ᵥ h) *
      Complex.re ((Cᴴ * C)⁻¹ i i) ≤ 1 := by
    have hresIm : (star h ⬝ᵥ h).im = 0 :=
      (RCLike.nonneg_iff.mp hres).2
    have hdiagIm : ((Cᴴ * C)⁻¹ i i).im = 0 :=
      (RCLike.nonneg_iff.mp hdiag).2
    change Complex.re
      ((star h ⬝ᵥ h) * (Cᴴ * C)⁻¹ i i) ≤ 1 at hswap
    rw [Complex.mul_re, hresIm, hdiagIm] at hswap
    simpa using hswap
  change ‖h a‖ * ‖leastSquaresLeftInverse C i x‖ ≤ 1
  have hxy0 : 0 ≤ ‖h a‖ * ‖leastSquaresLeftInverse C i x‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [hmul.trans hprod]

/-- Least-squares coefficient matrix against all ambient columns. -/
def maximumVolumeLeastSquaresMatrix {m n r : ℕ} (hrn : r ≤ n)
    (A : Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin r) (Fin n) ℂ :=
  fun i j => leastSquaresCoordinates
    (selectedColumns A (maximalOrderedColumnSelection hrn A))
    (fun a => A a j) i

theorem maximumVolumeLeastSquaresMatrix_eq_leftInverse_mul
    {m n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin m) (Fin n) ℂ) :
    maximumVolumeLeastSquaresMatrix hrn A =
      leastSquaresLeftInverse
        (selectedColumns A (maximalOrderedColumnSelection hrn A)) * A := by
  ext i j
  simp only [maximumVolumeLeastSquaresMatrix, leastSquaresCoordinates,
    leastSquaresLeftInverse]
  rw [Matrix.mulVec_mulVec, Matrix.mul_apply]
  rfl

theorem maximumVolumeLeastSquaresMatrix_mul_columnSelector
    {m n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hGram : IsUnit
      (((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
        selectedColumns A (maximalOrderedColumnSelection hrn A)).det)) :
    maximumVolumeLeastSquaresMatrix hrn A *
      columnSelector (maximalOrderedColumnSelection hrn A) = 1 := by
  rw [maximumVolumeLeastSquaresMatrix_eq_leftInverse_mul,
    Matrix.mul_assoc, mul_columnSelector,
    leastSquaresLeftInverse_mul _ hGram]

theorem maximumVolumeLeastSquaresMatrix_entry_norm_le_one
    {m n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hGram : IsUnit
      (((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
        selectedColumns A (maximalOrderedColumnSelection hrn A)).det))
    (i : Fin r) (j : Fin n) :
    ‖maximumVolumeLeastSquaresMatrix hrn A i j‖ ≤ 1 :=
  maximalOrderedColumnSelection_leastSquares_entry_norm_le_one hrn A hGram i j

theorem norm_maximumVolumeLeastSquaresMatrix_le
    {m n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hGram : IsUnit
      (((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
        selectedColumns A (maximalOrderedColumnSelection hrn A)).det)) :
    ‖maximumVolumeLeastSquaresMatrix hrn A‖ ≤ (r : ℝ) * n := by
  simpa using matrix_l2_opNorm_le_card_mul_card_of_entry_norm_le_one
    (maximumVolumeLeastSquaresMatrix hrn A)
      (maximumVolumeLeastSquaresMatrix_entry_norm_le_one hrn A hGram)

/-- Least-squares residual matrix against all ambient columns. -/
def maximumVolumeResidualMatrix {m n r : ℕ} (hrn : r ≤ n)
    (A : Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  A - selectedColumns A (maximalOrderedColumnSelection hrn A) *
    maximumVolumeLeastSquaresMatrix hrn A

theorem maximumVolume_column_decomposition {m n r : ℕ} (hrn : r ≤ n)
    (A : Matrix (Fin m) (Fin n) ℂ) :
    A = selectedColumns A (maximalOrderedColumnSelection hrn A) *
        maximumVolumeLeastSquaresMatrix hrn A +
      maximumVolumeResidualMatrix hrn A := by
  simp [maximumVolumeResidualMatrix]

theorem maximumVolumeResidualMatrix_col {m n r : ℕ} (hrn : r ≤ n)
    (A : Matrix (Fin m) (Fin n) ℂ) (j : Fin n) :
    (maximumVolumeResidualMatrix hrn A).col j =
      leastSquaresResidual
        (selectedColumns A (maximalOrderedColumnSelection hrn A))
        (fun a => A a j) := by
  ext a
  rfl

theorem maximumVolumeResidualMatrix_mul_columnSelector_eq_zero
    {m n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hGram : IsUnit
      (((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
        selectedColumns A (maximalOrderedColumnSelection hrn A)).det)) :
    maximumVolumeResidualMatrix hrn A *
      columnSelector (maximalOrderedColumnSelection hrn A) = 0 := by
  rw [maximumVolumeResidualMatrix, Matrix.sub_mul, mul_columnSelector,
    Matrix.mul_assoc, maximumVolumeLeastSquaresMatrix_mul_columnSelector
      hrn A hGram, Matrix.mul_one, sub_self]

/-- Coarse but fully explicit Gu--Eisenstat norm product: the first-round
residual norm times the norm of the canonical left inverse is polynomially
bounded. -/
theorem norm_maximumVolumeResidual_mul_norm_leastSquaresLeftInverse_le
    {m n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hGram : IsUnit
      (((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
        selectedColumns A (maximalOrderedColumnSelection hrn A)).det)) :
    ‖maximumVolumeResidualMatrix hrn A‖ *
      ‖leastSquaresLeftInverse
        (selectedColumns A (maximalOrderedColumnSelection hrn A))‖ ≤
      (m * n * r * m : ℕ) := by
  apply matrix_l2_opNorm_mul_le_card_product_of_pairwise_entry
  intro a j i x
  change ‖leastSquaresResidual
      (selectedColumns A (maximalOrderedColumnSelection hrn A))
      (fun y => A y j) a‖ *
    ‖leastSquaresLeftInverse
      (selectedColumns A (maximalOrderedColumnSelection hrn A)) i x‖ ≤ 1
  exact maximalOrderedColumnSelection_residual_entry_mul_leftInverse_entry_le_one
    hrn A hGram a j i x

theorem selectedColumns_conjTranspose_mul_maximumVolumeResidualMatrix
    {m n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin m) (Fin n) ℂ)
    (hGram : IsUnit
      (((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
        selectedColumns A (maximalOrderedColumnSelection hrn A)).det)) :
    (selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *
      maximumVolumeResidualMatrix hrn A = 0 := by
  ext i j
  change ((selectedColumns A (maximalOrderedColumnSelection hrn A))ᴴ *ᵥ
    (maximumVolumeResidualMatrix hrn A).col j) i = 0
  rw [maximumVolumeResidualMatrix_col]
  exact congrFun (leastSquaresResidual_orthogonal
    (selectedColumns A (maximalOrderedColumnSelection hrn A))
      (fun a => A a j) hGram) i

/-! ## Threshold-specialized first RRQR output -/

/-- Internally chosen maximum-volume column coordinates at the threshold. -/
def thresholdColumnSelection {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (tau : ℝ) : Fin (largeSingularValueCount A tau) → Fin n :=
  maximalOrderedColumnSelection (largeSingularValueCount_le A tau) A

def thresholdSelectedColumns {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (tau : ℝ) : Matrix (Fin n) (Fin (largeSingularValueCount A tau)) ℂ :=
  selectedColumns A (thresholdColumnSelection A tau)

def thresholdLeastSquaresMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (tau : ℝ) : Matrix (Fin (largeSingularValueCount A tau)) (Fin n) ℂ :=
  maximumVolumeLeastSquaresMatrix (largeSingularValueCount_le A tau) A

def thresholdResidualMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (tau : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  maximumVolumeResidualMatrix (largeSingularValueCount_le A tau) A

def thresholdColumnSelector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (tau : ℝ) : Matrix (Fin n) (Fin (largeSingularValueCount A tau)) ℂ :=
  columnSelector (thresholdColumnSelection A tau)

theorem thresholdColumnSelection_injective {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    Function.Injective
      (thresholdColumnSelection A tau) := by
  exact selectedColumns_selection_injective_of_gram_isUnit A _
    (thresholdMaximalColumnSelection_gram_isUnit A tau htau)

theorem mul_thresholdColumnSelector {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) :
    A * thresholdColumnSelector A tau = thresholdSelectedColumns A tau :=
  mul_columnSelector A _

theorem norm_thresholdColumnSelector_le_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    ‖thresholdColumnSelector A tau‖ ≤ 1 :=
  norm_columnSelector_le_one _ (thresholdColumnSelection_injective A tau htau)

theorem thresholdLeastSquaresMatrix_mul_selector {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    thresholdLeastSquaresMatrix A tau * thresholdColumnSelector A tau = 1 :=
  maximumVolumeLeastSquaresMatrix_mul_columnSelector
    (largeSingularValueCount_le A tau) A
      (thresholdMaximalColumnSelection_gram_isUnit A tau htau)

theorem thresholdResidualMatrix_mul_selector_eq_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    thresholdResidualMatrix A tau * thresholdColumnSelector A tau = 0 :=
  maximumVolumeResidualMatrix_mul_columnSelector_eq_zero
    (largeSingularValueCount_le A tau) A
      (thresholdMaximalColumnSelection_gram_isUnit A tau htau)

theorem threshold_column_decomposition {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) :
    A = thresholdSelectedColumns A tau * thresholdLeastSquaresMatrix A tau +
      thresholdResidualMatrix A tau :=
  maximumVolume_column_decomposition (largeSingularValueCount_le A tau) A

/-- Empty first-round pivot convention: if no singular value is above the
threshold, the selected product is the zero matrix and the residual is `A`. -/
theorem thresholdResidualMatrix_eq_self_of_count_eq_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ)
    (hcount : largeSingularValueCount A tau = 0) :
    thresholdResidualMatrix A tau = A := by
  have hprod : thresholdSelectedColumns A tau *
      thresholdLeastSquaresMatrix A tau = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro k _hk
    have hk := k.isLt
    omega
  have hdec := threshold_column_decomposition A tau
  rw [hprod, zero_add] at hdec
  exact hdec.symm

/-- Full first-round pivot convention: if every coordinate singular value is
above the threshold, the coordinate selector is square and the residual
vanishes. -/
theorem thresholdResidualMatrix_eq_zero_of_count_eq_dim {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (hcount : largeSingularValueCount A tau = n) :
    thresholdResidualMatrix A tau = 0 := by
  let S := thresholdColumnSelector A tau
  let H := thresholdResidualMatrix A tau
  have hinj := thresholdColumnSelection_injective A tau htau
  have hRS : Sᴴ * S = 1 :=
    columnSelector_conjTranspose_mul_self _ hinj
  have hSR : S * Sᴴ = 1 := by
    exact (Matrix.mul_eq_one_comm_of_card_eq
      (Fin (largeSingularValueCount A tau)) (Fin n) ℂ
      (by simpa using hcount)).mp hRS
  have hHS : H * S = 0 :=
    thresholdResidualMatrix_mul_selector_eq_zero A tau htau
  calc
    thresholdResidualMatrix A tau = H * 1 := by simp [H]
    _ = H * (S * Sᴴ) := by rw [hSR]
    _ = (H * S) * Sᴴ := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hHS]; simp only [Matrix.zero_mul]

theorem norm_thresholdLeastSquaresMatrix_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    ‖thresholdLeastSquaresMatrix A tau‖ ≤
      (largeSingularValueCount A tau : ℝ) * n := by
  exact norm_maximumVolumeLeastSquaresMatrix_le
    (largeSingularValueCount_le A tau) A
      (thresholdMaximalColumnSelection_gram_isUnit A tau htau)

theorem thresholdSelectedColumns_conjTranspose_mul_residual {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    (thresholdSelectedColumns A tau)ᴴ * thresholdResidualMatrix A tau = 0 :=
  selectedColumns_conjTranspose_mul_maximumVolumeResidualMatrix
    (largeSingularValueCount_le A tau) A
      (thresholdMaximalColumnSelection_gram_isUnit A tau htau)

theorem threshold_apply_decomposition {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ)
    (z : EuclideanSpace ℂ (Fin n)) :
    Matrix.toEuclideanLin A z =
      Matrix.toEuclideanLin (thresholdSelectedColumns A tau)
          (Matrix.toEuclideanLin (thresholdLeastSquaresMatrix A tau) z) +
        Matrix.toEuclideanLin (thresholdResidualMatrix A tau) z := by
  calc
    Matrix.toEuclideanLin A z =
        Matrix.toEuclideanLin
          (thresholdSelectedColumns A tau * thresholdLeastSquaresMatrix A tau +
            thresholdResidualMatrix A tau) z := by
      exact congrArg (fun M => Matrix.toEuclideanLin M z)
        (threshold_column_decomposition A tau)
    _ = _ := by simp

theorem norm_thresholdSelected_part_le_norm_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (z : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanLin (thresholdSelectedColumns A tau)
        (Matrix.toEuclideanLin (thresholdLeastSquaresMatrix A tau) z)‖ ≤
      ‖Matrix.toEuclideanLin A z‖ := by
  rw [threshold_apply_decomposition A tau z]
  apply norm_left_le_norm_add_of_inner_eq_zero
  apply inner_matrix_mulVec_eq_zero_of_conjTranspose_mul_eq_zero
  exact thresholdSelectedColumns_conjTranspose_mul_residual A tau htau

theorem norm_thresholdResidual_apply_le_norm_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (z : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanLin (thresholdResidualMatrix A tau) z‖ ≤
      ‖Matrix.toEuclideanLin A z‖ := by
  rw [threshold_apply_decomposition A tau z]
  apply norm_right_le_norm_add_of_inner_eq_zero
  apply inner_matrix_mulVec_eq_zero_of_conjTranspose_mul_eq_zero
  exact thresholdSelectedColumns_conjTranspose_mul_residual A tau htau

/-- A top residual direction can be moved into the coordinate complement
of the selected columns at a loss of at most two. -/
theorem exists_threshold_complement_vector {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (hr : 0 < largeSingularValueCount A tau)
    (hH : 0 < ‖thresholdResidualMatrix A tau‖) :
    ∃ x : EuclideanSpace ℂ (Fin n), x ≠ 0 ∧
      Matrix.toEuclideanLin (thresholdColumnSelector A tau)ᴴ x = 0 ∧
      ‖thresholdResidualMatrix A tau‖ * ‖x‖ ≤
        2 * ‖Matrix.toEuclideanLin (thresholdResidualMatrix A tau) x‖ := by
  have hn : 0 < n := lt_of_lt_of_le hr (largeSingularValueCount_le A tau)
  obtain ⟨v, hv0, hv⟩ :=
    exists_vector_l2OpNorm_mul_norm_le_apply
      (thresholdResidualMatrix A tau) hn
  let S := thresholdColumnSelector A tau
  let H := thresholdResidualMatrix A tau
  let x : EuclideanSpace ℂ (Fin n) :=
    v - Matrix.toEuclideanLin S (Matrix.toEuclideanLin Sᴴ v)
  have hinj := thresholdColumnSelection_injective A tau htau
  have hRS : Sᴴ * S = 1 := by
    exact columnSelector_conjTranspose_mul_self _ hinj
  have hRx : Matrix.toEuclideanLin Sᴴ x = 0 := by
    dsimp [x]
    rw [map_sub, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hRS,
      Matrix.toLpLin_one, LinearMap.id_apply, sub_self]
  have hHx : Matrix.toEuclideanLin H x = Matrix.toEuclideanLin H v := by
    dsimp [x]
    rw [map_sub]
    have hHS : H * S = 0 := by
      exact thresholdResidualMatrix_mul_selector_eq_zero A tau htau
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hHS]
    simp
  have hRv : ‖Matrix.toEuclideanLin Sᴴ v‖ ≤ ‖v‖ := by
    calc
      ‖Matrix.toEuclideanLin Sᴴ v‖ ≤ ‖Sᴴ‖ * ‖v‖ := by
        exact (Matrix.toEuclideanLin Sᴴ).toContinuousLinearMap.le_opNorm v
      _ = ‖S‖ * ‖v‖ := by rw [Matrix.l2_opNorm_conjTranspose]
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right
        (by simpa [S] using norm_thresholdColumnSelector_le_one A tau htau)
        (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  have hS_norm : ‖Matrix.toEuclideanLin S
      (Matrix.toEuclideanLin Sᴴ v)‖ = ‖Matrix.toEuclideanLin Sᴴ v‖ := by
    simpa only [S, thresholdColumnSelector] using columnSelector_mulVec_norm _ hinj
      (Matrix.toEuclideanLin Sᴴ v)
  have hxnorm : ‖x‖ ≤ 2 * ‖v‖ := by
    calc
      ‖x‖ ≤ ‖v‖ + ‖Matrix.toEuclideanLin S
          (Matrix.toEuclideanLin Sᴴ v)‖ := norm_sub_le _ _
      _ = ‖v‖ + ‖Matrix.toEuclideanLin Sᴴ v‖ := by rw [hS_norm]
      _ ≤ ‖v‖ + ‖v‖ := add_le_add (le_refl _) hRv
      _ = 2 * ‖v‖ := by ring
  have hx0 : x ≠ 0 := by
    intro hxzero
    have hHvzero : Matrix.toEuclideanLin H v = 0 := by
      rw [← hHx, hxzero, map_zero]
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    have : 0 < ‖H‖ * ‖v‖ := mul_pos hH hvnorm
    have hv' : ‖H‖ * ‖v‖ ≤ ‖Matrix.toEuclideanLin H v‖ := by
      simpa [H] using hv
    rw [hHvzero, norm_zero] at hv'
    linarith
  refine ⟨x, hx0, ?_, ?_⟩
  · simpa [S] using hRx
  · have hmul := mul_le_mul_of_nonneg_left hxnorm (norm_nonneg H)
    have hv' : ‖H‖ * ‖v‖ ≤ ‖Matrix.toEuclideanLin H v‖ := by
      simpa [H] using hv
    calc
      ‖thresholdResidualMatrix A tau‖ * ‖x‖ = ‖H‖ * ‖x‖ := by rfl
      _ ≤ ‖H‖ * (2 * ‖v‖) := hmul
      _ = 2 * (‖H‖ * ‖v‖) := by ring
      _ ≤ 2 * ‖Matrix.toEuclideanLin H v‖ :=
        mul_le_mul_of_nonneg_left hv' (by norm_num)
      _ = 2 * ‖Matrix.toEuclideanLin (thresholdResidualMatrix A tau) x‖ := by
        rw [hHx]

/-- First-round Gu--Eisenstat bridge in min--max form.  The constant is
deliberately coarse but explicit and polynomial. -/
theorem norm_thresholdResidual_le_scale_mul_nextSingularValue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (hr : 0 < largeSingularValueCount A tau)
    (hrn : largeSingularValueCount A tau < n) :
    ‖thresholdResidualMatrix A tau‖ ≤
      (((n * n * largeSingularValueCount A tau * n : ℕ) : ℝ) +
        2 * (‖thresholdLeastSquaresMatrix A tau‖ + 1)) *
      (Matrix.toEuclideanLin A).singularValues
        (largeSingularValueCount A tau) := by
  let r := largeSingularValueCount A tau
  let S := thresholdColumnSelector A tau
  let C := thresholdSelectedColumns A tau
  let T := thresholdLeastSquaresMatrix A tau
  let H := thresholdResidualMatrix A tau
  let L := leastSquaresLeftInverse C
  let P : ℝ := (n * n * r * n : ℕ)
  let scale : ℝ := P + 2 * (‖T‖ + 1)
  by_cases hHzero : ‖H‖ = 0
  · rw [show ‖thresholdResidualMatrix A tau‖ = 0 by simpa [H] using hHzero]
    exact mul_nonneg (by positivity)
      ((Matrix.toEuclideanLin A).singularValues_nonneg _)
  have hHpos : 0 < ‖H‖ := lt_of_le_of_ne (norm_nonneg H) (Ne.symm hHzero)
  obtain ⟨x, hx0, hRx, hxres⟩ :=
    exists_threshold_complement_vector A tau htau hr (by simpa [H] using hHpos)
  have hinj := thresholdColumnSelection_injective A tau htau
  have hRS : Sᴴ * S = 1 := by
    exact columnSelector_conjTranspose_mul_self _ hinj
  have hTS : T * S = 1 := by
    exact thresholdLeastSquaresMatrix_mul_selector A tau htau
  have hHS : H * S = 0 := by
    exact thresholdResidualMatrix_mul_selector_eq_zero A tau htau
  have hGram := thresholdMaximalColumnSelection_gram_isUnit A tau htau
  have hLC : L * C = 1 := by
    exact leastSquaresLeftInverse_mul C hGram
  have hHL : ‖H‖ * ‖L‖ ≤ P := by
    dsimp [H, L, C, P, r]
    exact norm_maximumVolumeResidual_mul_norm_leastSquaresLeftInverse_le
      (largeSingularValueCount_le A tau) A hGram
  let Φ := selectorSpanL2Map S x
  let i : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin n))) :=
    ⟨r, by simpa [r] using hrn⟩
  have hscale : 0 < scale := by
    dsimp [scale, P]
    positivity
  have hmain := scaled_le_mul_singularValue_of_injective_parametrization
    (D := WithLp 2
      (EuclideanSpace ℂ (Fin (largeSingularValueCount A tau)) × ℂ))
    (Matrix.toEuclideanLin A) i Φ ‖H‖ scale
  apply hmain
  · calc
      Module.finrank ℂ (WithLp 2
          (EuclideanSpace ℂ (Fin (largeSingularValueCount A tau)) × ℂ)) =
          Module.finrank ℂ
            (EuclideanSpace ℂ (Fin (largeSingularValueCount A tau)) × ℂ) :=
        (WithLp.linearEquiv 2 ℂ
          (EuclideanSpace ℂ (Fin (largeSingularValueCount A tau)) × ℂ)).finrank_eq
      _ = largeSingularValueCount A tau + 1 := by
        rw [Module.finrank_prod]
        simp
  · apply selectorSpanL2Map_injective S hRS x
    · simpa [S] using hRx
    · exact hx0
  · exact hscale
  · intro z
    have hHphi : Matrix.toEuclideanLin H (Φ z) =
        z.ofLp.2 • Matrix.toEuclideanLin H x := by
      change Matrix.toEuclideanLin H
          (Matrix.toEuclideanLin S z.ofLp.1 + z.ofLp.2 • x) = _
      rw [map_add, map_smul, ← LinearMap.comp_apply,
        ← Matrix.toLpLin_mul_same, hHS]
      simp
    have hTphi : Matrix.toEuclideanLin T (Φ z) =
        z.ofLp.1 + z.ofLp.2 • Matrix.toEuclideanLin T x := by
      change Matrix.toEuclideanLin T
          (Matrix.toEuclideanLin S z.ofLp.1 + z.ofLp.2 • x) = _
      rw [map_add, map_smul, ← LinearMap.comp_apply,
        ← Matrix.toLpLin_mul_same, hTS, Matrix.toLpLin_one,
        LinearMap.id_apply]
    have hCpart : ‖Matrix.toEuclideanLin C
        (Matrix.toEuclideanLin T (Φ z))‖ ≤
        ‖Matrix.toEuclideanLin A (Φ z)‖ := by
      simpa [C, T] using norm_thresholdSelected_part_le_norm_apply
        A tau htau (Φ z)
    have hHpart : ‖Matrix.toEuclideanLin H (Φ z)‖ ≤
        ‖Matrix.toEuclideanLin A (Φ z)‖ := by
      simpa [H] using norm_thresholdResidual_apply_le_norm_apply
        A tau htau (Φ z)
    have hSiso : ‖Matrix.toEuclideanLin S z.ofLp.1‖ = ‖z.ofLp.1‖ := by
      simpa only [S, thresholdColumnSelector] using
        columnSelector_mulVec_norm _ hinj z.ofLp.1
    have hphi : ‖Φ z‖ ≤ ‖z.ofLp.1‖ + ‖z.ofLp.2‖ * ‖x‖ := by
      change ‖Matrix.toEuclideanLin S z.ofLp.1 + z.ofLp.2 • x‖ ≤ _
      calc
        ‖Matrix.toEuclideanLin S z.ofLp.1 + z.ofLp.2 • x‖ ≤
            ‖Matrix.toEuclideanLin S z.ofLp.1‖ + ‖z.ofLp.2 • x‖ := norm_add_le _ _
        _ = ‖z.ofLp.1‖ + ‖z.ofLp.2‖ * ‖x‖ := by rw [hSiso, norm_smul]
    have hTu : ‖Matrix.toEuclideanLin T (Φ z)‖ ≤
        ‖L‖ * ‖Matrix.toEuclideanLin A (Φ z)‖ := by
      exact (norm_le_l2OpNorm_mul_norm_apply_of_leftInverse L C hLC
        (Matrix.toEuclideanLin T (Φ z))).trans
          (mul_le_mul_of_nonneg_left hCpart (norm_nonneg L))
    have hTx : ‖Matrix.toEuclideanLin T x‖ ≤ ‖T‖ * ‖x‖ :=
      (Matrix.toEuclideanLin T).toContinuousLinearMap.le_opNorm x
    have hy : ‖z.ofLp.1‖ ≤
        ‖L‖ * ‖Matrix.toEuclideanLin A (Φ z)‖ +
          ‖z.ofLp.2‖ * (‖T‖ * ‖x‖) := by
      have hyEq : z.ofLp.1 = Matrix.toEuclideanLin T (Φ z) -
          z.ofLp.2 • Matrix.toEuclideanLin T x := by
        rw [hTphi]
        abel
      rw [hyEq]
      exact (norm_sub_le _ _).trans (add_le_add hTu
        (by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left hTx (norm_nonneg z.ofLp.2)))
    have hphi' : ‖Φ z‖ ≤
        ‖L‖ * ‖Matrix.toEuclideanLin A (Φ z)‖ +
          ‖z.ofLp.2‖ * (‖T‖ + 1) * ‖x‖ := by
      calc
        ‖Φ z‖ ≤ ‖z.ofLp.1‖ + ‖z.ofLp.2‖ * ‖x‖ := hphi
        _ ≤ (‖L‖ * ‖Matrix.toEuclideanLin A (Φ z)‖ +
              ‖z.ofLp.2‖ * (‖T‖ * ‖x‖)) + ‖z.ofLp.2‖ * ‖x‖ :=
          add_le_add hy (le_refl _)
        _ = ‖L‖ * ‖Matrix.toEuclideanLin A (Φ z)‖ +
              ‖z.ofLp.2‖ * (‖T‖ + 1) * ‖x‖ := by ring
    have htHx : ‖z.ofLp.2‖ * ‖Matrix.toEuclideanLin H x‖ =
        ‖Matrix.toEuclideanLin H (Φ z)‖ := by
      rw [hHphi, norm_smul]
    have hxres' : ‖H‖ * ‖x‖ ≤
        2 * ‖Matrix.toEuclideanLin H x‖ := by
      simpa [H] using hxres
    have hfirst : ‖H‖ *
        (‖L‖ * ‖Matrix.toEuclideanLin A (Φ z)‖) ≤
        P * ‖Matrix.toEuclideanLin A (Φ z)‖ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hHL (norm_nonneg _)
    have hsecond : ‖H‖ * (‖z.ofLp.2‖ * (‖T‖ + 1) * ‖x‖) ≤
        2 * (‖T‖ + 1) * ‖Matrix.toEuclideanLin A (Φ z)‖ := by
      calc
        ‖H‖ * (‖z.ofLp.2‖ * (‖T‖ + 1) * ‖x‖) =
            (‖z.ofLp.2‖ * (‖T‖ + 1)) * (‖H‖ * ‖x‖) := by ring
        _ ≤ (‖z.ofLp.2‖ * (‖T‖ + 1)) *
            (2 * ‖Matrix.toEuclideanLin H x‖) :=
          mul_le_mul_of_nonneg_left hxres' (by positivity)
        _ = 2 * (‖T‖ + 1) *
            ‖Matrix.toEuclideanLin H (Φ z)‖ := by rw [← htHx]; ring
        _ ≤ 2 * (‖T‖ + 1) *
            ‖Matrix.toEuclideanLin A (Φ z)‖ :=
          mul_le_mul_of_nonneg_left hHpart (by positivity)
    calc
      ‖H‖ * ‖Φ z‖ ≤ ‖H‖ *
          (‖L‖ * ‖Matrix.toEuclideanLin A (Φ z)‖ +
            ‖z.ofLp.2‖ * (‖T‖ + 1) * ‖x‖) :=
        mul_le_mul_of_nonneg_left hphi' (norm_nonneg H)
      _ = ‖H‖ * (‖L‖ * ‖Matrix.toEuclideanLin A (Φ z)‖) +
          ‖H‖ * (‖z.ofLp.2‖ * (‖T‖ + 1) * ‖x‖) := by ring
      _ ≤ P * ‖Matrix.toEuclideanLin A (Φ z)‖ +
          2 * (‖T‖ + 1) * ‖Matrix.toEuclideanLin A (Φ z)‖ :=
        add_le_add hfirst hsecond
      _ = scale * ‖Matrix.toEuclideanLin A (Φ z)‖ := by
        dsimp [scale]
        ring

/-- Explicit polynomial produced by the two maximum-volume estimates in the
first RRQR round. -/
def rrqrResidualScale (n r : ℕ) : ℝ :=
  ((n * n * r * n : ℕ) : ℝ) + 2 * (((r * n : ℕ) : ℝ) + 1)

theorem rrqrResidualScale_nonneg (n r : ℕ) :
    0 ≤ rrqrResidualScale n r := by
  dsimp [rrqrResidualScale]
  positivity

/-- Uniform first-round residual estimate, including the empty and full
pivot conventions. -/
theorem norm_thresholdResidual_le_rrqrResidualScale_mul_tau {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (hn : 0 < n) :
    ‖thresholdResidualMatrix A tau‖ ≤
      rrqrResidualScale n (largeSingularValueCount A tau) * tau := by
  let r := largeSingularValueCount A tau
  by_cases hrzero : r = 0
  · have hself := thresholdResidualMatrix_eq_self_of_count_eq_zero A tau
      (by simpa [r] using hrzero)
    rw [hself]
    have hfirst := rrqr_matrix_l2OpNorm_le_firstSingularValue A hn
    have hnext := singularValue_count_le A tau (by
      have : largeSingularValueCount A tau = 0 := by simpa [r] using hrzero
      omega)
    calc
      ‖A‖ ≤ (Matrix.toEuclideanLin A).singularValues 0 := hfirst
      _ = (Matrix.toEuclideanLin A).singularValues
          (largeSingularValueCount A tau) := by
        rw [show largeSingularValueCount A tau = 0 by simpa [r] using hrzero]
      _ ≤ tau := hnext
      _ ≤ rrqrResidualScale n (largeSingularValueCount A tau) * tau := by
        rw [show largeSingularValueCount A tau = 0 by simpa [r] using hrzero]
        simp [rrqrResidualScale]
        linarith
  by_cases hrfull : r = n
  · rw [thresholdResidualMatrix_eq_zero_of_count_eq_dim A tau htau
      (by simpa [r] using hrfull)]
    simp only [norm_zero]
    exact mul_nonneg
      (rrqrResidualScale_nonneg n (largeSingularValueCount A tau)) htau
  have hrpos : 0 < largeSingularValueCount A tau := by
    dsimp [r] at hrzero
    exact Nat.pos_of_ne_zero hrzero
  have hrlt : largeSingularValueCount A tau < n := by
    have hrle := largeSingularValueCount_le A tau
    dsimp [r] at hrfull
    omega
  have hbridge := norm_thresholdResidual_le_scale_mul_nextSingularValue
    A tau htau hrpos hrlt
  have hT := norm_thresholdLeastSquaresMatrix_le A tau htau
  have hscale :
      (((n * n * largeSingularValueCount A tau * n : ℕ) : ℝ) +
          2 * (‖thresholdLeastSquaresMatrix A tau‖ + 1)) ≤
        rrqrResidualScale n (largeSingularValueCount A tau) := by
    dsimp [rrqrResidualScale]
    norm_num [Nat.cast_mul] at hT ⊢
    linarith
  have hnext := singularValue_count_le A tau hrlt
  calc
    ‖thresholdResidualMatrix A tau‖ ≤
        (((n * n * largeSingularValueCount A tau * n : ℕ) : ℝ) +
          2 * (‖thresholdLeastSquaresMatrix A tau‖ + 1)) *
        (Matrix.toEuclideanLin A).singularValues
          (largeSingularValueCount A tau) := hbridge
    _ ≤ rrqrResidualScale n (largeSingularValueCount A tau) *
        (Matrix.toEuclideanLin A).singularValues
          (largeSingularValueCount A tau) :=
      mul_le_mul_of_nonneg_right hscale
        ((Matrix.toEuclideanLin A).singularValues_nonneg _)
    _ ≤ rrqrResidualScale n (largeSingularValueCount A tau) * tau :=
      mul_le_mul_of_nonneg_left hnext
        (rrqrResidualScale_nonneg n (largeSingularValueCount A tau))

/-- First-round singular-value comparison before replacing the actual
least-squares norm by its entrywise polynomial bound. -/
theorem singularValue_le_firstRoundScale_mul_thresholdSelectedColumns
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (j : Fin (largeSingularValueCount A tau)) :
    (Matrix.toEuclideanLin A).singularValues j ≤
      (‖thresholdLeastSquaresMatrix A tau‖ +
        ((n * n * largeSingularValueCount A tau * n : ℕ) : ℝ)) *
      (Matrix.toEuclideanLin
        (thresholdSelectedColumns A tau)).singularValues j := by
  let r := largeSingularValueCount A tau
  let C := thresholdSelectedColumns A tau
  let T := thresholdLeastSquaresMatrix A tau
  let H := thresholdResidualMatrix A tau
  let L := leastSquaresLeftInverse C
  let P : ℝ := ((n * n * r * n : ℕ) : ℝ)
  let iA : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin n))) :=
    ⟨j, by
      have hrn := largeSingularValueCount_le A tau
      simpa using lt_of_lt_of_le j.isLt hrn⟩
  let iC : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ (Fin (largeSingularValueCount A tau)))) :=
    ⟨j, by simpa using j.isLt⟩
  have hGram := thresholdMaximalColumnSelection_gram_isUnit A tau htau
  have hLC : L * C = 1 := leastSquaresLeftInverse_mul C hGram
  have hHL : ‖H‖ * ‖L‖ ≤ P := by
    dsimp [H, L, C, P, r]
    exact norm_maximumVolumeResidual_mul_norm_leastSquaresLeftInverse_le
      (largeSingularValueCount_le A tau) A hGram
  have hone : 1 ≤ ‖L‖ *
      (Matrix.toEuclideanLin C).singularValues iC := by
    dsimp [L, iC]
    exact one_le_norm_leastSquaresLeftInverse_mul_singularValue C hGram j
  have hH : ‖H‖ ≤ P *
      (Matrix.toEuclideanLin C).singularValues iC := by
    calc
      ‖H‖ = ‖H‖ * 1 := by ring
      _ ≤ ‖H‖ * (‖L‖ *
          (Matrix.toEuclideanLin C).singularValues iC) :=
        mul_le_mul_of_nonneg_left hone (norm_nonneg H)
      _ = (‖H‖ * ‖L‖) *
          (Matrix.toEuclideanLin C).singularValues iC := by ring
      _ ≤ P * (Matrix.toEuclideanLin C).singularValues iC :=
        mul_le_mul_of_nonneg_right hHL
          ((Matrix.toEuclideanLin C).singularValues_nonneg iC)
  let W := (singularSpectralTail (Matrix.toEuclideanLin C) iC).comap
    (Matrix.toEuclideanLin T)
  apply singularValue_le_of_submodule_bound_of_le_finrank
    (Matrix.toEuclideanLin A) iA W
    ((‖T‖ + P) * (Matrix.toEuclideanLin C).singularValues iC)
  · have hpre := finrank_tsub_quotient_le_finrank_comap
      (Matrix.toEuclideanLin T)
      (singularSpectralTail (Matrix.toEuclideanLin C) iC)
    have hquot := (singularSpectralTail
      (Matrix.toEuclideanLin C) iC).finrank_quotient_add_finrank
    rw [finrank_singularSpectralTail] at hquot
    have hquot_eq : Module.finrank ℂ
        (EuclideanSpace ℂ (Fin (largeSingularValueCount A tau)) ⧸
          singularSpectralTail (Matrix.toEuclideanLin C) iC) = j := by
      dsimp [iC] at hquot ⊢
      simp only [finrank_euclideanSpace_fin] at hquot
      omega
    rw [hquot_eq] at hpre
    simpa [iA, W] using hpre
  · intro z hz
    have hzTail : Matrix.toEuclideanLin T z ∈
        singularSpectralTail (Matrix.toEuclideanLin C) iC := hz
    have hCz : ‖Matrix.toEuclideanLin C
        (Matrix.toEuclideanLin T z)‖ ≤
        (Matrix.toEuclideanLin C).singularValues iC * (‖T‖ * ‖z‖) := by
      calc
        ‖Matrix.toEuclideanLin C (Matrix.toEuclideanLin T z)‖ ≤
            (Matrix.toEuclideanLin C).singularValues iC *
              ‖Matrix.toEuclideanLin T z‖ :=
          norm_apply_le_singularValue_mul_norm_of_mem_singularSpectralTail
            (Matrix.toEuclideanLin C) iC hzTail
        _ ≤ (Matrix.toEuclideanLin C).singularValues iC * (‖T‖ * ‖z‖) :=
          mul_le_mul_of_nonneg_left
            (by
              simpa [Matrix.l2_opNorm_def] using
                (Matrix.toEuclideanLin T).toContinuousLinearMap.le_opNorm z)
            ((Matrix.toEuclideanLin C).singularValues_nonneg iC)
    have hHz : ‖Matrix.toEuclideanLin H z‖ ≤
        (P * (Matrix.toEuclideanLin C).singularValues iC) * ‖z‖ := by
      calc
        ‖Matrix.toEuclideanLin H z‖ ≤ ‖H‖ * ‖z‖ := by
          simpa [Matrix.l2_opNorm_def] using
            (Matrix.toEuclideanLin H).toContinuousLinearMap.le_opNorm z
        _ ≤ (P * (Matrix.toEuclideanLin C).singularValues iC) * ‖z‖ :=
          mul_le_mul_of_nonneg_right hH (norm_nonneg z)
    have hdec := threshold_apply_decomposition A tau z
    change Matrix.toEuclideanLin A z =
      Matrix.toEuclideanLin C (Matrix.toEuclideanLin T z) +
        Matrix.toEuclideanLin H z at hdec
    rw [hdec]
    calc
      ‖Matrix.toEuclideanLin C (Matrix.toEuclideanLin T z) +
          Matrix.toEuclideanLin H z‖ ≤
          ‖Matrix.toEuclideanLin C (Matrix.toEuclideanLin T z)‖ +
            ‖Matrix.toEuclideanLin H z‖ := norm_add_le _ _
      _ ≤ (Matrix.toEuclideanLin C).singularValues iC * (‖T‖ * ‖z‖) +
          (P * (Matrix.toEuclideanLin C).singularValues iC) * ‖z‖ :=
        add_le_add hCz hHz
      _ = ((‖T‖ + P) *
          (Matrix.toEuclideanLin C).singularValues iC) * ‖z‖ := by ring

/-- Polynomial first-round singular-value comparison. -/
theorem singularValue_le_firstRoundPoly_mul_thresholdSelectedColumns
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (j : Fin (largeSingularValueCount A tau)) :
    (Matrix.toEuclideanLin A).singularValues j ≤
      ((((largeSingularValueCount A tau * n : ℕ) : ℝ) +
        ((n * n * largeSingularValueCount A tau * n : ℕ) : ℝ))) *
      (Matrix.toEuclideanLin
        (thresholdSelectedColumns A tau)).singularValues j := by
  refine (singularValue_le_firstRoundScale_mul_thresholdSelectedColumns
    A tau htau j).trans ?_
  apply mul_le_mul_of_nonneg_right
  · have hT := norm_thresholdLeastSquaresMatrix_le A tau htau
    norm_num [Nat.cast_mul] at hT ⊢
    linarith
  · exact (Matrix.toEuclideanLin
      (thresholdSelectedColumns A tau)).singularValues_nonneg j

/-! ## Compatible maximum-volume row selection (second RRQR) -/

def thresholdRowSelection {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (tau : ℝ) : Fin (largeSingularValueCount A tau) → Fin n :=
  maximalOrderedColumnSelection (largeSingularValueCount_le A tau)
    (thresholdSelectedColumns A tau)ᴴ

/-- The compatible square pivot obtained by applying the same finite
maximum-volume construction to the adjoint of the already-selected columns. -/
def thresholdPivot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (tau : ℝ) :
    Matrix (Fin (largeSingularValueCount A tau))
      (Fin (largeSingularValueCount A tau)) ℂ :=
  (thresholdSelectedColumns A tau).submatrix (thresholdRowSelection A tau) id

def thresholdSecondSelectedColumns {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) :
    Matrix (Fin (largeSingularValueCount A tau))
      (Fin (largeSingularValueCount A tau)) ℂ :=
  selectedColumns (thresholdSelectedColumns A tau)ᴴ (thresholdRowSelection A tau)

theorem thresholdSecondSelectedColumns_eq_pivot_conjTranspose {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) :
    thresholdSecondSelectedColumns A tau = (thresholdPivot A tau)ᴴ := by
  ext i j
  rfl

theorem thresholdSecondSelectedColumns_gram_isUnit {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    IsUnit (((thresholdSecondSelectedColumns A tau)ᴴ *
      thresholdSecondSelectedColumns A tau).det) := by
  apply maximalOrderedColumnSelection_gram_isUnit_of_le_rank
  have hrank := rank_conjTranspose_eq_width_of_gram_isUnit
    (thresholdSelectedColumns A tau)
      (thresholdMaximalColumnSelection_gram_isUnit A tau htau)
  rw [hrank]

theorem thresholdRowSelection_injective {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    Function.Injective (thresholdRowSelection A tau) := by
  exact selectedColumns_selection_injective_of_gram_isUnit
    (thresholdSelectedColumns A tau)ᴴ (thresholdRowSelection A tau)
      (thresholdSecondSelectedColumns_gram_isUnit A tau htau)

/-- Canonical completion of the threshold column selection to a coordinate
equivalence.  Its left summand is definitionally the selected list. -/
def thresholdColEquiv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (tau : ℝ) (htau : 0 ≤ tau) :
    Fin (largeSingularValueCount A tau) ⊕
      Fin (n - largeSingularValueCount A tau) ≃ Fin n :=
  injectiveSelectionSumEquiv (thresholdColumnSelection A tau)
    (thresholdColumnSelection_injective A tau htau)
    (largeSingularValueCount_le A tau)

/-- Canonical completion of the compatible threshold row selection. -/
def thresholdRowEquiv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (tau : ℝ) (htau : 0 ≤ tau) :
    Fin (largeSingularValueCount A tau) ⊕
      Fin (n - largeSingularValueCount A tau) ≃ Fin n :=
  injectiveSelectionSumEquiv (thresholdRowSelection A tau)
    (thresholdRowSelection_injective A tau htau)
    (largeSingularValueCount_le A tau)

@[simp]
theorem thresholdColEquiv_inl {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (i : Fin (largeSingularValueCount A tau)) :
    thresholdColEquiv A tau htau (Sum.inl i) =
      thresholdColumnSelection A tau i := by
  apply injectiveSelectionSumEquiv_inl

@[simp]
theorem thresholdRowEquiv_inl {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (i : Fin (largeSingularValueCount A tau)) :
    thresholdRowEquiv A tau htau (Sum.inl i) =
      thresholdRowSelection A tau i := by
  apply injectiveSelectionSumEquiv_inl

/-- The compatible pivot is invertible whenever the threshold count is used;
this is derived, not supplied by a caller. -/
theorem thresholdPivot_isUnit_det {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    IsUnit (thresholdPivot A tau).det := by
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  apply (thresholdSecondSelectedColumns_gram_isUnit A tau htau).ne_zero
  rw [thresholdSecondSelectedColumns_eq_pivot_conjTranspose]
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, star_star, hzero,
    star_zero, zero_mul]

def thresholdSecondLeastSquaresMatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) :
    Matrix (Fin (largeSingularValueCount A tau)) (Fin n) ℂ :=
  maximumVolumeLeastSquaresMatrix (largeSingularValueCount_le A tau)
    (thresholdSelectedColumns A tau)ᴴ

def thresholdSecondResidualMatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) :
    Matrix (Fin (largeSingularValueCount A tau)) (Fin n) ℂ :=
  maximumVolumeResidualMatrix (largeSingularValueCount_le A tau)
    (thresholdSelectedColumns A tau)ᴴ

/-- All-row coefficient matrix from the compatible second selection. -/
def thresholdYAll {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (tau : ℝ) : Matrix (Fin n) (Fin (largeSingularValueCount A tau)) ℂ :=
  (thresholdSecondLeastSquaresMatrix A tau)ᴴ

theorem thresholdSecondResidualMatrix_eq_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    thresholdSecondResidualMatrix A tau = 0 := by
  have hGram := thresholdSecondSelectedColumns_gram_isUnit A tau htau
  have horth : (thresholdSecondSelectedColumns A tau)ᴴ *
      thresholdSecondResidualMatrix A tau = 0 := by
    exact selectedColumns_conjTranspose_mul_maximumVolumeResidualMatrix
      (largeSingularValueCount_le A tau) (thresholdSelectedColumns A tau)ᴴ hGram
  have hKH : thresholdPivot A tau * thresholdSecondResidualMatrix A tau = 0 := by
    simpa [thresholdSecondSelectedColumns_eq_pivot_conjTranspose] using horth
  have hK := thresholdPivot_isUnit_det A tau htau
  calc
    thresholdSecondResidualMatrix A tau =
        ((thresholdPivot A tau)⁻¹ * thresholdPivot A tau) *
          thresholdSecondResidualMatrix A tau := by
      rw [Matrix.nonsing_inv_mul _ hK, Matrix.one_mul]
    _ = (thresholdPivot A tau)⁻¹ *
        (thresholdPivot A tau * thresholdSecondResidualMatrix A tau) := by
      rw [Matrix.mul_assoc]
    _ = 0 := by rw [hKH, Matrix.mul_zero]

theorem threshold_selectedColumns_eq_YAll_mul_pivot {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    thresholdSelectedColumns A tau = thresholdYAll A tau * thresholdPivot A tau := by
  have hdecomp := maximumVolume_column_decomposition
    (largeSingularValueCount_le A tau) (thresholdSelectedColumns A tau)ᴴ
  change (thresholdSelectedColumns A tau)ᴴ =
      thresholdSecondSelectedColumns A tau *
        thresholdSecondLeastSquaresMatrix A tau +
      thresholdSecondResidualMatrix A tau at hdecomp
  rw [thresholdSecondResidualMatrix_eq_zero A tau htau, add_zero,
    thresholdSecondSelectedColumns_eq_pivot_conjTranspose] at hdecomp
  have hstar := congrArg Matrix.conjTranspose hdecomp
  simpa [thresholdYAll, Matrix.conjTranspose_mul] using hstar

theorem norm_thresholdYAll_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    ‖thresholdYAll A tau‖ ≤ (largeSingularValueCount A tau : ℝ) * n := by
  rw [thresholdYAll, Matrix.l2_opNorm_conjTranspose]
  apply norm_maximumVolumeLeastSquaresMatrix_le
  exact thresholdSecondSelectedColumns_gram_isUnit A tau htau

/-- The compatible second maximum-volume step already gives the pivot
singular-value comparison, because its residual vanishes identically. -/
theorem thresholdSelectedColumns_singularValue_le_normY_mul_pivot
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (j : Fin (largeSingularValueCount A tau)) :
    (Matrix.toEuclideanLin (thresholdSelectedColumns A tau)).singularValues j ≤
      ‖thresholdYAll A tau‖ *
        (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues j := by
  have h := rrqr_matrix_singularValue_mul_le_l2OpNorm_mul
    (thresholdYAll A tau) (thresholdPivot A tau) j
  rw [← threshold_selectedColumns_eq_YAll_mul_pivot A tau htau] at h
  exact h

theorem thresholdSelectedColumns_singularValue_le_poly_mul_pivot
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (j : Fin (largeSingularValueCount A tau)) :
    (Matrix.toEuclideanLin (thresholdSelectedColumns A tau)).singularValues j ≤
      ((largeSingularValueCount A tau : ℝ) * n) *
        (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues j := by
  exact (thresholdSelectedColumns_singularValue_le_normY_mul_pivot A tau htau j).trans
    (mul_le_mul_of_nonneg_right (norm_thresholdYAll_le A tau htau)
      ((Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues_nonneg j))

/-- Explicit two-round singular-value loss. -/
def rrqrPivotScale (n r : ℕ) : ℝ :=
  ((((r * n : ℕ) : ℝ) + ((n * n * r * n : ℕ) : ℝ))) *
    ((r * n : ℕ) : ℝ)

theorem singularValue_le_rrqrPivotScale_mul_pivot
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (j : Fin (largeSingularValueCount A tau)) :
    (Matrix.toEuclideanLin A).singularValues j ≤
      rrqrPivotScale n (largeSingularValueCount A tau) *
        (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues j := by
  let a : ℝ := (((largeSingularValueCount A tau * n : ℕ) : ℝ) +
    ((n * n * largeSingularValueCount A tau * n : ℕ) : ℝ))
  let b : ℝ := ((largeSingularValueCount A tau : ℝ) * n)
  have hfirst := singularValue_le_firstRoundPoly_mul_thresholdSelectedColumns
    A tau htau j
  have hsecond := thresholdSelectedColumns_singularValue_le_poly_mul_pivot
    A tau htau j
  calc
    (Matrix.toEuclideanLin A).singularValues j ≤
        a * (Matrix.toEuclideanLin
          (thresholdSelectedColumns A tau)).singularValues j := by
      simpa [a] using hfirst
    _ ≤ a * (b *
        (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues j) :=
      mul_le_mul_of_nonneg_left (by simpa [b] using hsecond) (by
        dsimp [a]
        positivity)
    _ = rrqrPivotScale n (largeSingularValueCount A tau) *
        (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues j := by
      dsimp [a, b, rrqrPivotScale]
      norm_num [Nat.cast_mul]
      ring

theorem rrqrPivotScale_pos_of_index {n r : ℕ} (j : Fin r) (hrn : r ≤ n) :
    0 < rrqrPivotScale n r := by
  have hr : 0 < r := Nat.pos_of_ne_zero (by
    intro hrzero
    subst r
    exact Fin.elim0 j)
  have hn : 0 < n := lt_of_lt_of_le hr hrn
  dsimp [rrqrPivotScale]
  positivity

/-- Multiplicative lower-bound form of the pivot comparison. -/
theorem rrqrPivotScale_inv_mul_singularValue_le_pivot
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (j : Fin (largeSingularValueCount A tau)) :
    (rrqrPivotScale n (largeSingularValueCount A tau))⁻¹ *
        (Matrix.toEuclideanLin A).singularValues j ≤
      (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues j := by
  rw [inv_mul_le_iff₀
    (rrqrPivotScale_pos_of_index j (largeSingularValueCount_le A tau))]
  exact singularValue_le_rrqrPivotScale_mul_pivot A tau htau j

/-! ## Exact coordinate skeleton algebra -/

section Skeleton

variable {p q ι : Type*}
variable [Fintype p] [DecidableEq p]
variable [Fintype q] [DecidableEq q]

/-- Upper-left block after independent row and column coordinate
permutations. -/
def pivotBlock (Q : Matrix ι ι ℂ) (rowEquiv colEquiv : p ⊕ q ≃ ι) :
    Matrix p p ℂ :=
  Q.submatrix (fun i => rowEquiv (Sum.inl i))
    (fun j => colEquiv (Sum.inl j))

/-- Upper-right block after the coordinate permutations. -/
def upperRightBlock (Q : Matrix ι ι ℂ) (rowEquiv colEquiv : p ⊕ q ≃ ι) :
    Matrix p q ℂ :=
  Q.submatrix (fun i => rowEquiv (Sum.inl i))
    (fun j => colEquiv (Sum.inr j))

/-- Lower-left block after the coordinate permutations. -/
def lowerLeftBlock (Q : Matrix ι ι ℂ) (rowEquiv colEquiv : p ⊕ q ≃ ι) :
    Matrix q p ℂ :=
  Q.submatrix (fun i => rowEquiv (Sum.inr i))
    (fun j => colEquiv (Sum.inl j))

/-- Lower-right block after the coordinate permutations. -/
def lowerRightBlock (Q : Matrix ι ι ℂ) (rowEquiv colEquiv : p ⊕ q ≃ ι) :
    Matrix q q ℂ :=
  Q.submatrix (fun i => rowEquiv (Sum.inr i))
    (fun j => colEquiv (Sum.inr j))

/-- The matrix after the row and column coordinate permutations. -/
def permutedMatrix (Q : Matrix ι ι ℂ) (rowEquiv colEquiv : p ⊕ q ≃ ι) :
    Matrix (p ⊕ q) (p ⊕ q) ℂ :=
  Q.submatrix rowEquiv colEquiv

/-- Literal four-block decomposition of a coordinate-permuted matrix. -/
theorem permutedMatrix_eq_fromBlocks (Q : Matrix ι ι ℂ)
    (rowEquiv colEquiv : p ⊕ q ≃ ι) :
    permutedMatrix Q rowEquiv colEquiv =
      Matrix.fromBlocks
        (pivotBlock Q rowEquiv colEquiv)
        (upperRightBlock Q rowEquiv colEquiv)
        (lowerLeftBlock Q rowEquiv colEquiv)
        (lowerRightBlock Q rowEquiv colEquiv) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

/-- `X_skel = K_piv⁻¹ Q_{I,Jᶜ}`.  Matrix inversion is mathlib's total
nonsingular inverse; the reconstruction theorems below require
`IsUnit K_piv.det`. -/
def skeletonX (Q : Matrix ι ι ℂ) (rowEquiv colEquiv : p ⊕ q ≃ ι) :
    Matrix p q ℂ :=
  (pivotBlock Q rowEquiv colEquiv)⁻¹ *
    upperRightBlock Q rowEquiv colEquiv

/-- `Y_skel = Q_{Iᶜ,J} K_piv⁻¹`. -/
def skeletonY (Q : Matrix ι ι ℂ) (rowEquiv colEquiv : p ⊕ q ≃ ι) :
    Matrix q p ℂ :=
  lowerLeftBlock Q rowEquiv colEquiv *
    (pivotBlock Q rowEquiv colEquiv)⁻¹

/-- `E₀ = Q_{Iᶜ,Jᶜ} - Y_skel K_piv X_skel`. -/
def skeletonError (Q : Matrix ι ι ℂ) (rowEquiv colEquiv : p ⊕ q ≃ ι) :
    Matrix q q ℂ :=
  lowerRightBlock Q rowEquiv colEquiv -
    skeletonY Q rowEquiv colEquiv *
      pivotBlock Q rowEquiv colEquiv *
        skeletonX Q rowEquiv colEquiv

/-- For a globally maximum-volume pivot, every entry of `X_skel` has
modulus at most one. -/
theorem skeletonX_entry_norm_le_one_of_global_max
    (Q : Matrix ι ι ℂ) (rowEquiv colEquiv : p ⊕ q ≃ ι)
    (hmax : ∀ rows cols : p → ι,
      ‖(Q.submatrix rows cols).det‖ ≤
        ‖(pivotBlock Q rowEquiv colEquiv).det‖)
    (hPivot : IsUnit (pivotBlock Q rowEquiv colEquiv).det)
    (i : p) (j : q) :
    ‖skeletonX Q rowEquiv colEquiv i j‖ ≤ 1 := by
  change ‖((pivotBlock Q rowEquiv colEquiv)⁻¹ *ᵥ
    (fun a => Q (rowEquiv (Sum.inl a)) (colEquiv (Sum.inr j)))) i‖ ≤ 1
  exact inverse_times_external_column_entry_norm_le_one
    Q (fun a => rowEquiv (Sum.inl a)) (fun a => colEquiv (Sum.inl a))
      hmax hPivot i (colEquiv (Sum.inr j))

/-- For a globally maximum-volume pivot, every entry of `Y_skel` has
modulus at most one. -/
theorem skeletonY_entry_norm_le_one_of_global_max
    (Q : Matrix ι ι ℂ) (rowEquiv colEquiv : p ⊕ q ≃ ι)
    (hmax : ∀ rows cols : p → ι,
      ‖(Q.submatrix rows cols).det‖ ≤
        ‖(pivotBlock Q rowEquiv colEquiv).det‖)
    (hPivot : IsUnit (pivotBlock Q rowEquiv colEquiv).det)
    (i : q) (j : p) :
    ‖skeletonY Q rowEquiv colEquiv i j‖ ≤ 1 := by
  change ‖((fun a => Q (rowEquiv (Sum.inr i)) (colEquiv (Sum.inl a))) ᵥ*
    (pivotBlock Q rowEquiv colEquiv)⁻¹) j‖ ≤ 1
  exact external_row_times_inverse_entry_norm_le_one
    Q (fun a => rowEquiv (Sum.inl a)) (fun a => colEquiv (Sum.inl a))
      hmax hPivot j (rowEquiv (Sum.inr i))

/-- Polynomial Euclidean operator-norm bound for `X_skel` obtained from
the maximum-volume determinant swaps. -/
theorem norm_skeletonX_le_card_mul_card_of_global_max
    (Q : Matrix ι ι ℂ) (rowEquiv colEquiv : p ⊕ q ≃ ι)
    (hmax : ∀ rows cols : p → ι,
      ‖(Q.submatrix rows cols).det‖ ≤
        ‖(pivotBlock Q rowEquiv colEquiv).det‖)
    (hPivot : IsUnit (pivotBlock Q rowEquiv colEquiv).det) :
    ‖skeletonX Q rowEquiv colEquiv‖ ≤
      (Fintype.card p : ℝ) * Fintype.card q :=
  matrix_l2_opNorm_le_card_mul_card_of_entry_norm_le_one _
    (skeletonX_entry_norm_le_one_of_global_max Q rowEquiv colEquiv hmax hPivot)

/-- Polynomial Euclidean operator-norm bound for `Y_skel` obtained from
the maximum-volume determinant swaps. -/
theorem norm_skeletonY_le_card_mul_card_of_global_max
    (Q : Matrix ι ι ℂ) (rowEquiv colEquiv : p ⊕ q ≃ ι)
    (hmax : ∀ rows cols : p → ι,
      ‖(Q.submatrix rows cols).det‖ ≤
        ‖(pivotBlock Q rowEquiv colEquiv).det‖)
    (hPivot : IsUnit (pivotBlock Q rowEquiv colEquiv).det) :
    ‖skeletonY Q rowEquiv colEquiv‖ ≤
      (Fintype.card q : ℝ) * Fintype.card p :=
  matrix_l2_opNorm_le_card_mul_card_of_entry_norm_le_one _
    (skeletonY_entry_norm_le_one_of_global_max Q rowEquiv colEquiv hmax hPivot)

theorem pivot_mul_skeletonX (Q : Matrix ι ι ℂ)
    (rowEquiv colEquiv : p ⊕ q ≃ ι)
    (hPivot : IsUnit (pivotBlock Q rowEquiv colEquiv).det) :
    pivotBlock Q rowEquiv colEquiv * skeletonX Q rowEquiv colEquiv =
      upperRightBlock Q rowEquiv colEquiv := by
  rw [skeletonX, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hPivot, Matrix.one_mul]

theorem skeletonY_mul_pivot (Q : Matrix ι ι ℂ)
    (rowEquiv colEquiv : p ⊕ q ≃ ι)
    (hPivot : IsUnit (pivotBlock Q rowEquiv colEquiv).det) :
    skeletonY Q rowEquiv colEquiv * pivotBlock Q rowEquiv colEquiv =
      lowerLeftBlock Q rowEquiv colEquiv := by
  rw [skeletonY, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hPivot, Matrix.mul_one]

theorem skeleton_recombine_error (Q : Matrix ι ι ℂ)
    (rowEquiv colEquiv : p ⊕ q ≃ ι) :
    skeletonY Q rowEquiv colEquiv *
        pivotBlock Q rowEquiv colEquiv * skeletonX Q rowEquiv colEquiv +
      skeletonError Q rowEquiv colEquiv =
        lowerRightBlock Q rowEquiv colEquiv := by
  simp [skeletonError]

/-- The exact block identity in `lem:local-rrqr`, with no quantitative RRQR
claim smuggled into the statement. -/
theorem skeleton_block_identity (Q : Matrix ι ι ℂ)
    (rowEquiv colEquiv : p ⊕ q ≃ ι)
    (hPivot : IsUnit (pivotBlock Q rowEquiv colEquiv).det) :
    permutedMatrix Q rowEquiv colEquiv =
      Matrix.fromBlocks
        (pivotBlock Q rowEquiv colEquiv)
        (pivotBlock Q rowEquiv colEquiv * skeletonX Q rowEquiv colEquiv)
        (skeletonY Q rowEquiv colEquiv * pivotBlock Q rowEquiv colEquiv)
        (skeletonY Q rowEquiv colEquiv *
            pivotBlock Q rowEquiv colEquiv * skeletonX Q rowEquiv colEquiv +
          skeletonError Q rowEquiv colEquiv) := by
  rw [permutedMatrix_eq_fromBlocks]
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · rfl
    · change upperRightBlock Q rowEquiv colEquiv i j =
        (pivotBlock Q rowEquiv colEquiv * skeletonX Q rowEquiv colEquiv) i j
      exact (congr_fun₂ (pivot_mul_skeletonX Q rowEquiv colEquiv hPivot) i j).symm
  · rcases j with j | j
    · change lowerLeftBlock Q rowEquiv colEquiv i j =
        (skeletonY Q rowEquiv colEquiv * pivotBlock Q rowEquiv colEquiv) i j
      exact (congr_fun₂ (skeletonY_mul_pivot Q rowEquiv colEquiv hPivot) i j).symm
    · change lowerRightBlock Q rowEquiv colEquiv i j =
        (skeletonY Q rowEquiv colEquiv * pivotBlock Q rowEquiv colEquiv *
          skeletonX Q rowEquiv colEquiv + skeletonError Q rowEquiv colEquiv) i j
      exact (congr_fun₂ (skeleton_recombine_error Q rowEquiv colEquiv) i j).symm

end Skeleton

/-! ## Threshold-specialized skeleton -/

/-- The operator norm of the nonsingular inverse is controlled by the last
singular value.  This is the square endpoint of Courant--Fischer. -/
theorem norm_nonsing_inv_mul_lastSingularValue_le_one {r : ℕ}
    (K : Matrix (Fin r) (Fin r) ℂ) (hK : IsUnit K.det) (hr : 0 < r) :
    ‖K⁻¹‖ * (Matrix.toEuclideanLin K).singularValues (r - 1) ≤ 1 := by
  let i : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin r))) :=
    ⟨r - 1, by simpa using (Nat.sub_lt hr Nat.zero_lt_one)⟩
  have hprod := rrqr_matrix_singularValue_mul_le_l2OpNorm_mul K⁻¹ K
    ⟨r - 1, by omega⟩
  rw [Matrix.nonsing_inv_mul _ hK] at hprod
  have hid : (Matrix.toEuclideanLin
      (1 : Matrix (Fin r) (Fin r) ℂ)).singularValues (r - 1) = 1 := by
    rw [Matrix.toLpLin_one]
    simpa [i] using (singularValues_id_eq_one
      (E := EuclideanSpace ℂ (Fin r)) i)
  rw [hid] at hprod
  have hspos : 0 < (Matrix.toEuclideanLin K).singularValues (r - 1) := by
    rw [(Matrix.toEuclideanLin K).singularValues_pos_iff_ne_zero]
    intro hs0
    rw [hs0, mul_zero] at hprod
    linarith
  have hhead : singularSpectralHead (Matrix.toEuclideanLin K) i = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_singularSpectralHead]
    dsimp [i]
    simp
    omega
  have hinvbound : ‖K⁻¹‖ ≤
      ((Matrix.toEuclideanLin K).singularValues (r - 1))⁻¹ := by
    rw [Matrix.l2_opNorm_def]
    apply (Matrix.toEuclideanLin K⁻¹).toContinuousLinearMap.opNorm_le_bound
      (inv_nonneg.mpr ((Matrix.toEuclideanLin K).singularValues_nonneg _))
    intro y
    have hlower := singularValue_mul_norm_le_norm_apply_of_mem_singularSpectralHead
      (Matrix.toEuclideanLin K) i
      (x := Matrix.toEuclideanLin K⁻¹ y) (by rw [hhead]; exact Submodule.mem_top)
    have hcancel : Matrix.toEuclideanLin K (Matrix.toEuclideanLin K⁻¹ y) = y := by
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
        Matrix.mul_nonsing_inv _ hK, Matrix.toLpLin_one, LinearMap.id_apply]
    rw [hcancel] at hlower
    change ‖Matrix.toEuclideanLin K⁻¹ y‖ ≤
      ((Matrix.toEuclideanLin K).singularValues (r - 1))⁻¹ * ‖y‖
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hspos).2 (by simpa [i, mul_comm] using hlower)
  calc
    ‖K⁻¹‖ * (Matrix.toEuclideanLin K).singularValues (r - 1) ≤
        ((Matrix.toEuclideanLin K).singularValues (r - 1))⁻¹ *
          (Matrix.toEuclideanLin K).singularValues (r - 1) :=
      mul_le_mul_of_nonneg_right hinvbound
        ((Matrix.toEuclideanLin K).singularValues_nonneg _)
    _ = 1 := inv_mul_cancel₀ hspos.ne'

theorem thresholdPivotBlock_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    pivotBlock A (thresholdRowEquiv A tau htau)
        (thresholdColEquiv A tau htau) =
      thresholdPivot A tau := by
  ext i j
  simp [pivotBlock, thresholdPivot, thresholdSelectedColumns,
    selectedColumns]

/-- Caller-ready exact skeleton data obtained solely from `A` and the
threshold; no mask, elimination, or RRQR certificate is an input. -/
def thresholdSkeletonData {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    BlockSkeletonData (Fin (largeSingularValueCount A tau))
      (Fin (n - largeSingularValueCount A tau)) where
  Kpiv := thresholdPivot A tau
  Xskel := skeletonX A (thresholdRowEquiv A tau htau)
    (thresholdColEquiv A tau htau)
  Yskel := skeletonY A (thresholdRowEquiv A tau htau)
    (thresholdColEquiv A tau htau)
  E0 := skeletonError A (thresholdRowEquiv A tau htau)
    (thresholdColEquiv A tau htau)

@[simp]
theorem thresholdSkeletonData_Kpiv {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    (thresholdSkeletonData A tau htau).Kpiv = thresholdPivot A tau := rfl

@[simp]
theorem thresholdSkeletonData_Xskel {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    (thresholdSkeletonData A tau htau).Xskel =
      skeletonX A (thresholdRowEquiv A tau htau)
        (thresholdColEquiv A tau htau) := rfl

@[simp]
theorem thresholdSkeletonData_Yskel {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    (thresholdSkeletonData A tau htau).Yskel =
      skeletonY A (thresholdRowEquiv A tau htau)
        (thresholdColEquiv A tau htau) := rfl

@[simp]
theorem thresholdSkeletonData_E0 {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    (thresholdSkeletonData A tau htau).E0 =
      skeletonError A (thresholdRowEquiv A tau htau)
        (thresholdColEquiv A tau htau) := rfl

theorem thresholdSkeletonData_pivot_isUnit {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    IsUnit (thresholdSkeletonData A tau htau).Kpiv.det :=
  thresholdPivot_isUnit_det A tau htau

/-- Literal CUR/skeleton identity for the internally selected threshold
coordinates. -/
theorem threshold_permutedMatrix_eq_skeletonMatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    permutedMatrix A (thresholdRowEquiv A tau htau)
        (thresholdColEquiv A tau htau) =
      skeletonMatrix (thresholdSkeletonData A tau htau) := by
  have hp : IsUnit
      (pivotBlock A (thresholdRowEquiv A tau htau)
        (thresholdColEquiv A tau htau)).det := by
    rw [thresholdPivotBlock_eq A tau htau]
    exact thresholdPivot_isUnit_det A tau htau
  simpa [skeletonMatrix, thresholdSkeletonData,
    thresholdPivotBlock_eq A tau htau] using
      (skeleton_block_identity A (thresholdRowEquiv A tau htau)
        (thresholdColEquiv A tau htau) hp)

/-- The specialized lower skeleton coefficient is exactly the complement-row
compression of the second-round all-row coefficient matrix. -/
theorem thresholdSkeletonData_Yskel_eq_submatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    (thresholdSkeletonData A tau htau).Yskel =
      (thresholdYAll A tau).submatrix
        (fun i => thresholdRowEquiv A tau htau (Sum.inr i)) id := by
  let Yc := (thresholdYAll A tau).submatrix
    (fun i => thresholdRowEquiv A tau htau (Sum.inr i)) id
  have hrows : lowerLeftBlock A (thresholdRowEquiv A tau htau)
      (thresholdColEquiv A tau htau) = Yc * thresholdPivot A tau := by
    ext i j
    have hC := congr_fun₂
      (threshold_selectedColumns_eq_YAll_mul_pivot A tau htau)
      (thresholdRowEquiv A tau htau (Sum.inr i)) j
    simpa [lowerLeftBlock, Yc, thresholdSelectedColumns,
      selectedColumns, Matrix.mul_apply] using hC
  rw [thresholdSkeletonData_Yskel, skeletonY,
    thresholdPivotBlock_eq A tau htau, hrows, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (thresholdPivot_isUnit_det A tau htau),
    Matrix.mul_one]

theorem norm_thresholdSkeletonData_Yskel_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    ‖(thresholdSkeletonData A tau htau).Yskel‖ ≤
      (largeSingularValueCount A tau : ℝ) * n := by
  rw [thresholdSkeletonData_Yskel_eq_submatrix A tau htau]
  refine (norm_submatrix_rows_le (thresholdYAll A tau)
    (fun i => thresholdRowEquiv A tau htau (Sum.inr i)) ?_).trans
      (norm_thresholdYAll_le A tau htau)
  exact (thresholdRowEquiv A tau htau).injective.comp Sum.inr_injective

/-- First-round coefficient block on the unselected columns. -/
def thresholdRightLeastSquaresBlock {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    Matrix (Fin (largeSingularValueCount A tau))
      (Fin (n - largeSingularValueCount A tau)) ℂ :=
  (thresholdLeastSquaresMatrix A tau).submatrix id
    (fun j => thresholdColEquiv A tau htau (Sum.inr j))

/-- Residual restricted to selected rows and unselected columns. -/
def thresholdResidualTopRightBlock {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    Matrix (Fin (largeSingularValueCount A tau))
      (Fin (n - largeSingularValueCount A tau)) ℂ :=
  (thresholdResidualMatrix A tau).submatrix
    (fun i => thresholdRowEquiv A tau htau (Sum.inl i))
    (fun j => thresholdColEquiv A tau htau (Sum.inr j))

/-- Residual restricted to the two coordinate complements. -/
def thresholdResidualBottomRightBlock {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    Matrix (Fin (n - largeSingularValueCount A tau))
      (Fin (n - largeSingularValueCount A tau)) ℂ :=
  (thresholdResidualMatrix A tau).submatrix
    (fun i => thresholdRowEquiv A tau htau (Sum.inr i))
    (fun j => thresholdColEquiv A tau htau (Sum.inr j))

theorem threshold_upperRight_decomposition {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    upperRightBlock A (thresholdRowEquiv A tau htau)
        (thresholdColEquiv A tau htau) =
      thresholdPivot A tau * thresholdRightLeastSquaresBlock A tau htau +
        thresholdResidualTopRightBlock A tau htau := by
  ext i j
  have h := congr_fun₂ (threshold_column_decomposition A tau)
    (thresholdRowEquiv A tau htau (Sum.inl i))
    (thresholdColEquiv A tau htau (Sum.inr j))
  simpa [upperRightBlock, thresholdPivot, thresholdSelectedColumns,
    selectedColumns, thresholdRightLeastSquaresBlock,
    thresholdResidualTopRightBlock, Matrix.mul_apply] using h

theorem threshold_lowerRight_decomposition {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    lowerRightBlock A (thresholdRowEquiv A tau htau)
        (thresholdColEquiv A tau htau) =
      lowerLeftBlock A (thresholdRowEquiv A tau htau)
          (thresholdColEquiv A tau htau) *
        thresholdRightLeastSquaresBlock A tau htau +
      thresholdResidualBottomRightBlock A tau htau := by
  ext i j
  have h := congr_fun₂ (threshold_column_decomposition A tau)
    (thresholdRowEquiv A tau htau (Sum.inr i))
    (thresholdColEquiv A tau htau (Sum.inr j))
  simpa [lowerRightBlock, lowerLeftBlock, thresholdSelectedColumns,
    selectedColumns, thresholdRightLeastSquaresBlock,
    thresholdResidualBottomRightBlock, Matrix.mul_apply] using h

/-- Exact formula `X = T + K⁻¹ H_I` from the two compatible selections. -/
theorem thresholdSkeletonData_Xskel_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    (thresholdSkeletonData A tau htau).Xskel =
      thresholdRightLeastSquaresBlock A tau htau +
        (thresholdPivot A tau)⁻¹ *
          thresholdResidualTopRightBlock A tau htau := by
  rw [thresholdSkeletonData_Xskel, skeletonX,
    thresholdPivotBlock_eq A tau htau,
    threshold_upperRight_decomposition A tau htau, Matrix.mul_add,
    ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (thresholdPivot_isUnit_det A tau htau),
    Matrix.one_mul]

/-- Exact formula `E₀ = H_{Iᶜ,Jᶜ} - Y H_{I,Jᶜ}`. -/
theorem thresholdSkeletonData_E0_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    (thresholdSkeletonData A tau htau).E0 =
      thresholdResidualBottomRightBlock A tau htau -
        (thresholdSkeletonData A tau htau).Yskel *
          thresholdResidualTopRightBlock A tau htau := by
  have hp : IsUnit
      (pivotBlock A (thresholdRowEquiv A tau htau)
        (thresholdColEquiv A tau htau)).det := by
    rw [thresholdPivotBlock_eq A tau htau]
    exact thresholdPivot_isUnit_det A tau htau
  have hKX := pivot_mul_skeletonX A (thresholdRowEquiv A tau htau)
    (thresholdColEquiv A tau htau) hp
  have hYK := skeletonY_mul_pivot A (thresholdRowEquiv A tau htau)
    (thresholdColEquiv A tau htau) hp
  rw [thresholdSkeletonData_E0, thresholdSkeletonData_Yskel, skeletonError,
    threshold_lowerRight_decomposition A tau htau, ← hYK]
  simp only [Matrix.mul_assoc]
  rw [hKX,
    threshold_upperRight_decomposition A tau htau,
    Matrix.mul_add, thresholdPivotBlock_eq A tau htau]
  noncomm_ring

theorem norm_thresholdRightLeastSquaresBlock_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    ‖thresholdRightLeastSquaresBlock A tau htau‖ ≤
      ‖thresholdLeastSquaresMatrix A tau‖ := by
  exact norm_submatrix_cols_le (thresholdLeastSquaresMatrix A tau)
    (fun j => thresholdColEquiv A tau htau (Sum.inr j))
    ((thresholdColEquiv A tau htau).injective.comp Sum.inr_injective)

theorem norm_thresholdResidualTopRightBlock_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    ‖thresholdResidualTopRightBlock A tau htau‖ ≤
      ‖thresholdResidualMatrix A tau‖ := by
  exact norm_submatrix_le (thresholdResidualMatrix A tau)
    (fun i => thresholdRowEquiv A tau htau (Sum.inl i))
    (fun j => thresholdColEquiv A tau htau (Sum.inr j))
    ((thresholdRowEquiv A tau htau).injective.comp Sum.inl_injective)
    ((thresholdColEquiv A tau htau).injective.comp Sum.inr_injective)

theorem norm_thresholdResidualBottomRightBlock_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau) :
    ‖thresholdResidualBottomRightBlock A tau htau‖ ≤
      ‖thresholdResidualMatrix A tau‖ := by
  exact norm_submatrix_le (thresholdResidualMatrix A tau)
    (fun i => thresholdRowEquiv A tau htau (Sum.inr i))
    (fun j => thresholdColEquiv A tau htau (Sum.inr j))
    ((thresholdRowEquiv A tau htau).injective.comp Sum.inr_injective)
    ((thresholdColEquiv A tau htau).injective.comp Sum.inr_injective)

/-- The potentially ill-conditioned pivot inverse only occurs multiplied by
the first-round residual; the threshold gap cancels it polynomially. -/
theorem norm_thresholdPivot_inv_mul_residual_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (hr : 0 < largeSingularValueCount A tau) :
    ‖(thresholdPivot A tau)⁻¹‖ * ‖thresholdResidualMatrix A tau‖ ≤
      rrqrPivotScale n (largeSingularValueCount A tau) *
        rrqrResidualScale n (largeSingularValueCount A tau) := by
  let r := largeSingularValueCount A tau
  let jlast : Fin r := ⟨r - 1, by omega⟩
  have hn : 0 < n := lt_of_lt_of_le hr (largeSingularValueCount_le A tau)
  have hH := norm_thresholdResidual_le_rrqrResidualScale_mul_tau
    A tau htau hn
  have htauA : tau ≤ (Matrix.toEuclideanLin A).singularValues jlast :=
    (singularValue_pred_count_gt A tau hr).le
  have hAK := singularValue_le_rrqrPivotScale_mul_pivot
    A tau htau jlast
  have hHtoK : ‖thresholdResidualMatrix A tau‖ ≤
      rrqrResidualScale n r *
        (rrqrPivotScale n r *
          (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues
            jlast) := by
    calc
      ‖thresholdResidualMatrix A tau‖ ≤ rrqrResidualScale n r * tau := by
        simpa [r] using hH
      _ ≤ rrqrResidualScale n r *
          (Matrix.toEuclideanLin A).singularValues jlast :=
        mul_le_mul_of_nonneg_left htauA (rrqrResidualScale_nonneg n r)
      _ ≤ rrqrResidualScale n r *
          (rrqrPivotScale n r *
            (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues
              jlast) :=
        mul_le_mul_of_nonneg_left (by simpa [r] using hAK)
          (rrqrResidualScale_nonneg n r)
  have hinv := norm_nonsing_inv_mul_lastSingularValue_le_one
    (thresholdPivot A tau) (thresholdPivot_isUnit_det A tau htau) hr
  have hinv' : ‖(thresholdPivot A tau)⁻¹‖ *
      (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues
        jlast ≤ 1 := by
    simpa [r, jlast] using hinv
  calc
    ‖(thresholdPivot A tau)⁻¹‖ * ‖thresholdResidualMatrix A tau‖ ≤
        ‖(thresholdPivot A tau)⁻¹‖ *
          (rrqrResidualScale n r * (rrqrPivotScale n r *
            (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues
              jlast)) :=
      mul_le_mul_of_nonneg_left hHtoK (norm_nonneg _)
    _ = (rrqrPivotScale n r * rrqrResidualScale n r) *
        (‖(thresholdPivot A tau)⁻¹‖ *
          (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues
            jlast) := by ring
    _ ≤ (rrqrPivotScale n r * rrqrResidualScale n r) * 1 :=
      mul_le_mul_of_nonneg_left hinv'
        (mul_nonneg
          (rrqrPivotScale_pos_of_index jlast
            (largeSingularValueCount_le A tau)).le
          (rrqrResidualScale_nonneg n r))
    _ = rrqrPivotScale n r * rrqrResidualScale n r := by ring

/-! ## Quantitative bounds for the literal skeleton -/

/-- Explicit bound for the upper skeleton coefficient. -/
def rrqrXScale (n r : ℕ) : ℝ :=
  ((r * n : ℕ) : ℝ) + rrqrPivotScale n r * rrqrResidualScale n r

/-- Explicit bound for the sum of the two skeleton coefficients. -/
def rrqrXYScale (n r : ℕ) : ℝ :=
  2 * ((r * n : ℕ) : ℝ) + rrqrPivotScale n r * rrqrResidualScale n r

/-- Explicit residual-block bound before simplifying to a fixed power of `n`. -/
def rrqrErrorScale (n r : ℕ) : ℝ :=
  (1 + ((r * n : ℕ) : ℝ)) * rrqrResidualScale n r

theorem rrqrPivotScale_nonneg (n r : ℕ) :
    0 ≤ rrqrPivotScale n r := by
  dsimp [rrqrPivotScale]
  positivity

/-- The first-round residual scale is at most `n⁷` when `r ≤ n` and
`n ≥ 2`.  This intentionally coarse fixed power keeps the public theorem
independent of the intermediate maximum-volume constants. -/
theorem rrqrResidualScale_le_pow_seven {n r : ℕ}
    (hn : 2 ≤ n) (hr : r ≤ n) :
    rrqrResidualScale n r ≤ (n : ℝ) ^ 7 := by
  have hN : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hR : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr
  have hN0 : (0 : ℝ) ≤ n := by positivity
  have hN1 : (1 : ℝ) ≤ n := by linarith
  have hR0 : (0 : ℝ) ≤ r := by positivity
  have hmain : rrqrResidualScale n r ≤ 5 * (n : ℝ) ^ 4 := by
    dsimp [rrqrResidualScale]
    norm_num [Nat.cast_mul]
    have hN2N4 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 :=
      pow_le_pow_right₀ hN1 (by omega)
    have h1N4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hN1
    have hRn : (r : ℝ) * n ≤ (n : ℝ) ^ 2 := by
      calc
        (r : ℝ) * n ≤ (n : ℝ) * n := by gcongr
        _ = (n : ℝ) ^ 2 := by ring
    have hnnrn : (n : ℝ) * n * r * n ≤ (n : ℝ) ^ 4 := by
      calc
        (n : ℝ) * n * r * n ≤ (n : ℝ) * n * n * n := by gcongr
        _ = (n : ℝ) ^ 4 := by ring
    calc
      (n : ℝ) * n * r * n + 2 * (r * n + 1) ≤
          (n : ℝ) ^ 4 + 2 * ((n : ℝ) ^ 2 + 1) := by gcongr
      _ ≤ (n : ℝ) ^ 4 +
          2 * ((n : ℝ) ^ 4 + (n : ℝ) ^ 4) := by gcongr
      _ = 5 * (n : ℝ) ^ 4 := by ring
  have h8 : (8 : ℝ) ≤ (n : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hN 3
    norm_num at h ⊢
    exact h
  calc
    rrqrResidualScale n r ≤ 5 * (n : ℝ) ^ 4 := hmain
    _ ≤ (n : ℝ) ^ 3 * (n : ℝ) ^ 4 := by
      gcongr
      linarith
    _ = (n : ℝ) ^ 7 := by ring

/-- The two-round pivot comparison scale is at most `n⁷`. -/
theorem rrqrPivotScale_le_pow_seven {n r : ℕ}
    (hn : 2 ≤ n) (hr : r ≤ n) :
    rrqrPivotScale n r ≤ (n : ℝ) ^ 7 := by
  have hN : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hR : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr
  have hN0 : (0 : ℝ) ≤ n := by positivity
  have hN1 : (1 : ℝ) ≤ n := by linarith
  have hR0 : (0 : ℝ) ≤ r := by positivity
  have hRn : (r : ℝ) * n ≤ (n : ℝ) ^ 2 := by
    calc
      (r : ℝ) * n ≤ (n : ℝ) * n := by gcongr
      _ = (n : ℝ) ^ 2 := by ring
  have hnnrn : (n : ℝ) * n * r * n ≤ (n : ℝ) ^ 4 := by
    calc
      (n : ℝ) * n * r * n ≤ (n : ℝ) * n * n * n := by gcongr
      _ = (n : ℝ) ^ 4 := by ring
  have hN2N4 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 :=
    pow_le_pow_right₀ hN1 (by omega)
  have hmain : rrqrPivotScale n r ≤ 2 * (n : ℝ) ^ 6 := by
    dsimp [rrqrPivotScale]
    norm_num [Nat.cast_mul]
    calc
      ((r : ℝ) * n + n * n * r * n) * (r * n) ≤
          ((n : ℝ) ^ 2 + (n : ℝ) ^ 4) * (n : ℝ) ^ 2 := by
        gcongr
      _ ≤ ((n : ℝ) ^ 4 + (n : ℝ) ^ 4) * (n : ℝ) ^ 2 := by
        gcongr
      _ = 2 * (n : ℝ) ^ 6 := by ring
  calc
    rrqrPivotScale n r ≤ 2 * (n : ℝ) ^ 6 := hmain
    _ ≤ (n : ℝ) * (n : ℝ) ^ 6 := by gcongr
    _ = (n : ℝ) ^ 7 := by ring

theorem norm_thresholdSkeletonData_Xskel_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (hr : 0 < largeSingularValueCount A tau) :
    ‖(thresholdSkeletonData A tau htau).Xskel‖ ≤
      rrqrXScale n (largeSingularValueCount A tau) := by
  let r := largeSingularValueCount A tau
  rw [thresholdSkeletonData_Xskel_eq A tau htau]
  have hT := norm_thresholdRightLeastSquaresBlock_le A tau htau
  have hTall := norm_thresholdLeastSquaresMatrix_le A tau htau
  have hTpoly : ‖thresholdRightLeastSquaresBlock A tau htau‖ ≤
      ((r * n : ℕ) : ℝ) := by
    calc
      ‖thresholdRightLeastSquaresBlock A tau htau‖ ≤
          ‖thresholdLeastSquaresMatrix A tau‖ := hT
      _ ≤ (r : ℝ) * n := by simpa [r] using hTall
      _ = ((r * n : ℕ) : ℝ) := by norm_num [Nat.cast_mul]
  have hKH : ‖(thresholdPivot A tau)⁻¹ *
        thresholdResidualTopRightBlock A tau htau‖ ≤
      rrqrPivotScale n r * rrqrResidualScale n r := by
    calc
      ‖(thresholdPivot A tau)⁻¹ *
          thresholdResidualTopRightBlock A tau htau‖ ≤
          ‖(thresholdPivot A tau)⁻¹‖ *
            ‖thresholdResidualTopRightBlock A tau htau‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ ‖(thresholdPivot A tau)⁻¹‖ *
          ‖thresholdResidualMatrix A tau‖ :=
        mul_le_mul_of_nonneg_left
          (norm_thresholdResidualTopRightBlock_le A tau htau) (norm_nonneg _)
      _ ≤ rrqrPivotScale n r * rrqrResidualScale n r := by
        simpa [r] using norm_thresholdPivot_inv_mul_residual_le
          A tau htau hr
  calc
    ‖thresholdRightLeastSquaresBlock A tau htau +
        (thresholdPivot A tau)⁻¹ *
          thresholdResidualTopRightBlock A tau htau‖ ≤
        ‖thresholdRightLeastSquaresBlock A tau htau‖ +
          ‖(thresholdPivot A tau)⁻¹ *
            thresholdResidualTopRightBlock A tau htau‖ := norm_add_le _ _
    _ ≤ ((r * n : ℕ) : ℝ) +
        rrqrPivotScale n r * rrqrResidualScale n r := add_le_add hTpoly hKH
    _ = rrqrXScale n r := rfl

theorem norm_thresholdSkeletonData_Xskel_add_Yskel_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (hr : 0 < largeSingularValueCount A tau) :
    ‖(thresholdSkeletonData A tau htau).Xskel‖ +
        ‖(thresholdSkeletonData A tau htau).Yskel‖ ≤
      rrqrXYScale n (largeSingularValueCount A tau) := by
  let r := largeSingularValueCount A tau
  have hX := norm_thresholdSkeletonData_Xskel_le A tau htau hr
  have hY := norm_thresholdSkeletonData_Yskel_le A tau htau
  have hYpoly : ‖(thresholdSkeletonData A tau htau).Yskel‖ ≤
      ((r * n : ℕ) : ℝ) := by
    calc
      ‖(thresholdSkeletonData A tau htau).Yskel‖ ≤
          (r : ℝ) * n := by simpa [r] using hY
      _ = ((r * n : ℕ) : ℝ) := by norm_num [Nat.cast_mul]
  calc
    ‖(thresholdSkeletonData A tau htau).Xskel‖ +
        ‖(thresholdSkeletonData A tau htau).Yskel‖ ≤
      rrqrXScale n r + ((r * n : ℕ) : ℝ) := add_le_add hX hYpoly
    _ = rrqrXYScale n r := by
      simp only [rrqrXScale, rrqrXYScale]
      ring

theorem norm_thresholdSkeletonData_E0_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (hn : 0 < n) :
    ‖(thresholdSkeletonData A tau htau).E0‖ ≤
      rrqrErrorScale n (largeSingularValueCount A tau) * tau := by
  let r := largeSingularValueCount A tau
  rw [thresholdSkeletonData_E0_eq A tau htau]
  have hY := norm_thresholdSkeletonData_Yskel_le A tau htau
  have hYpoly : ‖(thresholdSkeletonData A tau htau).Yskel‖ ≤
      ((r * n : ℕ) : ℝ) := by
    calc
      ‖(thresholdSkeletonData A tau htau).Yskel‖ ≤
          (r : ℝ) * n := by simpa [r] using hY
      _ = ((r * n : ℕ) : ℝ) := by norm_num [Nat.cast_mul]
  have hHt := norm_thresholdResidualTopRightBlock_le A tau htau
  have hHb := norm_thresholdResidualBottomRightBlock_le A tau htau
  have hH := norm_thresholdResidual_le_rrqrResidualScale_mul_tau
    A tau htau hn
  have hcoef : 0 ≤ 1 + ((r * n : ℕ) : ℝ) := by positivity
  calc
    ‖thresholdResidualBottomRightBlock A tau htau -
        (thresholdSkeletonData A tau htau).Yskel *
          thresholdResidualTopRightBlock A tau htau‖ ≤
      ‖thresholdResidualBottomRightBlock A tau htau‖ +
        ‖(thresholdSkeletonData A tau htau).Yskel *
          thresholdResidualTopRightBlock A tau htau‖ := norm_sub_le _ _
    _ ≤ ‖thresholdResidualMatrix A tau‖ +
        ‖(thresholdSkeletonData A tau htau).Yskel‖ *
          ‖thresholdResidualTopRightBlock A tau htau‖ :=
      add_le_add hHb (Matrix.l2_opNorm_mul _ _)
    _ ≤ ‖thresholdResidualMatrix A tau‖ +
        ((r * n : ℕ) : ℝ) * ‖thresholdResidualMatrix A tau‖ := by
      exact add_le_add (le_refl _) (mul_le_mul hYpoly hHt (norm_nonneg _) (by positivity))
    _ = (1 + ((r * n : ℕ) : ℝ)) *
        ‖thresholdResidualMatrix A tau‖ := by ring
    _ ≤ (1 + ((r * n : ℕ) : ℝ)) *
        (rrqrResidualScale n r * tau) :=
      mul_le_mul_of_nonneg_left (by simpa [r] using hH) hcoef
    _ = rrqrErrorScale n r * tau := by
      simp only [rrqrErrorScale]
      ring

/-- A single fixed exponent used by the caller-facing strong RRQR theorem. -/
def strongRRQRExponent : ℕ := 16

theorem rrqrXYScale_le_pow_sixteen {n r : ℕ}
    (hn : 2 ≤ n) (hr : r ≤ n) :
    rrqrXYScale n r ≤ (n : ℝ) ^ strongRRQRExponent := by
  have hN : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) ≤ n := by positivity
  have hN1 : (1 : ℝ) ≤ n := by linarith
  have hR : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr
  have hRn : ((r * n : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    norm_num [Nat.cast_mul]
    calc
      (r : ℝ) * n ≤ (n : ℝ) * n := by gcongr
      _ = (n : ℝ) ^ 2 := by ring
  have hP := rrqrPivotScale_le_pow_seven hn hr
  have hRscale := rrqrResidualScale_le_pow_seven hn hr
  have hprod : rrqrPivotScale n r * rrqrResidualScale n r ≤
      (n : ℝ) ^ 14 := by
    calc
      rrqrPivotScale n r * rrqrResidualScale n r ≤
          (n : ℝ) ^ 7 * (n : ℝ) ^ 7 :=
        mul_le_mul hP hRscale (rrqrResidualScale_nonneg n r) (by positivity)
      _ = (n : ℝ) ^ 14 := by ring
  have hN2N14 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 14 :=
    pow_le_pow_right₀ hN1 (by omega)
  have h4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hN 2
    norm_num at h ⊢
    exact h
  calc
    rrqrXYScale n r =
        2 * ((r * n : ℕ) : ℝ) +
          rrqrPivotScale n r * rrqrResidualScale n r := rfl
    _ ≤ 2 * (n : ℝ) ^ 2 + (n : ℝ) ^ 14 := by gcongr
    _ ≤ 2 * (n : ℝ) ^ 14 + (n : ℝ) ^ 14 := by gcongr
    _ = 3 * (n : ℝ) ^ 14 := by ring
    _ ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 14 := by
      gcongr
      linarith
    _ = (n : ℝ) ^ strongRRQRExponent := by
      simp only [strongRRQRExponent]
      ring

theorem rrqrErrorScale_le_pow_sixteen {n r : ℕ}
    (hn : 2 ≤ n) (hr : r ≤ n) :
    rrqrErrorScale n r ≤ (n : ℝ) ^ strongRRQRExponent := by
  have hN : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) ≤ n := by positivity
  have hN1 : (1 : ℝ) ≤ n := by linarith
  have hR : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr
  have hRn : ((r * n : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    norm_num [Nat.cast_mul]
    calc
      (r : ℝ) * n ≤ (n : ℝ) * n := by gcongr
      _ = (n : ℝ) ^ 2 := by ring
  have h1N2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hN1
  have hRscale := rrqrResidualScale_le_pow_seven hn hr
  have h2N7 : (2 : ℝ) ≤ (n : ℝ) ^ 7 := by
    exact hN.trans (le_self_pow₀ hN1 (by norm_num))
  calc
    rrqrErrorScale n r =
        (1 + ((r * n : ℕ) : ℝ)) * rrqrResidualScale n r := rfl
    _ ≤ (2 * (n : ℝ) ^ 2) * (n : ℝ) ^ 7 := by
      apply mul_le_mul
      · linarith
      · exact hRscale
      · exact rrqrResidualScale_nonneg n r
      · positivity
    _ = 2 * (n : ℝ) ^ 9 := by ring
    _ ≤ (n : ℝ) ^ 7 * (n : ℝ) ^ 9 := by gcongr
    _ = (n : ℝ) ^ strongRRQRExponent := by
      simp only [strongRRQRExponent]
      ring

theorem norm_thresholdSkeletonData_Xskel_add_Yskel_le_pow {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (hn : 2 ≤ n) :
    ‖(thresholdSkeletonData A tau htau).Xskel‖ +
        ‖(thresholdSkeletonData A tau htau).Yskel‖ ≤
      (n : ℝ) ^ strongRRQRExponent := by
  let r := largeSingularValueCount A tau
  by_cases hrzero : r = 0
  · have hX : (thresholdSkeletonData A tau htau).Xskel = 0 := by
      ext i
      have : Fin 0 := hrzero ▸ i
      exact Fin.elim0 this
    have hY : (thresholdSkeletonData A tau htau).Yskel = 0 := by
      ext i j
      have : Fin 0 := hrzero ▸ j
      exact Fin.elim0 this
    rw [hX, hY]
    simp only [norm_zero, zero_add]
    positivity
  · have hr : 0 < largeSingularValueCount A tau := by
      dsimp [r] at hrzero
      exact Nat.pos_of_ne_zero hrzero
    exact (norm_thresholdSkeletonData_Xskel_add_Yskel_le
      A tau htau hr).trans (rrqrXYScale_le_pow_sixteen hn
        (largeSingularValueCount_le A tau))

theorem norm_thresholdSkeletonData_E0_le_pow_mul_tau {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (hn : 2 ≤ n) :
    ‖(thresholdSkeletonData A tau htau).E0‖ ≤
      (n : ℝ) ^ strongRRQRExponent * tau := by
  have hnpos : 0 < n := by omega
  exact (norm_thresholdSkeletonData_E0_le A tau htau hnpos).trans
    (mul_le_mul_of_nonneg_right
      (rrqrErrorScale_le_pow_sixteen hn
        (largeSingularValueCount_le A tau)) htau)

theorem pow_inv_mul_singularValue_le_thresholdPivot {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (htau : 0 ≤ tau)
    (hn : 2 ≤ n) (j : Fin (largeSingularValueCount A tau)) :
    ((n : ℝ) ^ strongRRQRExponent)⁻¹ *
        (Matrix.toEuclideanLin A).singularValues j ≤
      (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues j := by
  have hnpos : (0 : ℝ) < n := by positivity
  rw [inv_mul_le_iff₀ (pow_pos hnpos strongRRQRExponent)]
  calc
    (Matrix.toEuclideanLin A).singularValues j ≤
        rrqrPivotScale n (largeSingularValueCount A tau) *
          (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues j :=
      singularValue_le_rrqrPivotScale_mul_pivot A tau htau j
    _ ≤ (n : ℝ) ^ 7 *
        (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues j :=
      mul_le_mul_of_nonneg_right
        (rrqrPivotScale_le_pow_seven hn
          (largeSingularValueCount_le A tau))
        ((Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues_nonneg j)
    _ ≤ (n : ℝ) ^ strongRRQRExponent *
        (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues j :=
      mul_le_mul_of_nonneg_right
        (by
          apply pow_le_pow_right₀
          · have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
            linarith
          · simp [strongRRQRExponent])
        ((Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues_nonneg j)

/-! ## Empty-pivot convention (`r = 0`) -/

section EmptyPivot

variable {n : ℕ}

abbrev emptySplitEquiv : Fin 0 ⊕ Fin n ≃ Fin n :=
  Equiv.emptySum (Fin 0) (Fin n)

/-- With an empty pivot the lower-right block is the original matrix. -/
theorem lowerRightBlock_empty (Q : Matrix (Fin n) (Fin n) ℂ) :
    lowerRightBlock (p := Fin 0) (q := Fin n) Q emptySplitEquiv emptySplitEquiv = Q := by
  ext i j
  rfl

/-- The `r = 0` convention: the pivot, `X_skel`, and `Y_skel` are the
unique empty matrices and `E₀ = Q`. -/
theorem empty_pivot_convention (Q : Matrix (Fin n) (Fin n) ℂ) :
    pivotBlock (p := Fin 0) (q := Fin n) Q emptySplitEquiv emptySplitEquiv = 0 ∧
      skeletonX (p := Fin 0) (q := Fin n) Q emptySplitEquiv emptySplitEquiv = 0 ∧
      skeletonY (p := Fin 0) (q := Fin n) Q emptySplitEquiv emptySplitEquiv = 0 ∧
      skeletonError (p := Fin 0) (q := Fin n) Q emptySplitEquiv emptySplitEquiv = Q := by
  constructor
  · ext i
    exact Fin.elim0 i
  constructor
  · ext i
    exact Fin.elim0 i
  constructor
  · ext i j
    exact Fin.elim0 j
  · rw [skeletonError, lowerRightBlock_empty]
    ext i j
    simp [skeletonY, pivotBlock, lowerLeftBlock]

/-- The literal empty-pivot block identity, expressed after the canonical
`Fin 0 ⊕ Fin n ≃ Fin n` coordinate reindexing. -/
theorem empty_pivot_block_identity (Q : Matrix (Fin n) (Fin n) ℂ) :
    permutedMatrix (p := Fin 0) (q := Fin n) Q emptySplitEquiv emptySplitEquiv =
      Matrix.fromBlocks
        (0 : Matrix (Fin 0) (Fin 0) ℂ)
        (0 : Matrix (Fin 0) (Fin n) ℂ)
        (0 : Matrix (Fin n) (Fin 0) ℂ)
        Q := by
  rw [permutedMatrix_eq_fromBlocks]
  ext i j
  rcases i with i | i
  · exact Fin.elim0 i
  · rcases j with j | j
    · exact Fin.elim0 j
    · rfl

end EmptyPivot

/-! ## Caller-facing strong RRQR conclusion with exponent 16 -/

/-- Complete output of the complex strong RRQR construction.  The structure
is output data, not an assumption: its row/column choices and skeleton are
constructed internally from `A` and `tau` by the theorem below. -/
structure StrongRRQRConclusion {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ) (r : ℕ) where
  /-- `r = #{j : s_j(A) > tau}`. -/
  r_eq : r = (Finset.univ.filter fun j : Fin n =>
    tau < (Matrix.toEuclideanLin A).singularValues j).card
  r_le_n : r ≤ n
  rowEquiv : Fin r ⊕ Fin (n - r) ≃ Fin n
  colEquiv : Fin r ⊕ Fin (n - r) ≃ Fin n
  data : BlockSkeletonData (Fin r) (Fin (n - r))
  /-- The pivot is literally the selected coordinate minor. -/
  pivot_eq : data.Kpiv = A.submatrix
    (fun i => rowEquiv (Sum.inl i)) (fun j => colEquiv (Sum.inl j))
  /-- This is total, including mathlib's `0 × 0` determinant convention. -/
  pivot_isUnit : IsUnit data.Kpiv.det
  /-- Literal `[[K,KX],[YK,YKX+E₀]]` identity. -/
  block_identity : A.submatrix rowEquiv colEquiv = skeletonMatrix data
  /-- Fixed-power singular-value comparison, for every selected index. -/
  pivot_singular_lower : ∀ j : Fin r,
    ((n : ℝ) ^ strongRRQRExponent)⁻¹ *
        (Matrix.toEuclideanLin A).singularValues j ≤
      (Matrix.toEuclideanLin data.Kpiv).singularValues j
  coefficient_bound : ‖data.Xskel‖ + ‖data.Yskel‖ ≤
    (n : ℝ) ^ strongRRQRExponent
  error_bound : ‖data.E0‖ ≤ (n : ℝ) ^ strongRRQRExponent * tau
  /-- At `r = 0`, all pivot-facing blocks are the unique empty matrices and
  `E₀` is the full complementary coordinate block. -/
  empty_pivot : r = 0 →
    data.Kpiv = 0 ∧ data.Xskel = 0 ∧ data.Yskel = 0 ∧
      data.E0 = A.submatrix
        (fun i => rowEquiv (Sum.inr i)) (fun j => colEquiv (Sum.inr j))

/-- Complex strong RRQR with exponent 16, built by two finite maximum-Gram-volume
selections.  The only inputs are the matrix, threshold, and the paper's
dimension/threshold side conditions; no RRQR certificate is supplied by the
caller. -/
noncomputable def strongRRQRConclusion {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ)
    (hn : 2 ≤ n) (htau : 1 ≤ tau) :
    StrongRRQRConclusion A tau (largeSingularValueCount A tau) := by
  let htau0 : 0 ≤ tau := le_trans zero_le_one htau
  let S := thresholdSkeletonData A tau htau0
  refine {
    r_eq := ?_
    r_le_n := largeSingularValueCount_le A tau
    rowEquiv := thresholdRowEquiv A tau htau0
    colEquiv := thresholdColEquiv A tau htau0
    data := S
    pivot_eq := ?_
    pivot_isUnit := ?_
    block_identity := ?_
    pivot_singular_lower := ?_
    coefficient_bound := ?_
    error_bound := ?_
    empty_pivot := ?_ }
  · rfl
  · change (thresholdPivot A tau) =
      A.submatrix
        (fun i => thresholdRowEquiv A tau htau0 (Sum.inl i))
        (fun j => thresholdColEquiv A tau htau0 (Sum.inl j))
    exact (thresholdPivotBlock_eq A tau htau0).symm
  · change IsUnit (thresholdPivot A tau).det
    exact thresholdPivot_isUnit_det A tau htau0
  · change permutedMatrix A (thresholdRowEquiv A tau htau0)
        (thresholdColEquiv A tau htau0) =
      skeletonMatrix (thresholdSkeletonData A tau htau0)
    exact threshold_permutedMatrix_eq_skeletonMatrix A tau htau0
  · intro j
    change ((n : ℝ) ^ strongRRQRExponent)⁻¹ *
        (Matrix.toEuclideanLin A).singularValues j ≤
      (Matrix.toEuclideanLin (thresholdPivot A tau)).singularValues j
    exact pow_inv_mul_singularValue_le_thresholdPivot
      A tau htau0 hn j
  · change ‖(thresholdSkeletonData A tau htau0).Xskel‖ +
        ‖(thresholdSkeletonData A tau htau0).Yskel‖ ≤
      (n : ℝ) ^ strongRRQRExponent
    exact norm_thresholdSkeletonData_Xskel_add_Yskel_le_pow
      A tau htau0 hn
  · change ‖(thresholdSkeletonData A tau htau0).E0‖ ≤
      (n : ℝ) ^ strongRRQRExponent * tau
    exact norm_thresholdSkeletonData_E0_le_pow_mul_tau A tau htau0 hn
  · intro hrzero
    have hK : (thresholdSkeletonData A tau htau0).Kpiv = 0 := by
      ext i
      have : Fin 0 := hrzero ▸ i
      exact Fin.elim0 this
    have hX : (thresholdSkeletonData A tau htau0).Xskel = 0 := by
      ext i
      have : Fin 0 := hrzero ▸ i
      exact Fin.elim0 this
    have hY : (thresholdSkeletonData A tau htau0).Yskel = 0 := by
      ext i j
      have : Fin 0 := hrzero ▸ j
      exact Fin.elim0 this
    refine ⟨hK, hX, hY, ?_⟩
    rw [thresholdSkeletonData_E0_eq A tau htau0, hY, Matrix.zero_mul,
      sub_zero]
    change (thresholdResidualMatrix A tau).submatrix
        (fun i => thresholdRowEquiv A tau htau0 (Sum.inr i))
        (fun j => thresholdColEquiv A tau htau0 (Sum.inr j)) = _
    rw [thresholdResidualMatrix_eq_self_of_count_eq_zero A tau hrzero]

/-- Existential theorem form of `strongRRQRConclusion`, useful to callers that
want to introduce the paper's rank variable explicitly. -/
theorem exists_strongRRQRConclusion {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (tau : ℝ)
    (hn : 2 ≤ n) (htau : 1 ≤ tau) :
    ∃ r : ℕ, Nonempty (StrongRRQRConclusion A tau r) :=
  ⟨largeSingularValueCount A tau,
    ⟨strongRRQRConclusion A tau hn htau⟩⟩

end BernoulliSection9
