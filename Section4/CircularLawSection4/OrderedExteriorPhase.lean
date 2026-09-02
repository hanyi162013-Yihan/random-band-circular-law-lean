import CircularLawSection4.ArbitraryResetWord
import CircularLawSection4.RowLinearity
import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular

/-!
# Ordered exterior phases for the reset model

This module compares the actual ordered-minor coefficient matrices arising
from the companion shift with the Boolean reset support model.  The first
layer, proved here without assumptions, records that every one-step
coefficient is a sign, hence every surviving coefficient has modulus one.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

/-- The zero-based companion shift: column `j+1` is sent to row `j`. -/
def finLeftShift (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun i j ↦ if i.val + 1 = j.val then 1 else 0

/-- The actual coefficient family from row-linearity, including the minus
sign on reset coefficients.  We use `d+1` sites so that the distinguished
last row is available without an auxiliary positivity hypothesis. -/
def orderedCoefficient (d : ℕ) (q : ExteriorDegree (d + 1))
    (ell : ResetLabel (d + 1)) :
    Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ :=
  match ell with
  | none => rowFreeCompound q.val (finLeftShift d) (Fin.last d)
  | some j => -rowMinorCoefficient q.val (finLeftShift d) (Fin.last d) j

section TotallyUnimodular

variable {m n R : Type*} [CommRing R]
variable [DecidableEq n]

/-- A matrix whose rows each contain at most one signed unit is totally
unimodular.  The sign `0` represents an all-zero row. -/
theorem isTotallyUnimodular_of_rows_signSingle (A : Matrix m n R)
    (hA : Nonempty n → ∀ i : m, ∃ j : n, ∃ s : SignType,
      A i = Pi.single j s.cast) :
    A.IsTotallyUnimodular := by
  let Z : Matrix Empty n R := fun i _ ↦ isEmptyElim i
  have hZ : Z.IsTotallyUnimodular := Matrix.emptyRows_isTotallyUnimodular Z
  have hZA : (Matrix.fromRows Z A).IsTotallyUnimodular :=
    hZ.fromRows_unitlike hA
  have heq :
      (Matrix.fromRows Z A).submatrix (fun i ↦ Sum.inr i) id = A := by
    ext i j
    simp
  rw [← heq]
  exact hZA.submatrix (fun i ↦ Sum.inr i) id

/-- A signed-minor value which is nonzero has norm one over `ℂ`. -/
theorem norm_eq_one_of_mem_range_signType_cast {z : ℂ}
    (hz : z ∈ Set.range SignType.cast) (hne : z ≠ 0) : ‖z‖ = 1 := by
  obtain ⟨s, rfl⟩ := hz
  cases s <;> simp_all

/-- Every nonzero compound entry of a totally unimodular complex matrix has
unit modulus. -/
theorem norm_compound_apply_eq_one_of_tu
    {iota : Type*} [Fintype iota] [DecidableEq iota] [LinearOrder iota]
    (k : ℕ) (A : Matrix iota iota ℂ) (hA : A.IsTotallyUnimodular)
    (s t : powersetCard iota k) (hne : compound k A s t ≠ 0) :
    ‖compound k A s t‖ = 1 := by
  apply norm_eq_one_of_mem_range_signType_cast _ hne
  rw [compound_apply]
  exact hA k (ofFinEmbEquiv.symm s) (ofFinEmbEquiv.symm t)
    (ofFinEmbEquiv.symm s).injective (ofFinEmbEquiv.symm t).injective

/-- Every non-last row of the companion shift is a single positive unit. -/
theorem finLeftShift_row_eq_single (d : ℕ) (i : Fin (d + 1))
    (hi : i ≠ Fin.last d) :
    finLeftShift d i =
      Pi.single (let next : Fin (d + 1) := ⟨i.val + 1, by
        have hil : i.val < d := by
          have hi_le : i.val ≤ d := Nat.le_of_lt_succ i.isLt
          exact lt_of_le_of_ne hi_le (by
            intro hid
            apply hi
            apply Fin.ext
            simpa using hid)
        omega⟩
        next) 1 := by
  classical
  let next : Fin (d + 1) := ⟨i.val + 1, by
    have hi_le : i.val ≤ d := Nat.le_of_lt_succ i.isLt
    have hil : i.val < d := lt_of_le_of_ne hi_le (by
      intro hid
      apply hi
      apply Fin.ext
      simpa using hid)
    omega⟩
  change finLeftShift d i = Pi.single next 1
  funext j
  by_cases hj : j = next
  · subst j
    simp [finLeftShift, next]
  · have hval : i.val + 1 ≠ j.val := by
      intro h
      apply hj
      apply Fin.ext
      simpa [next] using h.symm
    simp [finLeftShift, hval, hj]

/-- The last row of the companion shift is zero. -/
theorem finLeftShift_last_row (d : ℕ) :
    finLeftShift d (Fin.last d) = 0 := by
  funext j
  simp only [finLeftShift, Fin.last]
  split_ifs with h
  · have := j.isLt
    omega
  · rfl

/-- The companion shift is totally unimodular. -/
theorem finLeftShift_isTotallyUnimodular (d : ℕ) :
    (finLeftShift d).IsTotallyUnimodular := by
  apply isTotallyUnimodular_of_rows_signSingle
  intro _ i
  by_cases hi : i = Fin.last d
  · refine ⟨0, 0, ?_⟩
    rw [hi, finLeftShift_last_row]
    ext j
    simp
  · let j : Fin (d + 1) := ⟨i.val + 1, by
      have hi_le : i.val ≤ d := Nat.le_of_lt_succ i.isLt
      have hil : i.val < d := lt_of_le_of_ne hi_le (by
        intro hid
        apply hi
        apply Fin.ext
        simpa using hid)
      omega⟩
    refine ⟨j, 1, ?_⟩
    simpa only [j, SignType.coe_one] using finLeftShift_row_eq_single d i hi

/-- Replacing the last row of the shift by a coordinate row preserves total
unimodularity. -/
theorem finLeftShift_updateLast_isTotallyUnimodular (d : ℕ)
    (j : Fin (d + 1)) :
    ((finLeftShift d).updateRow (Fin.last d) (Pi.single j 1)).IsTotallyUnimodular := by
  apply isTotallyUnimodular_of_rows_signSingle
  intro _ i
  by_cases hi : i = Fin.last d
  · subst i
    refine ⟨j, 1, ?_⟩
    ext k
    simp
  · let k : Fin (d + 1) := ⟨i.val + 1, by
      have hi_le : i.val ≤ d := Nat.le_of_lt_succ i.isLt
      have hil : i.val < d := lt_of_le_of_ne hi_le (by
        intro hid
        apply hi
        apply Fin.ext
        simpa using hid)
      omega⟩
    refine ⟨k, 1, ?_⟩
    rw [Matrix.updateRow_ne hi]
    simpa only [k, SignType.coe_one] using finLeftShift_row_eq_single d i hi

/-- A surviving star coefficient in the actual ordered exterior basis has
unit modulus. -/
theorem norm_rowFreeCompound_finLeftShift_eq_one
    (d k : ℕ) (B A : powersetCard (Fin (d + 1)) k)
    (hne : rowFreeCompound k (finLeftShift d) (Fin.last d) B A ≠ 0) :
    ‖rowFreeCompound k (finLeftShift d) (Fin.last d) B A‖ = 1 := by
  have hrow : Fin.last d ∉ B.val := by
    intro h
    apply hne
    simp [rowFreeCompound, h]
  simp only [rowFreeCompound, hrow, ↓reduceIte] at hne ⊢
  exact norm_compound_apply_eq_one_of_tu k (finLeftShift d)
    (finLeftShift_isTotallyUnimodular d) B A hne

/-- A surviving reset minor in the actual ordered exterior basis has unit
modulus. -/
theorem norm_rowMinorCoefficient_finLeftShift_eq_one
    (d k : ℕ) (j : Fin (d + 1))
    (B A : powersetCard (Fin (d + 1)) k)
    (hne : rowMinorCoefficient k (finLeftShift d) (Fin.last d) j B A ≠ 0) :
    ‖rowMinorCoefficient k (finLeftShift d) (Fin.last d) j B A‖ = 1 := by
  have hrow : Fin.last d ∈ B.val := by
    by_contra h
    apply hne
    simp [rowMinorCoefficient, h]
  simp only [rowMinorCoefficient, hrow, ↓reduceIte] at hne ⊢
  exact norm_compound_apply_eq_one_of_tu k
    ((finLeftShift d).updateRow (Fin.last d) (Pi.single j 1))
    (finLeftShift_updateLast_isTotallyUnimodular d j) B A hne

/-- Every nonzero entry of the actual one-step coefficient family has unit
modulus, including the row-linearity minus sign on resets. -/
theorem norm_orderedCoefficient_eq_one_of_ne_zero
    (d : ℕ) (q : ExteriorDegree (d + 1)) (ell : ResetLabel (d + 1))
    (B A : ExteriorIndex (d + 1) q)
    (hne : orderedCoefficient d q ell B A ≠ 0) :
    ‖orderedCoefficient d q ell B A‖ = 1 := by
  cases ell with
  | none =>
      exact norm_rowFreeCompound_finLeftShift_eq_one d q.val B A hne
  | some j =>
      change ‖-rowMinorCoefficient q.val (finLeftShift d) (Fin.last d) j B A‖ = 1
      rw [norm_neg]
      apply norm_rowMinorCoefficient_finLeftShift_eq_one d q.val j B A
      simpa [orderedCoefficient] using hne

end TotallyUnimodular

section CertificateTransport

/-- Entrywise equality of the norms of two word operators transports a
singleton certificate.  This isolates the exact remaining obligation for
the ordered/Boolean bridge: prove support equality for the one-step matrices
and propagate it through the deterministic partial-map product. -/
noncomputable def singletonWordCertificate_of_word_norm_eq
    {d : ℕ}
    {K K0 : (q : ExteriorDegree d) → ResetLabel d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ}
    {omega : Fin d → ResetLabel d} {r : ExteriorDegree d}
    {I J : ExteriorIndex d r}
    (h0 : SingletonWordCertificate K0 omega r I J)
    (hnorm : ∀ (q : ExteriorDegree d) (B A : ExteriorIndex d q),
      ‖wordOperator (K q) omega B A‖ =
        ‖wordOperator (K0 q) omega B A‖) :
    SingletonWordCertificate K omega r I J := by
  let phase : ℂ := wordOperator (K r) omega I J
  have phase_norm : ‖phase‖ = 1 := by
    rw [show ‖phase‖ = ‖wordOperator (K r) omega I J‖ by rfl,
      hnorm r I J, h0.selected_degree]
    simpa using h0.phase_norm
  refine {
    phase := phase
    phase_norm := phase_norm
    selected_degree := ?_
    other_degrees := ?_
  }
  · ext B A
    by_cases hBI : B = I
    · subst B
      by_cases hAJ : A = J
      · subst A
        simp [phase]
      · have hz_norm : ‖wordOperator (K r) omega I A‖ = 0 := by
          have hJA : J ≠ A := fun h ↦ hAJ h.symm
          rw [hnorm r I A, h0.selected_degree, Matrix.smul_apply,
            Matrix.single_apply_of_col_ne I I hJA 1]
          simp
        have hz : wordOperator (K r) omega I A = 0 := norm_eq_zero.mp hz_norm
        have hJA : J ≠ A := fun h ↦ hAJ h.symm
        rw [hz, Matrix.smul_apply,
          Matrix.single_apply_of_col_ne I I hJA 1]
        simp
    · have hz_norm : ‖wordOperator (K r) omega B A‖ = 0 := by
        have hIB : I ≠ B := fun h ↦ hBI h.symm
        rw [hnorm r B A, h0.selected_degree, Matrix.smul_apply,
          Matrix.single_apply_of_row_ne hIB J A 1]
        simp
      have hz : wordOperator (K r) omega B A = 0 := norm_eq_zero.mp hz_norm
      have hIB : I ≠ B := fun h ↦ hBI h.symm
      rw [hz, Matrix.smul_apply,
        Matrix.single_apply_of_row_ne hIB J A 1]
      simp
  · intro q hqr
    ext B A
    apply norm_eq_zero.mp
    rw [hnorm q B A, h0.other_degrees q hqr]
    simp

end CertificateTransport

end CircularLawSection4
