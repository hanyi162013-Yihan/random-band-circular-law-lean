import CircularLawSection4.Exterior
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.FieldSimp

/-!
# Exact one-row linearity of compounds

The main theorem is `clearedRowCompanionCompound_eq_affine`.  It is the
coordinate/minor form of the manuscript's row-linearity identity

`β wedge^k (S - β⁻¹ e_ρ cᵀ) = β K_star - sum_j c_j K_j`.

The transpose here is bilinear.  No complex conjugation occurs.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

section RowMinorLinearity

variable {R : Type*} [CommRing R]
variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [LinearOrder ι]
variable [Fintype κ] [DecidableEq κ]

omit [CommRing R] [Fintype ι] [LinearOrder ι] [Fintype κ] in
theorem submatrix_updateRow_of_hit
    (A : Matrix ι ι R) (ρ : ι) (v : ι → R)
    (rows cols : κ → ι) (hrows : Function.Injective rows)
    (q : κ) (hq : rows q = ρ) :
    (A.updateRow ρ v).submatrix rows cols =
      (A.submatrix rows cols).updateRow q (fun j ↦ v (cols j)) := by
  ext i j
  by_cases hi : i = q
  · subst i
    simp [hq]
  · have hir : rows i ≠ ρ := by
      intro h
      apply hi
      apply hrows
      exact h.trans hq.symm
    simp [Matrix.updateRow_apply, hi, hir]

omit [CommRing R] [Fintype ι] [LinearOrder ι] [Fintype κ]
  [DecidableEq κ] in
theorem submatrix_updateRow_of_miss
    (A : Matrix ι ι R) (ρ : ι) (v : ι → R)
    (rows cols : κ → ι) (hmiss : ∀ q, rows q ≠ ρ) :
    (A.updateRow ρ v).submatrix rows cols = A.submatrix rows cols := by
  ext i j
  simp [Matrix.updateRow_apply, hmiss i]

omit [Fintype ι] [LinearOrder ι] in
theorem det_submatrix_updateRow_add_of_hit
    (A : Matrix ι ι R) (ρ : ι) (u v : ι → R)
    (rows cols : κ → ι) (hrows : Function.Injective rows)
    (q : κ) (hq : rows q = ρ) :
    ((A.updateRow ρ (u + v)).submatrix rows cols).det =
      ((A.updateRow ρ u).submatrix rows cols).det +
        ((A.updateRow ρ v).submatrix rows cols).det := by
  rw [submatrix_updateRow_of_hit A ρ (u + v) rows cols hrows q hq,
    submatrix_updateRow_of_hit A ρ u rows cols hrows q hq,
    submatrix_updateRow_of_hit A ρ v rows cols hrows q hq]
  exact Matrix.det_updateRow_add (A.submatrix rows cols) q
    (fun j ↦ u (cols j)) (fun j ↦ v (cols j))

omit [Fintype ι] [LinearOrder ι] in
theorem det_submatrix_updateRow_smul_of_hit
    (A : Matrix ι ι R) (ρ : ι) (a : R) (v : ι → R)
    (rows cols : κ → ι) (hrows : Function.Injective rows)
    (q : κ) (hq : rows q = ρ) :
    ((A.updateRow ρ (a • v)).submatrix rows cols).det =
      a * ((A.updateRow ρ v).submatrix rows cols).det := by
  rw [submatrix_updateRow_of_hit A ρ (a • v) rows cols hrows q hq,
    submatrix_updateRow_of_hit A ρ v rows cols hrows q hq]
  exact Matrix.det_updateRow_smul (A.submatrix rows cols) q a
    (fun j ↦ v (cols j))

end RowMinorLinearity

section CompoundRowLinearity

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

theorem compound_updateRow_add_apply_of_hit
    (k : ℕ) (A : Matrix ι ι R) (ρ : ι) (u v : ι → R)
    (s t : powersetCard ι k) (q : Fin k)
    (hq : ofFinEmbEquiv.symm s q = ρ) :
    compound k (A.updateRow ρ (u + v)) s t =
      compound k (A.updateRow ρ u) s t +
        compound k (A.updateRow ρ v) s t := by
  simp only [compound_apply]
  unfold minor
  exact det_submatrix_updateRow_add_of_hit A ρ u v
    (ofFinEmbEquiv.symm s) (ofFinEmbEquiv.symm t)
    (ofFinEmbEquiv.symm s).injective q hq

theorem compound_updateRow_smul_apply_of_hit
    (k : ℕ) (A : Matrix ι ι R) (ρ : ι) (a : R) (v : ι → R)
    (s t : powersetCard ι k) (q : Fin k)
    (hq : ofFinEmbEquiv.symm s q = ρ) :
    compound k (A.updateRow ρ (a • v)) s t =
      a * compound k (A.updateRow ρ v) s t := by
  simp only [compound_apply]
  unfold minor
  exact det_submatrix_updateRow_smul_of_hit A ρ a v
    (ofFinEmbEquiv.symm s) (ofFinEmbEquiv.symm t)
    (ofFinEmbEquiv.symm s).injective q hq

theorem compound_updateRow_apply_of_miss
    (k : ℕ) (A : Matrix ι ι R) (ρ : ι) (v : ι → R)
    (s t : powersetCard ι k)
    (hmiss : ∀ q : Fin k, ofFinEmbEquiv.symm s q ≠ ρ) :
    compound k (A.updateRow ρ v) s t = compound k A s t := by
  simp only [compound_apply]
  unfold minor
  rw [submatrix_updateRow_of_miss A ρ v
    (ofFinEmbEquiv.symm s) (ofFinEmbEquiv.symm t) hmiss]

theorem compound_updateRow_finsetSum_apply_of_hit
    {α : Type*} (k : ℕ) (A : Matrix ι ι R) (ρ : ι)
    (U : α → ι → R) (a : Finset α)
    (s t : powersetCard ι k) (q : Fin k)
    (hq : ofFinEmbEquiv.symm s q = ρ) :
    compound k (A.updateRow ρ (∑ x ∈ a, U x)) s t =
      ∑ x ∈ a, compound k (A.updateRow ρ (U x)) s t := by
  classical
  induction a using Finset.induction_on with
  | empty =>
      have hzero := compound_updateRow_smul_apply_of_hit
        k A ρ (0 : R) (0 : ι → R) s t q hq
      simpa using hzero
  | @insert x a hxa ih =>
      simp only [Finset.sum_insert hxa]
      rw [compound_updateRow_add_apply_of_hit k A ρ (U x)
        (∑ y ∈ a, U y) s t q hq, ih]

end CompoundRowLinearity

section ClearedCompanionRow

variable {F : Type*} [Field F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- A companion-style one-row update. -/
def rowCompanion (S : Matrix ι ι F) (ρ : ι) (β : F) (c : ι → F) :
    Matrix ι ι F :=
  S.updateRow ρ ((-β⁻¹) • c)

/-- One scalar denominator clears every exterior degree. -/
def clearedRowCompanionCompound (k : ℕ) (S : Matrix ι ι F)
    (ρ : ι) (β : F) (c : ι → F) :
    Matrix (powersetCard ι k) (powersetCard ι k) F :=
  β • compound k (rowCompanion S ρ β c)

/-- Contribution of minors which do not use the updated row. -/
def rowFreeCompound (k : ℕ) (S : Matrix ι ι F) (ρ : ι) :
    Matrix (powersetCard ι k) (powersetCard ι k) F := fun s t ↦
  if ρ ∈ s.val then 0 else compound k S s t

/-- Coefficient matrix of the `j`th updated-row coordinate. -/
def rowMinorCoefficient (k : ℕ) (S : Matrix ι ι F) (ρ j : ι) :
    Matrix (powersetCard ι k) (powersetCard ι k) F := fun s t ↦
  if ρ ∈ s.val then
    compound k (S.updateRow ρ (Pi.single j 1)) s t
  else 0

theorem clearedRowCompanionCompound_apply_of_hit
    (k : ℕ) (S : Matrix ι ι F) (ρ : ι) (β : F) (c : ι → F)
    (hβ : β ≠ 0) (s t : powersetCard ι k) (q : Fin k)
    (hq : ofFinEmbEquiv.symm s q = ρ) :
    clearedRowCompanionCompound k S ρ β c s t =
      -compound k (S.updateRow ρ c) s t := by
  rw [clearedRowCompanionCompound, Matrix.smul_apply]
  change β * compound k (S.updateRow ρ ((-β⁻¹) • c)) s t = _
  rw [compound_updateRow_smul_apply_of_hit
    k S ρ (-β⁻¹) c s t q hq]
  field_simp

theorem clearedRowCompanionCompound_apply_of_miss
    (k : ℕ) (S : Matrix ι ι F) (ρ : ι) (β : F) (c : ι → F)
    (s t : powersetCard ι k)
    (hmiss : ∀ q : Fin k, ofFinEmbEquiv.symm s q ≠ ρ) :
    clearedRowCompanionCompound k S ρ β c s t =
      β * compound k S s t := by
  rw [clearedRowCompanionCompound, Matrix.smul_apply]
  change β * compound k (S.updateRow ρ ((-β⁻¹) • c)) s t = _
  rw [compound_updateRow_apply_of_miss k S ρ ((-β⁻¹) • c) s t hmiss]

/-- **Row-linearity (Lemma 4.1).**  Exact affine dependence of the entire
cleared compound matrix on `β` and on every coordinate of `c`.  This includes
exterior degree zero. -/
theorem clearedRowCompanionCompound_eq_affine
    (k : ℕ) (S : Matrix ι ι F) (ρ : ι) (β : F) (c : ι → F)
    (hβ : β ≠ 0) :
    clearedRowCompanionCompound k S ρ β c =
      β • rowFreeCompound k S ρ -
        ∑ j, c j • rowMinorCoefficient k S ρ j := by
  classical
  ext s t
  by_cases hs : ρ ∈ s.val
  · obtain ⟨q, hq⟩ :=
      (mem_range_ofFinEmbEquiv_symm_iff_mem s ρ).mpr hs
    rw [clearedRowCompanionCompound_apply_of_hit
      k S ρ β c hβ s t q hq]
    have hlinear :
        compound k (S.updateRow ρ c) s t =
          ∑ j, c j *
            compound k (S.updateRow ρ (Pi.single j 1)) s t := by
      calc
        compound k (S.updateRow ρ c) s t =
            compound k
              (S.updateRow ρ
                (∑ j, (c j) • Pi.single (M := fun _ ↦ F) j 1)) s t := by
              rw [← pi_eq_sum_univ' c]
        _ = ∑ j, compound k
              (S.updateRow ρ ((c j) • Pi.single j 1)) s t := by
              simpa using
                (compound_updateRow_finsetSum_apply_of_hit
                  k S ρ
                    (fun j ↦ (c j) • Pi.single (M := fun _ ↦ F) j 1)
                    Finset.univ s t q hq)
        _ = ∑ j, c j *
              compound k (S.updateRow ρ (Pi.single j 1)) s t := by
              apply Finset.sum_congr rfl
              intro j _
              exact compound_updateRow_smul_apply_of_hit
                k S ρ (c j) (Pi.single j 1) s t q hq
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply,
      rowFreeCompound, rowMinorCoefficient, if_pos hs,
      smul_eq_mul]
    rw [hlinear]
    ring
  · have hmiss : ∀ q : Fin k, ofFinEmbEquiv.symm s q ≠ ρ := by
      intro q hq
      apply hs
      exact (mem_range_ofFinEmbEquiv_symm_iff_mem s ρ).mp ⟨q, hq⟩
    rw [clearedRowCompanionCompound_apply_of_miss
      k S ρ β c s t hmiss]
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply,
      rowFreeCompound, rowMinorCoefficient, hs]

end ClearedCompanionRow

end CircularLawSection4
