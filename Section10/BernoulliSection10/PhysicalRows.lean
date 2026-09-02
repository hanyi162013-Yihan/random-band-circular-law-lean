import BernoulliLinearAlgebra.ConcreteClearedTransfer

/-!
# Physical-row multiaffinity

This file formalizes Lemma 10.4.  A physical row consists of the corresponding
rows of the three one-site blocks `B`, `D = A - zI`, and `C`.  We work with the
denominator-free matrix `clearedStepCompound`; consequently the statement and
proof remain valid when `B` is singular.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliSection10

open Matrix Set Set.powersetCard
open BernoulliLinearAlgebra

/-- The `3W` scalar coordinates in one physical equation row.  The middle row
is the row of `D = A - zI`; hence the deterministic `-z` shift is already
included in this datum. -/
@[ext]
structure PhysicalRowGroup (W : Type*) where
  B : W → ℂ
  D : W → ℂ
  C : W → ℂ

namespace PhysicalRowGroup

/-- Affine interpolation of two physical rows. -/
def interpolate {W : Type*} (t : ℂ)
    (x y : PhysicalRowGroup W) : PhysicalRowGroup W where
  B j := (1 - t) * x.B j + t * y.B j
  D j := (1 - t) * x.D j + t * y.D j
  C j := (1 - t) * x.C j + t * y.C j

end PhysicalRowGroup

/-- The three physical blocks at one site. -/
@[ext]
structure PhysicalBlocks (W : Type*) where
  B : Matrix W W ℂ
  D : Matrix W W ℂ
  C : Matrix W W ℂ

namespace PhysicalBlocks

/-- Replace one complete physical row, simultaneously in `B`, `D`, and `C`. -/
def replaceRow {W : Type*} [DecidableEq W] (X : PhysicalBlocks W)
    (a : W) (g : PhysicalRowGroup W) : PhysicalBlocks W where
  B := X.B.updateRow a g.B
  D := X.D.updateRow a g.D
  C := X.C.updateRow a g.C

end PhysicalBlocks

/-- A function of the three site blocks is affine in physical row `a` if its
restriction to every line obtained by replacing that row obeys the usual
two-point affine interpolation identity.  All other rows remain fixed in `X`.
-/
def IsAffineInPhysicalRow {W E : Type*} [DecidableEq W]
    [AddCommMonoid E] [Module ℂ E]
    (a : W) (F : PhysicalBlocks W → E) : Prop :=
  ∀ (X : PhysicalBlocks W) (x y : PhysicalRowGroup W) (t : ℂ),
    F (X.replaceRow a (PhysicalRowGroup.interpolate t x y)) =
      (1 - t) • F (X.replaceRow a x) + t • F (X.replaceRow a y)

section DeterminantRows

variable {m n q : Type*}
variable [Fintype q] [DecidableEq q]

/-- Determinant interpolation when one row is replaced by an affine
interpolation of two candidate rows. -/
theorem det_updateRow_interpolate (A : Matrix q q ℂ) (i : q)
    (x y : q → ℂ) (t : ℂ) :
    (A.updateRow i (fun j => (1 - t) * x j + t * y j)).det =
      (1 - t) * (A.updateRow i x).det +
        t * (A.updateRow i y).det := by
  have hrow : (fun j => (1 - t) * x j + t * y j) =
      (1 - t) • x + t • y := by
    ext j
    simp
  rw [hrow, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.det_updateRow_smul]

/-- If the changed ambient row is absent from the selected row set, the minor
does not change. -/
theorem minor_updateRow_eq_of_not_mem
    [Fintype m] [LinearOrder m] [DecidableEq m]
    [LinearOrder n] [DecidableEq n]
    (k : ℕ) (A : Matrix m n ℂ) (i : m) (r : n → ℂ)
    (s : powersetCard m k) (u : powersetCard n k)
    (hi : i ∉ s) :
    minor k (A.updateRow i r) s u = minor k A s u := by
  unfold minor
  congr 1
  ext p v
  have hp : ofFinEmbEquiv.symm s p ≠ i := by
    intro hpi
    apply hi
    have hrange : ofFinEmbEquiv.symm s p ∈
        Set.range (ofFinEmbEquiv.symm s) := ⟨p, rfl⟩
    rw [mem_range_ofFinEmbEquiv_symm_iff_mem] at hrange
    simpa [hpi] using hrange
  simp [Matrix.updateRow_apply, hp]

/-- If the changed ambient row belongs to the selected row set, multilinearity
of the determinant makes the minor affine in the replacement row. -/
theorem minor_updateRow_interpolate_of_mem
    [Fintype m] [LinearOrder m] [DecidableEq m]
    [LinearOrder n] [DecidableEq n]
    (k : ℕ) (A : Matrix m n ℂ) (i : m) (x y : n → ℂ) (t : ℂ)
    (s : powersetCard m k) (u : powersetCard n k)
    (hi : i ∈ s) :
    minor k (A.updateRow i (fun j => (1 - t) * x j + t * y j)) s u =
      (1 - t) * minor k (A.updateRow i x) s u +
        t * minor k (A.updateRow i y) s u := by
  let e := ofFinEmbEquiv.symm s
  let f := ofFinEmbEquiv.symm u
  have hirange : i ∈ Set.range e := by
    rw [mem_range_ofFinEmbEquiv_symm_iff_mem]
    exact hi
  obtain ⟨p, hp⟩ := hirange
  have hsub (r : n → ℂ) :
      (A.updateRow i r).submatrix e f =
        (A.submatrix e f).updateRow p (fun v => r (f v)) := by
    ext p' v
    by_cases hpp : p' = p
    · subst p'
      simp [hp]
    · have hne : e p' ≠ i := by
        intro h
        apply hpp
        apply e.injective
        simpa [hp] using h
      simp [Matrix.updateRow_apply, hpp, hne]
  unfold minor
  rw [hsub, hsub, hsub]
  have hrow : (fun v => ((fun j => (1 - t) * x j + t * y j)) (f v)) =
      fun v => (1 - t) * (x (f v)) + t * (y (f v)) := rfl
  rw [hrow, det_updateRow_interpolate]

end DeterminantRows

section PhysicalStepRows

variable {W : Type*} [Fintype W] [LinearOrder W]

local instance physicalRowsSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift' (fun x : W ⊕ W => (toLex x : W ⊕ₗ W))
    (fun _ _ h => toLex.injective h)

/-- The top row inserted into `stepL B`. -/
def liftedBRow (g : PhysicalRowGroup W) : W ⊕ W → ℂ
  | Sum.inl j => g.B j
  | Sum.inr _ => 0

/-- The top row inserted into `stepK D C`. -/
def liftedDCRow (g : PhysicalRowGroup W) : W ⊕ W → ℂ
  | Sum.inl j => g.D j
  | Sum.inr j => g.C j

theorem liftedBRow_interpolate (t : ℂ) (x y : PhysicalRowGroup W) :
    liftedBRow (PhysicalRowGroup.interpolate t x y) =
      fun j => (1 - t) * liftedBRow x j + t * liftedBRow y j := by
  ext j
  cases j <;> simp [liftedBRow, PhysicalRowGroup.interpolate]

theorem liftedDCRow_interpolate (t : ℂ) (x y : PhysicalRowGroup W) :
    liftedDCRow (PhysicalRowGroup.interpolate t x y) =
      fun j => (1 - t) * liftedDCRow x j + t * liftedDCRow y j := by
  ext j
  cases j <;> simp [liftedDCRow, PhysicalRowGroup.interpolate]

/-- Replacing a physical `B` row is exactly replacement of the corresponding
top row in the augmented interface block `stepL`. -/
theorem stepL_replaceRow (X : PhysicalBlocks W) (a : W)
    (g : PhysicalRowGroup W) :
    stepL (X.replaceRow a g).B =
      (stepL X.B).updateRow (Sum.inl a) (liftedBRow g) := by
  ext i j
  cases i <;> cases j <;>
    simp [PhysicalBlocks.replaceRow, stepL, liftedBRow,
      Matrix.updateRow_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]

/-- Replacing the `D,C` parts of a physical row is exactly replacement of the
corresponding top row in `stepK`. -/
theorem stepK_replaceRow (X : PhysicalBlocks W) (a : W)
    (g : PhysicalRowGroup W) :
    stepK (X.replaceRow a g).D (X.replaceRow a g).C =
      (stepK X.D X.C).updateRow (Sum.inl a) (liftedDCRow g) := by
  ext i j
  cases i <;> cases j <;>
    simp [PhysicalBlocks.replaceRow, stepK, liftedDCRow,
      Matrix.updateRow_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]

/-- A deliberately small unfolding lemma for one entry of the cleared step.
Keeping this expansion separate prevents the simplifier from repeatedly
normalizing the much larger physical-row expressions below. -/
theorem clearedStepCompound_apply (k : ℕ) (B D C : Matrix W W ℂ)
    (s v : powersetCard (W ⊕ W) k) :
    clearedStepCompound k B D C s v =
      (-1 : ℂ) ^ k *
        (clearedInverseCompound k (stepL B) *
          compound k (stepK D C)) s v := by
  unfold clearedStepCompound
  rw [Matrix.smul_apply]
  simp only [smul_eq_mul]

/-- One summand in the Cauchy--Binet expansion defining a cleared one-step
compound is affine in the complete physical row.  The key point is that the
intermediate row set selects the row either in the `stepK` minor or in the
complementary `stepL` minor, never in both. -/
theorem clearedStepCompound_summand_row_interpolate
    (k : ℕ) (hk : k ≤ Fintype.card (W ⊕ W))
    (X : PhysicalBlocks W) (a : W)
    (x y : PhysicalRowGroup W) (t : ℂ)
    (s u v : powersetCard (W ⊕ W) k) :
    clearedInverseCompound k
          (stepL (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).B) s u *
        compound k
          (stepK (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).D
            (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).C) u v =
      (1 - t) *
          (clearedInverseCompound k (stepL (X.replaceRow a x).B) s u *
            compound k (stepK (X.replaceRow a x).D
              (X.replaceRow a x).C) u v) +
        t *
          (clearedInverseCompound k (stepL (X.replaceRow a y).B) s u *
            compound k (stepK (X.replaceRow a y).D
              (X.replaceRow a y).C) u v) := by
  let hm : Fintype.card (W ⊕ W) - k + k = Fintype.card (W ⊕ W) :=
    Nat.sub_add_cancel hk
  by_cases ha : Sum.inl a ∈ u
  · have hac : Sum.inl a ∉ powersetCard.compl hm u := by
      simpa using ha
    have hB (g : PhysicalRowGroup W) :
        clearedInverseCompound k (stepL (X.replaceRow a g).B) s u =
          clearedInverseCompound k (stepL X.B) s u := by
      rw [clearedInverseCompound_apply_of_le k _ hk,
        clearedInverseCompound_apply_of_le k _ hk,
        stepL_replaceRow]
      rw [minor_updateRow_eq_of_not_mem _ _ _ _ _ _ hac]
    have hK :
        compound k
            (stepK (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).D
              (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).C) u v =
          (1 - t) *
              compound k (stepK (X.replaceRow a x).D
                (X.replaceRow a x).C) u v +
            t * compound k (stepK (X.replaceRow a y).D
                (X.replaceRow a y).C) u v := by
      simp only [compound_apply]
      rw [stepK_replaceRow, stepK_replaceRow, stepK_replaceRow,
        liftedDCRow_interpolate]
      exact minor_updateRow_interpolate_of_mem _ _ _ _ _ _ _ _ ha
    rw [hB, hB, hB, hK]
    ring
  · have hac : Sum.inl a ∈ powersetCard.compl hm u := by
      simpa using ha
    have hK (g : PhysicalRowGroup W) :
        compound k (stepK (X.replaceRow a g).D
            (X.replaceRow a g).C) u v =
          compound k (stepK X.D X.C) u v := by
      simp only [compound_apply]
      rw [stepK_replaceRow]
      exact minor_updateRow_eq_of_not_mem _ _ _ _ _ _ ha
    have hB :
        clearedInverseCompound k
            (stepL (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).B) s u =
          (1 - t) *
              clearedInverseCompound k (stepL (X.replaceRow a x).B) s u +
            t * clearedInverseCompound k (stepL (X.replaceRow a y).B) s u := by
      rw [clearedInverseCompound_apply_of_le k _ hk,
        clearedInverseCompound_apply_of_le k _ hk,
        clearedInverseCompound_apply_of_le k _ hk,
        stepL_replaceRow, stepL_replaceRow, stepL_replaceRow,
        liftedBRow_interpolate]
      have hminor := minor_updateRow_interpolate_of_mem
        (Fintype.card (W ⊕ W) - k) (stepL X.B) (Sum.inl a)
        (liftedBRow x) (liftedBRow y) t
        (powersetCard.compl hm u) (powersetCard.compl hm s) hac
      rw [hminor]
      ring
    rw [hK, hK, hK, hB]
    ring

/-- Entrywise form of Lemma 10.4: every entry of the denominator-free one-site
exterior operator is affine in each full physical row group. -/
theorem clearedStepCompound_entry_row_interpolate
    (k : ℕ) (hk : k ≤ Fintype.card (W ⊕ W))
    (X : PhysicalBlocks W) (a : W)
    (x y : PhysicalRowGroup W) (t : ℂ)
    (s v : powersetCard (W ⊕ W) k) :
    clearedStepCompound k
        (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).B
        (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).D
        (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).C s v =
      (1 - t) *
          clearedStepCompound k (X.replaceRow a x).B
            (X.replaceRow a x).D (X.replaceRow a x).C s v +
        t * clearedStepCompound k (X.replaceRow a y).B
            (X.replaceRow a y).D (X.replaceRow a y).C s v := by
  simp only [clearedStepCompound_apply, Matrix.mul_apply]
  calc
    (-1 : ℂ) ^ k *
          ∑ u, clearedInverseCompound k
              (stepL (X.replaceRow a
                (PhysicalRowGroup.interpolate t x y)).B) s u *
            compound k
              (stepK (X.replaceRow a
                  (PhysicalRowGroup.interpolate t x y)).D
                (X.replaceRow a
                  (PhysicalRowGroup.interpolate t x y)).C) u v =
        (-1 : ℂ) ^ k *
          ∑ u, ((1 - t) *
              (clearedInverseCompound k (stepL (X.replaceRow a x).B) s u *
                compound k (stepK (X.replaceRow a x).D
                  (X.replaceRow a x).C) u v) +
            t *
              (clearedInverseCompound k (stepL (X.replaceRow a y).B) s u *
                compound k (stepK (X.replaceRow a y).D
                  (X.replaceRow a y).C) u v)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro u _
          exact clearedStepCompound_summand_row_interpolate
            k hk X a x y t s u v
    _ = (1 - t) *
          ((-1 : ℂ) ^ k *
            ∑ u, clearedInverseCompound k (stepL (X.replaceRow a x).B) s u *
              compound k (stepK (X.replaceRow a x).D
                (X.replaceRow a x).C) u v) +
        t *
          ((-1 : ℂ) ^ k *
            ∑ u, clearedInverseCompound k (stepL (X.replaceRow a y).B) s u *
              compound k (stepK (X.replaceRow a y).D
                (X.replaceRow a y).C) u v) := by
          rw [Finset.sum_add_distrib]
          simp_rw [← Finset.mul_sum]
          ring

/-- Matrix-valued caller-facing form of Lemma 10.4. -/
theorem clearedStepCompound_isAffineInPhysicalRow
    (k : ℕ) (hk : k ≤ Fintype.card (W ⊕ W)) (a : W) :
    IsAffineInPhysicalRow a
      (fun X : PhysicalBlocks W => clearedStepCompound k X.B X.D X.C) := by
  intro X x y t
  ext s v
  simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using
    clearedStepCompound_entry_row_interpolate k hk X a x y t s v

/-- Multiplication on the left and right by matrices independent of the
physical row preserves the separate-affinity identity. -/
theorem independent_mul_clearedStepCompound_mul_isAffineInPhysicalRow
    (k : ℕ) (hk : k ≤ Fintype.card (W ⊕ W)) (a : W)
    (L R : Matrix (powersetCard (W ⊕ W) k)
      (powersetCard (W ⊕ W) k) ℂ) :
    IsAffineInPhysicalRow a
      (fun X : PhysicalBlocks W =>
        L * clearedStepCompound k X.B X.D X.C * R) := by
  intro X x y t
  change
    L * clearedStepCompound k
          (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).B
          (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).D
          (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).C * R =
      (1 - t) •
          (L * clearedStepCompound k (X.replaceRow a x).B
            (X.replaceRow a x).D (X.replaceRow a x).C * R) +
        t •
          (L * clearedStepCompound k (X.replaceRow a y).B
            (X.replaceRow a y).D (X.replaceRow a y).C * R)
  have hstep :
      clearedStepCompound k
          (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).B
          (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).D
          (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).C =
        (1 - t) • clearedStepCompound k (X.replaceRow a x).B
            (X.replaceRow a x).D (X.replaceRow a x).C +
          t • clearedStepCompound k (X.replaceRow a y).B
            (X.replaceRow a y).D (X.replaceRow a y).C := by
    exact clearedStepCompound_isAffineInPhysicalRow k hk a X x y t
  calc
    _ = L *
          ((1 - t) • clearedStepCompound k (X.replaceRow a x).B
              (X.replaceRow a x).D (X.replaceRow a x).C +
            t • clearedStepCompound k (X.replaceRow a y).B
              (X.replaceRow a y).D (X.replaceRow a y).C) * R := by
        exact congrArg (fun M => L * M * R) hstep
    _ = _ := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
        Matrix.smul_mul]

/-- Entrywise corollary for an arbitrary product with independent left and
right factors, matching the operator-valued formulation in Lemma 10.4. -/
theorem independent_mul_clearedStepCompound_mul_entry_row_interpolate
    (k : ℕ) (hk : k ≤ Fintype.card (W ⊕ W))
    (X : PhysicalBlocks W) (a : W)
    (x y : PhysicalRowGroup W) (t : ℂ)
    (L R : Matrix (powersetCard (W ⊕ W) k)
      (powersetCard (W ⊕ W) k) ℂ)
    (s v : powersetCard (W ⊕ W) k) :
    (L * clearedStepCompound k
        (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).B
        (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).D
        (X.replaceRow a (PhysicalRowGroup.interpolate t x y)).C * R) s v =
      (1 - t) *
          (L * clearedStepCompound k (X.replaceRow a x).B
            (X.replaceRow a x).D (X.replaceRow a x).C * R) s v +
        t *
          (L * clearedStepCompound k (X.replaceRow a y).B
            (X.replaceRow a y).D (X.replaceRow a y).C * R) s v := by
  have h := independent_mul_clearedStepCompound_mul_isAffineInPhysicalRow
    k hk a L R X x y t
  simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using congrFun₂ h s v

end PhysicalStepRows

end BernoulliSection10
