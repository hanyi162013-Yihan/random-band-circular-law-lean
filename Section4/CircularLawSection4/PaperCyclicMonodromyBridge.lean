import CircularLawSection4.ArbitraryPeriodicElimination
import CircularLawSection4.CyclicCompanionRawRows
import CircularLawSection4.PaperPeriodicDeterminant
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# From the paper's raw cyclic companion matrix to monodromy

This module closes the second deterministic interface in the periodic
determinant proof.  It first identifies the paper's raw state-copy matrix with
the cyclic equations

`s_(i+1) - T_i s_i = 0`,

for an explicit companion transfer `T_i`.  A finite cyclic elimination then
proves that the determinant is a permutation sign times
`det (1 - chronologicalProduct (List.ofFn T))`.  Finally this is compared with
the already constructed `recursivePeriodicSystem`.  The latter has two dummy
identity blocks, so the comparison is at determinant level rather than by an
impossible same-cardinality reindexing.
-/

open scoped Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

section RawTransfer

variable {R : Type*} [Field R]

/-- The companion transfer read directly from the paper's raw last equation.
Its first `m` output coordinates shift the state, and its final coordinate is
the negative normalized coefficient row. -/
def paperCyclicTransferMatrix
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R)
    (i : ZMod N) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  fun row col => Fin.lastCases
    (-((βraw i)⁻¹ * a i col))
    (fun k => if col = k.succ then 1 else 0) row

/-- A raw block-cyclic transfer system, with one equation
`s_(i+1) - T_i s_i = 0` at every cyclic site. -/
def rawCyclicTransferSystem
    (N : ℕ) [NeZero N] {d : Type*} [Fintype d] [DecidableEq d]
    (T : ZMod N → Matrix d d R) :
    Matrix (ZMod N × d) (ZMod N × d) R :=
  fun row col =>
    (if col.1 = row.1 + 1 then (1 : Matrix d d R) row.2 col.2 else 0) -
      if col.1 = row.1 then T row.1 row.2 col.2 else 0

/-- Entrywise identification of the paper's raw cyclic companion state matrix
with the explicit cyclic transfer system. -/
theorem cyclicCompanionStateMatrix_eq_rawCyclicTransferSystem
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R) :
    cyclicCompanionStateMatrix N m offset
        (paperSparseCyclicLastRow N m βraw a) =
      rawCyclicTransferSystem N
        (paperCyclicTransferMatrix N m βraw a) := by
  classical
  ext ⟨i, r⟩ ⟨j, c⟩
  refine Fin.lastCases ?_ (fun k => ?_) r
  · simp [cyclicCompanionStateMatrix_last, paperSparseCyclicLastRow,
      rawCyclicTransferSystem, paperCyclicTransferMatrix, Matrix.one_apply]
    split_ifs <;> simp_all
  · rw [cyclicCompanionStateMatrix_castSucc_row]
    simp [rawCyclicTransferSystem, paperCyclicTransferMatrix,
      Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp_all

end RawTransfer

section FiniteCyclicElimination

variable {R : Type*} [Field R]
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The same cyclic system after shifting equation row `i` to its target site
`i+1`.  This convention puts identity blocks on the diagonal. -/
def finShiftedCyclicSystem (n : ℕ)
    (T : Fin (n + 1) → Matrix d d R) :
    Matrix (Fin (n + 1) × d) (Fin (n + 1) × d) R :=
  fun row col =>
    (if row.1 = col.1 then (1 : Matrix d d R) row.2 col.2 else 0) -
      Fin.cases
        (if col.1 = Fin.last n then T (Fin.last n) row.2 col.2 else 0)
        (fun k =>
          if col.1 = k.castSucc then T k.castSucc row.2 col.2 else 0)
        row.1

private theorem finCases_last
    {α : Type*} (n : ℕ) (z : α) (f : Fin (n + 1) → α) :
    Fin.cases z f (Fin.last (n + 1)) = f (Fin.last n) := by
  rw [show Fin.last (n + 1) = (Fin.last n).succ from
    (Fin.succ_last n).symm]
  rfl

/-- Split the final site from a product-indexed state space. -/
def splitLastSiteEquiv (n : ℕ) :
    Fin (n + 2) × d ≃ (Fin (n + 1) × d) ⊕ d :=
  ((finSplitLastEquiv (n + 1)).prodCongr (Equiv.refl d)) |>.trans
    (Equiv.sumProdDistrib (Fin (n + 1)) Unit d) |>.trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.uniqueProd d Unit))

omit [Fintype d] [DecidableEq d] in
@[simp] theorem splitLastSiteEquiv_castSucc
    (n : ℕ) (i : Fin (n + 1)) (x : d) :
    splitLastSiteEquiv (d := d) n (i.castSucc, x) = Sum.inl (i, x) := by
  simp [splitLastSiteEquiv, finSplitLastEquiv]

omit [Fintype d] [DecidableEq d] in
@[simp] theorem splitLastSiteEquiv_last
    (n : ℕ) (x : d) :
    splitLastSiteEquiv (d := d) n (Fin.last (n + 1), x) = Sum.inr x := by
  simp [splitLastSiteEquiv, finSplitLastEquiv]

omit [Fintype d] [DecidableEq d] in
@[simp] theorem splitLastSiteEquiv_symm_inl
    (n : ℕ) (i : Fin (n + 1)) (x : d) :
    (splitLastSiteEquiv (d := d) n).symm (Sum.inl (i, x)) =
      (i.castSucc, x) := by
  apply (splitLastSiteEquiv (d := d) n).injective
  simp

omit [Fintype d] [DecidableEq d] in
@[simp] theorem splitLastSiteEquiv_symm_inr
    (n : ℕ) (x : d) :
    (splitLastSiteEquiv (d := d) n).symm (Sum.inr x) =
      (Fin.last (n + 1), x) := by
  apply (splitLastSiteEquiv (d := d) n).injective
  simp

/-- Merge the last two transfers after eliminating the final state variable. -/
def mergeLastTransfer (n : ℕ)
    (T : Fin (n + 2) → Matrix d d R) :
    Fin (n + 1) → Matrix d d R :=
  Fin.lastCases
    (T (Fin.last (n + 1)) * T (Fin.last n).castSucc)
    (fun i => T i.castSucc.castSucc)

/-- The chronological product is unchanged when its final two factors are
merged in chronological order. -/
theorem chronologicalProduct_mergeLastTransfer (n : ℕ)
    (T : Fin (n + 2) → Matrix d d R) :
    chronologicalProduct (List.ofFn (mergeLastTransfer n T)) =
      chronologicalProduct (List.ofFn T) := by
  simp only [List.ofFn_succ', List.concat_eq_append, mergeLastTransfer,
    Fin.lastCases_last, Fin.lastCases_castSucc, chronologicalProduct_append,
    chronologicalProduct_cons, chronologicalProduct_nil, Matrix.one_mul]
  rw [Matrix.mul_assoc]

private def shiftedOldBlock (n : ℕ)
    (T : Fin (n + 2) → Matrix d d R) :
    Matrix (Fin (n + 1) × d) (Fin (n + 1) × d) R :=
  fun r c =>
    Matrix.reindex (splitLastSiteEquiv (d := d) n)
      (splitLastSiteEquiv (d := d) n)
      (finShiftedCyclicSystem (n + 1) T) (Sum.inl r) (Sum.inl c)

private def shiftedLastColumn (n : ℕ)
    (T : Fin (n + 2) → Matrix d d R) :
    Matrix (Fin (n + 1) × d) d R :=
  fun r c =>
    Matrix.reindex (splitLastSiteEquiv (d := d) n)
      (splitLastSiteEquiv (d := d) n)
      (finShiftedCyclicSystem (n + 1) T) (Sum.inl r) (Sum.inr c)

private def shiftedLastRow (n : ℕ)
    (T : Fin (n + 2) → Matrix d d R) :
    Matrix d (Fin (n + 1) × d) R :=
  fun r c =>
    Matrix.reindex (splitLastSiteEquiv (d := d) n)
      (splitLastSiteEquiv (d := d) n)
      (finShiftedCyclicSystem (n + 1) T) (Sum.inr r) (Sum.inl c)

omit [Fintype d] in
private theorem shiftedOldBlock_apply
    (n : ℕ) (T : Fin (n + 2) → Matrix d d R)
    (i j : Fin (n + 1)) (x y : d) :
    shiftedOldBlock n T (i, x) (j, y) =
      (if i = j then (1 : Matrix d d R) x y else 0) -
        Fin.cases 0
          (fun k => if j = k.castSucc then T k.castSucc.castSucc x y else 0)
          i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [shiftedOldBlock, finShiftedCyclicSystem, Matrix.one_apply]
    simp only [Fin.ext_iff, Fin.val_zero, Fin.val_castSucc]
  · simp [shiftedOldBlock, finShiftedCyclicSystem, Matrix.one_apply]
    simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]

omit [Fintype d] in
private theorem shiftedLastColumn_apply
    (n : ℕ) (T : Fin (n + 2) → Matrix d d R)
    (i : Fin (n + 1)) (x y : d) :
    shiftedLastColumn n T (i, x) y =
      if i = 0 then -T (Fin.last (n + 1)) x y else 0 := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [shiftedLastColumn, finShiftedCyclicSystem]
  · simp [shiftedLastColumn, finShiftedCyclicSystem]
    intro h
    exact (Fin.castSucc_ne_last i.castSucc h.symm).elim

omit [Fintype d] in
private theorem shiftedLastRow_apply
    (n : ℕ) (T : Fin (n + 2) → Matrix d d R)
    (x : d) (j : Fin (n + 1)) (y : d) :
    shiftedLastRow n T x (j, y) =
      if j = Fin.last n then -T (Fin.last n).castSucc x y else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  ·
    change finShiftedCyclicSystem (n + 1) T
        ((splitLastSiteEquiv (d := d) n).symm (Sum.inr x))
        ((splitLastSiteEquiv (d := d) n).symm
          (Sum.inl (Fin.last n, y))) = _
    rw [splitLastSiteEquiv_symm_inr, splitLastSiteEquiv_symm_inl]
    rw [finShiftedCyclicSystem]
    simp [finCases_last, Matrix.one_apply]
    intro h
    exact (Fin.castSucc_ne_last (Fin.last n) h.symm).elim
  ·
    change finShiftedCyclicSystem (n + 1) T
        ((splitLastSiteEquiv (d := d) n).symm (Sum.inr x))
        ((splitLastSiteEquiv (d := d) n).symm
          (Sum.inl (j.castSucc, y))) = _
    rw [splitLastSiteEquiv_symm_inr, splitLastSiteEquiv_symm_inl]
    rw [finShiftedCyclicSystem]
    simp [finCases_last, Matrix.one_apply]
    intro h
    exact (Fin.castSucc_ne_last j.castSucc h.symm).elim

omit [Fintype d] in
private theorem finShiftedCyclicSystem_lastBlock
    (n : ℕ) (T : Fin (n + 2) → Matrix d d R) :
    Matrix.reindex (splitLastSiteEquiv (d := d) n)
        (splitLastSiteEquiv (d := d) n)
        (finShiftedCyclicSystem (n + 1) T) =
      Matrix.fromBlocks (shiftedOldBlock n T) (shiftedLastColumn n T)
        (shiftedLastRow n T) 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · rfl
  ·
    change finShiftedCyclicSystem (n + 1) T
        ((splitLastSiteEquiv (d := d) n).symm (Sum.inr i))
        ((splitLastSiteEquiv (d := d) n).symm (Sum.inr j)) =
      (1 : Matrix d d R) i j
    rw [splitLastSiteEquiv_symm_inr, splitLastSiteEquiv_symm_inr]
    rw [finShiftedCyclicSystem]
    simp [finCases_last, Matrix.one_apply]
    intro h
    exact (Fin.castSucc_ne_last (Fin.last n) h.symm).elim

private theorem finShiftedCyclicSystem_schur
    (n : ℕ) (T : Fin (n + 2) → Matrix d d R) :
    shiftedOldBlock n T - shiftedLastColumn n T * shiftedLastRow n T =
      finShiftedCyclicSystem n (mergeLastTransfer n T) := by
  classical
  ext ⟨i, x⟩ ⟨j, y⟩
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [shiftedOldBlock_apply, shiftedLastColumn_apply,
        shiftedLastRow_apply, finShiftedCyclicSystem, mergeLastTransfer,
        Matrix.mul_apply, Matrix.one_apply]
    · simp [shiftedOldBlock_apply, shiftedLastColumn_apply,
        shiftedLastRow_apply, finShiftedCyclicSystem, mergeLastTransfer,
        Matrix.mul_apply, Matrix.one_apply]
  · simp [shiftedOldBlock_apply, shiftedLastColumn_apply,
      shiftedLastRow_apply, finShiftedCyclicSystem, mergeLastTransfer,
      Matrix.mul_apply, Matrix.one_apply]

/-- Eliminating the final identity pivot contracts the last two cyclic
transfers into their chronological product. -/
theorem finShiftedCyclicSystem_det_contract
    (n : ℕ) (T : Fin (n + 2) → Matrix d d R) :
    (finShiftedCyclicSystem (n + 1) T).det =
      (finShiftedCyclicSystem n (mergeLastTransfer n T)).det := by
  rw [← Matrix.det_reindex_self (splitLastSiteEquiv (d := d) n)]
  rw [finShiftedCyclicSystem_lastBlock]
  rw [Matrix.det_fromBlocks_one₂₂]
  exact congrArg Matrix.det (finShiftedCyclicSystem_schur n T)

/-- Determinant of a finite cyclic transfer system. -/
theorem finShiftedCyclicSystem_det (n : ℕ)
    (T : Fin (n + 1) → Matrix d d R) :
    (finShiftedCyclicSystem n T).det =
      (1 - chronologicalProduct (List.ofFn T)).det := by
  induction n with
  | zero =>
      let e : Fin 1 × d ≃ d := Equiv.uniqueProd d (Fin 1)
      rw [← Matrix.det_reindex_self e]
      congr 1
      ext i j
      simp [e, finShiftedCyclicSystem, Matrix.one_apply,
        Equiv.uniqueProd_symm_apply]
      rfl
  | succ n ih =>
      rw [finShiftedCyclicSystem_det_contract n T]
      rw [ih (mergeLastTransfer n T)]
      rw [chronologicalProduct_mergeLastTransfer n T]

end FiniteCyclicElimination

section RawToFinite

variable {R : Type*} [Field R]
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Translation by one on the cyclic site group. -/
def zmodAddOneEquiv (N : ℕ) [NeZero N] : ZMod N ≃ ZMod N where
  toFun i := i + 1
  invFun j := j - 1
  left_inv i := by simp [sub_eq_add_neg, add_assoc]
  right_inv j := by simp [sub_eq_add_neg, add_assoc]

/-- Raw state columns are put in the standard finite site order. -/
def rawCyclicColumnEquiv (n : ℕ) :
    ZMod (n + 1) × d ≃ Fin (n + 1) × d :=
  ((ZMod.finEquiv (n + 1)).symm.toEquiv.prodCongr (Equiv.refl d))

/-- Raw equation row `i` is put at its target site `i+1`. -/
def rawCyclicTargetRowEquiv (n : ℕ) :
    ZMod (n + 1) × d ≃ Fin (n + 1) × d :=
  ((zmodAddOneEquiv (n + 1)).prodCongr (Equiv.refl d)) |>.trans
    (rawCyclicColumnEquiv (d := d) n)

omit [Fintype d] [DecidableEq d] in
@[simp] theorem rawCyclicColumnEquiv_symm_apply
    (n : ℕ) (i : Fin (n + 1)) (x : d) :
    (rawCyclicColumnEquiv (d := d) n).symm (i, x) =
      (ZMod.finEquiv (n + 1) i, x) := rfl

omit [Fintype d] [DecidableEq d] in
@[simp] theorem rawCyclicTargetRowEquiv_symm_zero
    (n : ℕ) (x : d) :
    (rawCyclicTargetRowEquiv (d := d) n).symm (0, x) =
      (ZMod.finEquiv (n + 1) (Fin.last n), x) := by
  apply (rawCyclicTargetRowEquiv (d := d) n).injective
  rw [(rawCyclicTargetRowEquiv (d := d) n).apply_symm_apply]
  simp [rawCyclicTargetRowEquiv, rawCyclicColumnEquiv, zmodAddOneEquiv]

omit [Fintype d] [DecidableEq d] in
@[simp] theorem rawCyclicTargetRowEquiv_symm_succ
    (n : ℕ) (i : Fin n) (x : d) :
    (rawCyclicTargetRowEquiv (d := d) n).symm (i.succ, x) =
      (ZMod.finEquiv (n + 1) i.castSucc, x) := by
  apply (rawCyclicTargetRowEquiv (d := d) n).injective
  rw [(rawCyclicTargetRowEquiv (d := d) n).apply_symm_apply]
  simp [rawCyclicTargetRowEquiv, rawCyclicColumnEquiv, zmodAddOneEquiv]

private theorem zmod_finEquiv_last_add_one (n : ℕ) :
    ZMod.finEquiv (n + 1) (Fin.last n) + 1 =
      ZMod.finEquiv (n + 1) 0 := by
  change (Fin.last n + 1 : Fin (n + 1)) = 0
  exact Fin.last_add_one n

private theorem zmod_finEquiv_castSucc_add_one
    (n : ℕ) (i : Fin n) :
    ZMod.finEquiv (n + 1) i.castSucc + 1 =
      ZMod.finEquiv (n + 1) i.succ := by
  change (i.castSucc + 1 : Fin (n + 1)) = i.succ
  apply Fin.ext
  rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last i)]
  rfl

private theorem zmod_finEquiv_eq_last_add_one_iff
    (n : ℕ) (j : Fin (n + 1)) :
    ZMod.finEquiv (n + 1) j =
        ZMod.finEquiv (n + 1) (Fin.last n) + 1 ↔
      (0 : Fin (n + 1)) = j := by
  rw [zmod_finEquiv_last_add_one]
  exact (ZMod.finEquiv (n + 1)).injective.eq_iff.trans eq_comm

private theorem zmod_finEquiv_eq_castSucc_add_one_iff
    (n : ℕ) (i : Fin n) (j : Fin (n + 1)) :
    ZMod.finEquiv (n + 1) j =
        ZMod.finEquiv (n + 1) i.castSucc + 1 ↔
      i.succ = j := by
  rw [zmod_finEquiv_castSucc_add_one]
  exact (ZMod.finEquiv (n + 1)).injective.eq_iff.trans eq_comm

/-- After the target-row shift and the standard finite column ordering, the
raw `ZMod` system is exactly the finite identity-diagonal cyclic system. -/
theorem rawCyclicTransferSystem_reindex
    (n : ℕ) (T : ZMod (n + 1) → Matrix d d R) :
    Matrix.reindex (rawCyclicTargetRowEquiv (d := d) n)
        (rawCyclicColumnEquiv (d := d) n)
        (rawCyclicTransferSystem (n + 1) T) =
      finShiftedCyclicSystem n
        (fun i => T (ZMod.finEquiv (n + 1) i)) := by
  classical
  ext ⟨i, x⟩ ⟨j, y⟩
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Matrix.reindex_apply, rawCyclicTransferSystem,
      finShiftedCyclicSystem, zmod_finEquiv_eq_last_add_one_iff,
      Matrix.one_apply]
  · simp [Matrix.reindex_apply, rawCyclicTransferSystem,
      finShiftedCyclicSystem, zmod_finEquiv_eq_castSucc_add_one_iff,
      Matrix.one_apply]

/-- The explicit row/column permutation sign used to pass from raw cyclic
sites to the identity-diagonal finite cycle. -/
def rawCyclicMonodromySign (R : Type*) [CommRing R] (n : ℕ) : R :=
  (Equiv.Perm.sign
    ((rawCyclicColumnEquiv (d := d) n).trans
      (rawCyclicTargetRowEquiv (d := d) n).symm) : R)

theorem rawCyclicMonodromySign_spec (n : ℕ) :
    rawCyclicMonodromySign R (d := d) n = 1 ∨
      rawCyclicMonodromySign R (d := d) n = -1 := by
  rcases Int.units_eq_one_or
      (Equiv.Perm.sign
        ((rawCyclicColumnEquiv (d := d) n).trans
          (rawCyclicTargetRowEquiv (d := d) n).symm)) with h | h
  · left
    simp [rawCyclicMonodromySign, h]
  · right
    simp [rawCyclicMonodromySign, h]

/-- Exact raw cyclic determinant-to-monodromy formula, including the
deterministic target-row permutation sign. -/
theorem rawCyclicTransferSystem_det
    (n : ℕ) (T : ZMod (n + 1) → Matrix d d R) :
    (rawCyclicTransferSystem (n + 1) T).det =
      rawCyclicMonodromySign R (d := d) n *
        (1 - chronologicalProduct
          (List.ofFn fun i => T (ZMod.finEquiv (n + 1) i))).det := by
  have hreindex := Matrix.det_reindex
    (rawCyclicTargetRowEquiv (d := d) n)
    (rawCyclicColumnEquiv (d := d) n)
    (rawCyclicTransferSystem (n + 1) T)
  rw [rawCyclicTransferSystem_reindex] at hreindex
  rw [finShiftedCyclicSystem_det] at hreindex
  change
    (1 - chronologicalProduct
      (List.ofFn fun i => T (ZMod.finEquiv (n + 1) i))).det =
      rawCyclicMonodromySign R (d := d) n *
        (rawCyclicTransferSystem (n + 1) T).det at hreindex
  have hsquare :
      rawCyclicMonodromySign R (d := d) n *
          rawCyclicMonodromySign R (d := d) n = 1 := by
    rcases rawCyclicMonodromySign_spec (R := R) (d := d) n with h | h <;>
      simp [h]
  calc
    (rawCyclicTransferSystem (n + 1) T).det =
        1 * (rawCyclicTransferSystem (n + 1) T).det := by simp
    _ =
        (rawCyclicMonodromySign R (d := d) n *
          rawCyclicMonodromySign R (d := d) n) *
            (rawCyclicTransferSystem (n + 1) T).det := by rw [hsquare]
    _ = rawCyclicMonodromySign R (d := d) n *
        (rawCyclicMonodromySign R (d := d) n *
          (rawCyclicTransferSystem (n + 1) T).det) := by ring
    _ = rawCyclicMonodromySign R (d := d) n *
        (1 - chronologicalProduct
          (List.ofFn fun i => T (ZMod.finEquiv (n + 1) i))).det := by
      rw [hreindex]

/-- Determinant-level comparison with the existing recursive periodic system.
The recursive system contains two extra identity vertices, but its determinant
is exactly the same monodromy determinant. -/
theorem rawCyclicTransferSystem_det_eq_recursivePeriodicSystem
    (n : ℕ) (T : ZMod (n + 1) → Matrix d d R) :
    (rawCyclicTransferSystem (n + 1) T).det =
      rawCyclicMonodromySign R (d := d) n *
        (recursivePeriodicSystem
          (List.ofFn fun i => T (ZMod.finEquiv (n + 1) i))).det := by
  rw [rawCyclicTransferSystem_det]
  rw [recursivePeriodicSystem_det]

end RawToFinite

section PaperBridge

variable {R : Type*} [Field R]

/-- The paper's chronological list of explicit companion transfers. -/
def paperCyclicTransferList
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R) :
    List (Matrix (Fin (m + 1)) (Fin (m + 1)) R) :=
  List.ofFn fun i : Fin N =>
    paperCyclicTransferMatrix N m βraw a (ZMod.finEquiv N i)

/-- The raw paper companion determinant is now connected, without a
determinant hypothesis, to the existing recursive monodromy system. -/
theorem paperCyclicCompanionState_det_eq_recursivePeriodicSystem
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R) :
    ∃ σ : R, (σ = 1 ∨ σ = -1) ∧
      (cyclicCompanionStateMatrix N m offset
        (paperSparseCyclicLastRow N m βraw a)).det =
        σ * (recursivePeriodicSystem
          (paperCyclicTransferList N m βraw a)).det := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      refine ⟨rawCyclicMonodromySign R (d := Fin (m + 1)) n,
        rawCyclicMonodromySign_spec (R := R) (d := Fin (m + 1)) n, ?_⟩
      rw [cyclicCompanionStateMatrix_eq_rawCyclicTransferSystem]
      unfold paperCyclicTransferList
      convert rawCyclicTransferSystem_det_eq_recursivePeriodicSystem
          (R := R) (d := Fin (m + 1)) n
          (paperCyclicTransferMatrix (n + 1) m βraw a) using 1

/-- Direct monodromy form of the preceding paper-specific bridge. -/
theorem paperCyclicCompanionState_det_eq_monodromy
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R) :
    ∃ σ : R, (σ = 1 ∨ σ = -1) ∧
      (cyclicCompanionStateMatrix N m offset
        (paperSparseCyclicLastRow N m βraw a)).det =
        σ * (1 - chronologicalProduct
          (paperCyclicTransferList N m βraw a)).det := by
  obtain ⟨σ, hσ, hdet⟩ :=
    paperCyclicCompanionState_det_eq_recursivePeriodicSystem
      (R := R) N m offset βraw a
  refine ⟨σ, hσ, ?_⟩
  rw [hdet, recursivePeriodicSystem_det]

/-- Closed periodic determinant formula for the raw band matrix: the earlier
paper-specific physical elimination and the present monodromy elimination are
combined, with both deterministic signs absorbed into one sign. -/
theorem paperCyclicRawBandMatrix_det_eq_monodromy
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (βraw : ZMod N → R) (hβ : ∀ i, βraw i ≠ 0)
    (a : ZMod N → Fin (m + 1) → R) :
    ∃ σ : R, (σ = 1 ∨ σ = -1) ∧
      (paperCyclicRawBandMatrix N m offset βraw a).det =
        σ * (∏ p, paperCyclicOrderedScaling N m offset βraw p) *
          (1 - chronologicalProduct
            (paperCyclicTransferList N m βraw a)).det := by
  obtain ⟨τ, hτ, hstate⟩ :=
    paperCyclicCompanionState_det_eq_monodromy
      (R := R) N m offset βraw a
  refine ⟨paperPeriodicDeterminantSign (R := R) N m offset * τ, ?_, ?_⟩
  · rcases paperPeriodicDeterminantSign_spec (R := R) N m offset with hp | hp <;>
      rcases hτ with ht | ht <;> simp [hp, ht]
  · rw [paperCyclicRawBandMatrix_det (R := R) N m offset βraw hβ a,
      hstate]
    ring

end PaperBridge

end CircularLawSection4
