import BernoulliLinearAlgebra.BlockFloquet
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Prod.Lex
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# A concrete finite cyclic transfer system

This is the concrete determinant calculation for Lemma 7.6, whose proof
is in Section 9.3 of arXiv:2609.01295v1.

This file removes the abstract periodic-elimination input from the transfer
half of the Block Floquet calculation.  For `m + 1` transfer steps, columns are
ordered as

`(s₁, ..., sₘ | s₀)`

and rows as the actual equations

`s_{j+1} - T_j s_j = 0`.

In this ordering the first `m` block columns form a unit lower-bidiagonal
pivot.  Its Schur complement is exactly `I - T_m ... T_0`.  Thus the theorem
`rotatedPeriodicTransfer_det` is a concrete periodic determinant theorem and
does not accept a `PeriodicEliminationCertificate`.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix

section ReverseProducts

variable {S : Type*} [Monoid S]

/-- The product through site `j`, in chronological transfer order:
`T_j * ... * T_0`.  `MulOpposite` lets us reuse mathlib's partial products
without assuming that the matrices commute. -/
def reversePrefixProduct {q : ℕ} (T : Fin q → S) (j : Fin q) : S :=
  MulOpposite.unop
    (Fin.partialProd (fun i ↦ MulOpposite.op (T i)) j.succ)

@[simp] theorem reversePrefixProduct_zero {q : ℕ} (T : Fin (q + 1) → S) :
    reversePrefixProduct T 0 = T 0 := by
  simp [reversePrefixProduct, Fin.partialProd]

theorem reversePrefixProduct_succ {q : ℕ} (T : Fin (q + 1) → S)
    (j : Fin q) :
    reversePrefixProduct T j.succ =
      T j.succ * reversePrefixProduct T (Fin.castSucc j) := by
  unfold reversePrefixProduct
  rw [Fin.partialProd_succ (fun i ↦ MulOpposite.op (T i)) j.succ]
  simp only [MulOpposite.unop_mul, MulOpposite.unop_op]
  congr 2

/-- The finite-family form agrees with the list convention used in
`BlockFloquet`: `[T₀,...,Tₘ]` is multiplied as `Tₘ⋯T₀`. -/
theorem chronologicalProduct_eq_unop_prod {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n]
    (Ts : List (Matrix n n R)) :
    chronologicalProduct Ts =
      MulOpposite.unop ((Ts.map MulOpposite.op).prod) := by
  induction Ts with
  | nil => rfl
  | cons T Ts ih =>
      simp only [chronologicalProduct_cons, List.map_cons, List.prod_cons,
        MulOpposite.unop_mul, MulOpposite.unop_op]
      rw [ih]

theorem reversePrefixProduct_last_eq_chronologicalProduct
    {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n] {q : ℕ}
    (T : Fin (q + 1) → Matrix n n R) :
    reversePrefixProduct T (Fin.last q) =
      chronologicalProduct (List.ofFn T) := by
  rw [chronologicalProduct_eq_unop_prod]
  unfold reversePrefixProduct Fin.partialProd
  rw [(List.take_eq_self_iff _).mpr (by simp)]
  simp only [List.map_ofFn, Function.comp_def]

end ReverseProducts

section ConcretePeriodicSystem

variable {R : Type*} [CommRing R]
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
variable {m : ℕ}

/-- The unit lower-bidiagonal pivot obtained from the first `m` periodic
transfer equations.  Its block rows are equations `0,...,m-1`; its block
columns are states `s₁,...,sₘ`. -/
def openTransferPivotBlocks (T : Fin (m + 1) → Matrix n n R) :
    Matrix (Fin m) (Fin m) (Matrix n n R) := fun i j ↦
  if i = j then 1
  else if i.val = j.val + 1 then -(T (Fin.castSucc i))
  else 0

/-- Scalar expansion of `openTransferPivotBlocks`. -/
def openTransferPivot (T : Fin (m + 1) → Matrix n n R) :
    Matrix (Fin m × n) (Fin m × n) R :=
  Matrix.comp _ _ _ _ _ (openTransferPivotBlocks T)

/-- The column involving the cyclic initial state `s₀` in the first `m`
equations. -/
def initialTransferColumn (T : Fin (m + 1) → Matrix n n R) :
    Matrix (Fin m × n) n R := fun i b ↦
  if i.1.val = 0 then -(T 0) i.2 b else 0

/-- The final periodic equation contains `-T_m s_m`. -/
def terminalTransferRow (T : Fin (m + 1) → Matrix n n R) :
    Matrix n (Fin m × n) R := fun a j ↦
  if j.1.val + 1 = m then -(T (Fin.last m)) a j.2 else 0

/-- The actual cyclic first-order coefficient matrix, with columns rotated to
`(s₁,...,sₘ | s₀)`. -/
def rotatedPeriodicTransferSystem (T : Fin (m + 1) → Matrix n n R) :
    Matrix ((Fin m × n) ⊕ n) ((Fin m × n) ⊕ n) R :=
  Matrix.fromBlocks (openTransferPivot T) (initialTransferColumn T)
    (terminalTransferRow T) 1

/-- The same pivot equipped with the lexicographic order on its scalar
indices. -/
def lexOpenTransferPivot (T : Fin (m + 1) → Matrix n n R) :
    Matrix (Fin m ×ₗ n) (Fin m ×ₗ n) R := fun i j ↦
  openTransferPivot T (ofLex i) (ofLex j)

omit [Fintype n] in
/-- The open-chain pivot is lower triangular at the scalar level. -/
theorem lexOpenTransferPivot_isLowerTriangular
    (T : Fin (m + 1) → Matrix n n R) :
    (lexOpenTransferPivot T).IsLowerTriangular := by
  rintro ia jb hij
  rw [OrderDual.toDual_lt_toDual] at hij
  rcases Prod.Lex.lt_iff.mp hij with hij | hij
  · simp only [lexOpenTransferPivot, openTransferPivot, Matrix.comp_apply,
      openTransferPivotBlocks]
    rw [if_neg (ne_of_lt hij)]
    rw [if_neg (by intro hstep; omega)]
    rfl
  · rcases hij with ⟨hij, hab⟩
    simp only [lexOpenTransferPivot, openTransferPivot, Matrix.comp_apply,
      openTransferPivotBlocks]
    rw [if_pos hij]
    simp [ne_of_lt hab]

@[simp] theorem openTransferPivot_det
    (T : Fin (m + 1) → Matrix n n R) :
    (openTransferPivot T).det = 1 := by
  let e : (Fin m × n) ≃ (Fin m ×ₗ n) := toLex
  rw [← Matrix.det_reindex_self e (openTransferPivot T)]
  change (lexOpenTransferPivot T).det = 1
  rw [Matrix.det_of_isLowerTriangular _ (lexOpenTransferPivot_isLowerTriangular T)]
  simp [lexOpenTransferPivot, openTransferPivot, openTransferPivotBlocks,
    Matrix.comp_apply]

/-- The explicit open-chain solution column.  Its `i`-th block is
`-(T_i ... T_0)`. -/
def openChainSolution (T : Fin (m + 1) → Matrix n n R) :
    Matrix (Fin m × n) n R := fun i b ↦
  -(reversePrefixProduct T (Fin.castSucc i.1)) i.2 b

/-- Block-column version of `openChainSolution`. -/
def openChainSolutionBlocks (T : Fin (m + 1) → Matrix n n R) :
    Matrix (Fin m) PUnit.{1} (Matrix n n R) := fun i _ ↦
  -(reversePrefixProduct T (Fin.castSucc i))

/-- Block-column version of `initialTransferColumn`. -/
def initialTransferColumnBlocks (T : Fin (m + 1) → Matrix n n R) :
    Matrix (Fin m) PUnit.{1} (Matrix n n R) := fun i _ ↦
  if i.val = 0 then -(T 0) else 0

/-- Expand a block column and remove its dummy `PUnit` column index. -/
def expandBlockColumn (M : Matrix (Fin m) PUnit.{1} (Matrix n n R)) :
    Matrix (Fin m × n) n R :=
  Matrix.reindex (Equiv.refl (Fin m × n)) (Equiv.punitProd n)
    (Matrix.comp _ _ _ _ _ M)

omit [LinearOrder n] in
theorem openChainSolution_eq_expandBlockColumn
    (T : Fin (m + 1) → Matrix n n R) :
    openChainSolution T = expandBlockColumn (openChainSolutionBlocks T) := by
  ext i b
  rfl

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
theorem initialTransferColumn_eq_expandBlockColumn
    (T : Fin (m + 1) → Matrix n n R) :
    initialTransferColumn T =
      expandBlockColumn (initialTransferColumnBlocks T) := by
  ext i b
  by_cases h : i.1.val = 0 <;>
    simp [initialTransferColumn, expandBlockColumn,
      initialTransferColumnBlocks, Matrix.reindex_apply, h]

omit [DecidableEq n] [LinearOrder n] in
/-- Scalar expansion commutes with multiplication of a square block matrix
and a block column. -/
theorem comp_mul_expandBlockColumn
    (A : Matrix (Fin m) (Fin m) (Matrix n n R))
    (B : Matrix (Fin m) PUnit.{1} (Matrix n n R)) :
    Matrix.comp _ _ _ _ _ A * expandBlockColumn B =
      expandBlockColumn (A * B) := by
  apply Matrix.ext
  rintro ⟨i, a⟩ b
  simp [expandBlockColumn, Matrix.mul_apply, Matrix.reindex_apply,
    Fintype.sum_prod_type]
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.mul_apply]

omit [LinearOrder n] in
/-- Forward substitution in the unit lower-bidiagonal pivot. -/
theorem openTransferPivotBlocks_mul_openChainSolutionBlocks
    (T : Fin (m + 1) → Matrix n n R) :
    openTransferPivotBlocks T * openChainSolutionBlocks T =
      initialTransferColumnBlocks T := by
  apply Matrix.ext
  intro i u
  cases u
  simp only [Matrix.mul_apply, openTransferPivotBlocks,
    openChainSolutionBlocks, initialTransferColumnBlocks]
  by_cases hi : i.val = 0
  · let z : Fin m := ⟨0, by omega⟩
    have hi0 : i = z := Fin.ext hi
    rw [hi0]
    simp [z, reversePrefixProduct_zero]
  · let p : Fin m := ⟨i.val - 1, by omega⟩
    have hp : i.val = p.val + 1 := by simp [p]; omega
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hrest :
        ∑ x ∈ Finset.univ.erase i,
            (if i = x then 1
             else if i.val = x.val + 1 then -(T (Fin.castSucc i)) else 0) *
              -reversePrefixProduct T (Fin.castSucc x) =
          -(T (Fin.castSucc i)) *
            -reversePrefixProduct T (Fin.castSucc p) := by
      rw [Finset.sum_eq_single p]
      · simp [hp, show i ≠ p by omega]
      · intro j hj hji
        have hji' : i ≠ j := by
          exact (Finset.mem_erase.mp hj).1.symm
        simp only [if_neg hji']
        rw [if_neg]
        · simp
        · intro heq
          apply hji
          apply Fin.ext
          simp [p]
          omega
      · simp [show p ≠ i by omega]
    rw [hrest]
    have hipSucc : Fin.castSucc i = p.succ := Fin.ext hp
    rw [hipSucc]
    rw [reversePrefixProduct_succ T p]
    simp [hi]

omit [LinearOrder n] in
/-- Scalar expansion of forward substitution. -/
theorem openTransferPivot_mul_openChainSolution
    (T : Fin (m + 1) → Matrix n n R) :
    openTransferPivot T * openChainSolution T = initialTransferColumn T := by
  rw [openChainSolution_eq_expandBlockColumn,
    initialTransferColumn_eq_expandBlockColumn]
  rw [openTransferPivot, comp_mul_expandBlockColumn]
  rw [openTransferPivotBlocks_mul_openChainSolutionBlocks]

/-- The explicit solution column is `A⁻¹B`; no transfer matrix is inverted in
this statement. -/
theorem openTransferPivot_inv_mul_initialTransferColumn
    (T : Fin (m + 1) → Matrix n n R) :
    (openTransferPivot T)⁻¹ * initialTransferColumn T =
      openChainSolution T := by
  have hA : IsUnit (openTransferPivot T).det := by simp
  calc
    (openTransferPivot T)⁻¹ * initialTransferColumn T =
        (openTransferPivot T)⁻¹ *
          (openTransferPivot T * openChainSolution T) := by
            rw [openTransferPivot_mul_openChainSolution]
    _ = ((openTransferPivot T)⁻¹ * openTransferPivot T) *
          openChainSolution T := by rw [Matrix.mul_assoc]
    _ = openChainSolution T := by rw [Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]

omit [LinearOrder n] in
/-- Closing the last equation against the forward solution produces the full
monodromy.  The hypothesis merely excludes the degenerate one-site encoding,
where predecessor and successor coincide in the same block entry. -/
theorem terminalTransferRow_mul_openChainSolution
    (T : Fin (m + 1) → Matrix n n R) (hm : 0 < m) :
    terminalTransferRow T * openChainSolution T =
      reversePrefixProduct T (Fin.last m) := by
  apply Matrix.ext
  intro a b
  simp only [Matrix.mul_apply, terminalTransferRow, openChainSolution,
    Fintype.sum_prod_type]
  let l : Fin m := ⟨m - 1, by omega⟩
  have hl : l.val + 1 = m := by simp [l]; omega
  rw [Finset.sum_eq_single l]
  · simp only [if_pos hl]
    change ((-(T (Fin.last m))) *
      (-(reversePrefixProduct T (Fin.castSucc l)))) a b = _
    rw [neg_mul, mul_neg, neg_neg]
    have hlast : l.succ = Fin.last m := by
      apply Fin.ext
      simp [l]
      omega
    rw [← hlast, reversePrefixProduct_succ T l]
  · intro j hj hjl
    have hne : j.val + 1 ≠ m := by
      intro h
      apply hjl
      apply Fin.ext
      simp [l]
      omega
    simp [hne]
  · simp

/-- Concrete periodic transfer determinant.  This is the second elimination
of Section 9.3 with the matrix and the identity pivots fully displayed; it has
no elimination-certificate argument. -/
theorem rotatedPeriodicTransfer_det
    (T : Fin (m + 1) → Matrix n n R) (hm : 0 < m) :
    (rotatedPeriodicTransferSystem T).det =
      (1 - reversePrefixProduct T (Fin.last m)).det := by
  have hA : IsUnit (openTransferPivot T).det := by simp
  let _ : Invertible (openTransferPivot T) :=
    (openTransferPivot T).invertibleOfIsUnitDet hA
  rw [rotatedPeriodicTransferSystem, Matrix.det_fromBlocks₁₁]
  rw [openTransferPivot_det, one_mul]
  rw [Matrix.invOf_eq_nonsing_inv]
  rw [Matrix.mul_assoc, openTransferPivot_inv_mul_initialTransferColumn]
  rw [terminalTransferRow_mul_openChainSolution T hm]

/-- List-order form of the concrete periodic determinant. -/
theorem rotatedPeriodicTransfer_det_chronological
    (T : Fin (m + 1) → Matrix n n R) (hm : 0 < m) :
    (rotatedPeriodicTransferSystem T).det =
      (1 - chronologicalProduct (List.ofFn T)).det := by
  rw [rotatedPeriodicTransfer_det T hm,
    reversePrefixProduct_last_eq_chronologicalProduct]

section RawOrdering

/-- Cyclic successor of a site: the last site wraps to zero. -/
def periodicSiteSucc : Equiv.Perm (Fin (m + 1)) :=
  finSuccEquivLast.trans (finSuccEquiv m).symm

@[simp] theorem periodicSiteSucc_last :
    periodicSiteSucc (m := m) (Fin.last m) = 0 := by
  simp [periodicSiteSucc]

@[simp] theorem periodicSiteSucc_castSucc (i : Fin m) :
    periodicSiteSucc (m := m) (Fin.castSucc i) = i.succ := by
  simp [periodicSiteSucc]

/-- For at least two sites, cyclic successor has no fixed point.  The
one-site encoding is deliberately excluded throughout the concrete Floquet
formula because its predecessor and successor contributions occupy the same
matrix entry. -/
theorem periodicSiteSucc_ne_self (hm : 0 < m) (j : Fin (m + 1)) :
    periodicSiteSucc (m := m) j ≠ j := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp [hm.ne']
  · intro h
    have hv := congrArg Fin.val h
    simp at hv

/-- Row ordering map: the open equations come first and the last periodic
equation comes last. -/
def periodicRowMap (x : (Fin m × n) ⊕ n) : Fin (m + 1) × n :=
  match x with
  | Sum.inl ja => (Fin.castSucc ja.1, ja.2)
  | Sum.inr a => (Fin.last m, a)

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
theorem periodicRowMap_bijective :
    Function.Bijective (periodicRowMap (m := m) (n := n)) := by
  constructor
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        simp only [periodicRowMap, Prod.mk.injEq, Fin.castSucc_inj] at h
        exact congrArg Sum.inl (Prod.ext h.1 h.2)
      | inr y =>
        simp only [periodicRowMap, Prod.mk.injEq] at h
        exact (Fin.castSucc_ne_last x.1 h.1).elim
    | inr x =>
      cases y with
      | inl y =>
        simp only [periodicRowMap, Prod.mk.injEq] at h
        exact (Fin.castSucc_ne_last y.1 h.1.symm).elim
      | inr y =>
        simp only [periodicRowMap, Prod.mk.injEq, true_and] at h
        exact congrArg Sum.inr h
  · rintro ⟨j, a⟩
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · exact ⟨Sum.inr a, rfl⟩
    · exact ⟨Sum.inl (i, a), rfl⟩

/-- Equivalence implementing the row ordering. -/
def periodicRowEquiv : ((Fin m × n) ⊕ n) ≃ (Fin (m + 1) × n) :=
  Equiv.ofBijective periodicRowMap periodicRowMap_bijective

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
@[simp] theorem periodicRowEquiv_symm_castSucc (i : Fin m) (a : n) :
    (periodicRowEquiv (m := m) (n := n)).symm (Fin.castSucc i, a) =
      Sum.inl (i, a) := by
  apply (periodicRowEquiv (m := m) (n := n)).symm_apply_eq.mpr
  rfl

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
@[simp] theorem periodicRowEquiv_symm_last (a : n) :
    (periodicRowEquiv (m := m) (n := n)).symm (Fin.last m, a) =
      Sum.inr a := by
  apply (periodicRowEquiv (m := m) (n := n)).symm_apply_eq.mpr
  rfl

/-- Column ordering map: `(s₁,...,sₘ | s₀)` is rotated back to
`(s₀,...,sₘ)`. -/
def periodicColumnMap (x : (Fin m × n) ⊕ n) : Fin (m + 1) × n :=
  match x with
  | Sum.inl ja => (ja.1.succ, ja.2)
  | Sum.inr a => (0, a)

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
theorem periodicColumnMap_bijective :
    Function.Bijective (periodicColumnMap (m := m) (n := n)) := by
  constructor
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        simp only [periodicColumnMap, Prod.mk.injEq, Fin.succ_inj] at h
        exact congrArg Sum.inl (Prod.ext h.1 h.2)
      | inr y =>
        simp only [periodicColumnMap, Prod.mk.injEq] at h
        exact (Fin.succ_ne_zero x.1 h.1).elim
    | inr x =>
      cases y with
      | inl y =>
        simp only [periodicColumnMap, Prod.mk.injEq] at h
        exact (Fin.succ_ne_zero y.1 h.1.symm).elim
      | inr y =>
        simp only [periodicColumnMap, Prod.mk.injEq, true_and] at h
        exact congrArg Sum.inr h
  · rintro ⟨j, a⟩
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · exact ⟨Sum.inr a, rfl⟩
    · exact ⟨Sum.inl (i, a), rfl⟩

/-- Equivalence implementing the column rotation. -/
def periodicColumnEquiv : ((Fin m × n) ⊕ n) ≃ (Fin (m + 1) × n) :=
  Equiv.ofBijective periodicColumnMap periodicColumnMap_bijective

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
@[simp] theorem periodicColumnEquiv_symm_zero (a : n) :
    (periodicColumnEquiv (m := m) (n := n)).symm (0, a) =
      Sum.inr a := by
  apply (periodicColumnEquiv (m := m) (n := n)).symm_apply_eq.mpr
  rfl

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
@[simp] theorem periodicColumnEquiv_symm_succ (i : Fin m) (a : n) :
    (periodicColumnEquiv (m := m) (n := n)).symm (i.succ, a) =
      Sum.inl (i, a) := by
  apply (periodicColumnEquiv (m := m) (n := n)).symm_apply_eq.mpr
  rfl

/-- The periodic transfer system in the literal site order
`(s₀,...,sₘ)`, for both equations and states. -/
def rawPeriodicTransferSystem (T : Fin (m + 1) → Matrix n n R) :
    Matrix (Fin (m + 1) × n) (Fin (m + 1) × n) R :=
  Matrix.reindex periodicRowEquiv periodicColumnEquiv
    (rotatedPeriodicTransferSystem T)

omit [Fintype n] [LinearOrder n] in
/-- Entrywise form of the literal periodic equations:
`s_{j+1} - T_j s_j`. -/
theorem rawPeriodicTransferSystem_apply
    (T : Fin (m + 1) → Matrix n n R)
    (hm : 0 < m) (j k : Fin (m + 1)) (a b : n) :
    rawPeriodicTransferSystem T (j, a) (k, b) =
      (if k = periodicSiteSucc j then (1 : Matrix n n R) a b else 0) -
        (if k = j then (T j) a b else 0) := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · refine Fin.cases ?_ (fun p ↦ ?_) k
    · simp [rawPeriodicTransferSystem, Matrix.reindex_apply,
        rotatedPeriodicTransferSystem,
        Matrix.fromBlocks_apply₂₂, hm.ne']
    · simp [rawPeriodicTransferSystem, Matrix.reindex_apply,
        rotatedPeriodicTransferSystem, terminalTransferRow,
        Matrix.fromBlocks_apply₂₁, Fin.ext_iff]
      by_cases h : p.val + 1 = m
      · simp [h]
      · simp [h]
  · refine Fin.cases ?_ (fun p ↦ ?_) k
    · simp [rawPeriodicTransferSystem, Matrix.reindex_apply,
        rotatedPeriodicTransferSystem, initialTransferColumn,
        Matrix.fromBlocks_apply₁₂, Fin.ext_iff]
      by_cases h : i.val = 0
      · have heq : (Fin.castSucc i : Fin (m + 1)) = 0 := Fin.ext h
        simp [h, heq]
      · simp [h]
        intro hi0
        exact (h hi0.symm).elim
    · simp [rawPeriodicTransferSystem, Matrix.reindex_apply,
        rotatedPeriodicTransferSystem, openTransferPivot,
        openTransferPivotBlocks, Matrix.fromBlocks_apply₁₁, Fin.ext_iff]
      have hstep : p.succ = (Fin.castSucc i : Fin (m + 1)) ↔
          i.val = p.val + 1 := by
        constructor
        · intro h
          have hv := congrArg Fin.val h
          simpa using hv.symm
        · intro h
          exact Fin.ext h.symm
      by_cases hip : i = p
      · simp [hip, eq_comm]
      · have hv : i.val ≠ p.val := fun h ↦ hip (Fin.ext h)
        by_cases hs : i.val = p.val + 1 <;>
          simp [hv, hs, eq_comm]

/-- The sole difference between raw site ordering and elimination ordering is
the explicit sign of the row/column permutation. -/
def periodicOrderingSign : R :=
  (Equiv.Perm.sign
    ((periodicColumnEquiv (m := m) (n := n)).trans
      (periodicRowEquiv (m := m) (n := n)).symm) : ℤ)

omit [LinearOrder n] in
theorem periodicOrderingSign_spec :
    periodicOrderingSign (R := R) (m := m) (n := n) = 1 ∨
      periodicOrderingSign (R := R) (m := m) (n := n) = -1 := by
  unfold periodicOrderingSign
  rcases Int.units_eq_one_or (Equiv.Perm.sign
    ((periodicColumnEquiv (m := m) (n := n)).trans
      (periodicRowEquiv (m := m) (n := n)).symm)) with h | h <;>
    simp [h]

/-- Certificate-free determinant of the literal periodic equations. -/
theorem rawPeriodicTransfer_det
    (T : Fin (m + 1) → Matrix n n R) (hm : 0 < m) :
    (rawPeriodicTransferSystem T).det =
      periodicOrderingSign (R := R) (m := m) (n := n) *
        (1 - chronologicalProduct (List.ofFn T)).det := by
  rw [rawPeriodicTransferSystem, Matrix.det_reindex,
    rotatedPeriodicTransfer_det_chronological T hm]
  rfl

end RawOrdering

section ConcreteAugmented

variable {w : Type*} [Fintype w] [DecidableEq w] [LinearOrder w]

local instance stateSumLinearOrder : LinearOrder (w ⊕ w) :=
  LinearOrder.lift'
    (fun x : w ⊕ w ↦ (toLex x : w ⊕ₗ w)) toLex.injective

/-- Block diagonal in site-first ordering. -/
def siteBlockDiagonal (A : Fin (m + 1) → Matrix n n R) :
    Matrix (Fin (m + 1) × n) (Fin (m + 1) × n) R :=
  Matrix.comp _ _ _ _ _ (Matrix.diagonal A)

omit [LinearOrder n] in
@[simp] theorem siteBlockDiagonal_det
    (A : Fin (m + 1) → Matrix n n R) :
    (siteBlockDiagonal A).det = ∏ j, (A j).det := by
  have h : siteBlockDiagonal A =
      Matrix.reindex (Equiv.prodComm n (Fin (m + 1)))
        (Equiv.prodComm n (Fin (m + 1))) (Matrix.blockDiagonal A) := by
    ext i j
    by_cases hij : i.1 = j.1 <;>
      simp [siteBlockDiagonal, Matrix.comp_apply, Matrix.reindex_apply,
        Matrix.blockDiagonal, Matrix.diagonal, hij]
  rw [h, Matrix.det_reindex_self, Matrix.det_blockDiagonal]

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
/-- Entrywise form of a site-block diagonal matrix. -/
theorem siteBlockDiagonal_apply
    (A : Fin (m + 1) → Matrix n n R)
    (j k : Fin (m + 1)) (a b : n) :
    siteBlockDiagonal A (j, a) (k, b) =
      if j = k then A j a b else 0 := by
  by_cases h : j = k <;>
    simp [siteBlockDiagonal, Matrix.comp_apply, Matrix.diagonal, h]

/-- The literal first-order augmented system
`L_j (s_{j+1} - T_j s_j)=0` in site ordering. -/
def rawCyclicAugmented
    (B D C : Fin (m + 1) → Matrix w w R) :
    Matrix (Fin (m + 1) × (w ⊕ w)) (Fin (m + 1) × (w ⊕ w)) R :=
  siteBlockDiagonal (fun j ↦ stepL (B j)) *
    rawPeriodicTransferSystem (fun j ↦ stepTransfer (B j) (D j) (C j))

/-- The row-factor part of Block Floquet is now concrete: its determinant is
the product of the physical right-interface determinants. -/
theorem rawCyclicAugmented_det
    (B D C : Fin (m + 1) → Matrix w w R) (hm : 0 < m) :
    (rawCyclicAugmented B D C).det =
      periodicOrderingSign (R := R) (m := m) (n := w ⊕ w) *
        (∏ j, (B j).det) *
          (1 - chronologicalProduct
            (List.ofFn fun j ↦ stepTransfer (B j) (D j) (C j))).det := by
  rw [rawCyclicAugmented, Matrix.det_mul, siteBlockDiagonal_det,
    rawPeriodicTransfer_det _ hm]
  simp_rw [stepL_det]
  ring

omit [LinearOrder w] in
/-- On the invertible-interface locus, the raw augmented equations really are
the paper's `K_j s_j + L_j s_{j+1}=0`, since every row block satisfies the
one-step factorization. -/
theorem rawCyclicAugmented_local_factorization
    (B D C : Fin (m + 1) → Matrix w w R)
    (hB : ∀ j, IsUnit (B j).det) (j : Fin (m + 1)) :
    stepK (D j) (C j) + stepL (B j) *
      stepTransfer (B j) (D j) (C j) = 0 :=
  step_factorization_of_isUnit_det _ _ _ (hB j)

omit [LinearOrder w] in
/-- Entrywise actual augmented recurrence on the invertible-interface locus. -/
theorem rawCyclicAugmented_apply
    (B D C : Fin (m + 1) → Matrix w w R)
    (hB : ∀ j, IsUnit (B j).det) (hm : 0 < m)
    (j k : Fin (m + 1)) (s t : w ⊕ w) :
    rawCyclicAugmented B D C (j, s) (k, t) =
      if k = periodicSiteSucc j then (stepL (B j)) s t
      else if k = j then (stepK (D j) (C j)) s t
      else 0 := by
  have hfac := rawCyclicAugmented_local_factorization B D C hB j
  have hk : -(stepL (B j) * stepTransfer (B j) (D j) (C j)) =
      stepK (D j) (C j) := by
    rw [eq_comm]
    exact eq_neg_of_add_eq_zero_left hfac
  have hfix : periodicSiteSucc (m := m) j ≠ j :=
    periodicSiteSucc_ne_self hm j
  simp only [rawCyclicAugmented, Matrix.mul_apply, siteBlockDiagonal,
    Matrix.comp_apply, Matrix.diagonal_apply]
  rw [Fintype.sum_prod_type]
  simp only [rawPeriodicTransferSystem_apply _ hm]
  rw [Finset.sum_eq_single j]
  · by_cases hn : k = periodicSiteSucc j
    · subst k
      simp only [hfix, if_false, if_true, sub_zero]
      change ((stepL (B j) * (1 : Matrix (w ⊕ w) (w ⊕ w) R)) s t) = _
      rw [Matrix.mul_one]
    · by_cases hs : k = j
      · subst k
        simp only [hfix.symm, if_false, if_true, zero_sub]
        change ((stepL (B j) * (-stepTransfer (B j) (D j) (C j))) s t) = _
        rw [Matrix.mul_neg, hk]
      · simp [hn, hs]
  · intro l hl hlj
    simp [hlj.symm]
  · simp

section PhysicalCyclic

/-- Cyclic successor on the block sites. -/
def cyclicSiteSucc : Equiv.Perm (Fin (m + 1)) :=
  periodicSiteSucc

@[simp] theorem cyclicSiteSucc_last :
    cyclicSiteSucc (m := m) (Fin.last m) = 0 := by
  simp [cyclicSiteSucc]

@[simp] theorem cyclicSiteSucc_castSucc (i : Fin m) :
    cyclicSiteSucc (m := m) (Fin.castSucc i) = i.succ := by
  simp [cyclicSiteSucc]

/-- Cyclic successor simultaneously on site and internal coordinate. -/
def cyclicScalarSucc : Equiv.Perm (Fin (m + 1) × w) :=
  (cyclicSiteSucc (m := m)).prodCongr (Equiv.refl w)

/-- The scalar permutation matrix `S`, so `(S ψ)_j = ψ_{j+1}`. -/
def cyclicShift : Matrix (Fin (m + 1) × w) (Fin (m + 1) × w) R :=
  (cyclicScalarSucc (m := m) (w := w)).permMatrix R

omit [LinearOrder w] in
/-- A block diagonal followed by the cyclic shift has precisely the
successor-site block in every row. -/
theorem siteBlockDiagonal_mul_cyclicShift_apply
    (A : Fin (m + 1) → Matrix w w R)
    (j k : Fin (m + 1)) (a b : w) :
    (siteBlockDiagonal A * cyclicShift (R := R) (m := m) (w := w))
        (j, a) (k, b) =
      if k = cyclicSiteSucc j then A j a b else 0 := by
  rw [cyclicShift, PEquiv.mul_toMatrix_toPEquiv]
  simp only [Matrix.submatrix_apply, siteBlockDiagonal, Matrix.comp_apply,
    Matrix.diagonal, cyclicScalarSucc, cyclicSiteSucc]
  by_cases h : k = periodicSiteSucc j
  · subst k
    simp
  · have hs : j ≠ (periodicSiteSucc (m := m)).symm k := by
      intro hj
      apply h
      have hv := congrArg (periodicSiteSucc (m := m)) hj
      simpa using hv.symm
    simp [h, hs]

omit [Fintype w] [LinearOrder w] in
/-- Entrywise form of the cyclic shift itself. -/
theorem cyclicShift_apply
    (j k : Fin (m + 1)) (a b : w) :
    cyclicShift (R := R) (m := m) (w := w) (j, a) (k, b) =
      if k = cyclicSiteSucc j then (1 : Matrix w w R) a b else 0 := by
  by_cases hsk : periodicSiteSucc j = k <;>
    by_cases hab : a = b <;>
      simp [cyclicShift, cyclicScalarSucc, cyclicSiteSucc,
        Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.one_apply,
        Prod.ext_iff, hsk, hab, eq_comm]

omit [LinearOrder w] in
@[simp] theorem cyclicShift_det :
    (cyclicShift (R := R) (m := m) (w := w)).det =
      Equiv.Perm.sign (cyclicScalarSucc (m := m) (w := w)) := by
  simp [cyclicShift]

omit [LinearOrder w] in
theorem cyclicShift_det_isUnit :
    IsUnit (cyclicShift (R := R) (m := m) (w := w)).det := by
  rw [cyclicShift_det]
  rcases Int.units_eq_one_or
    (Equiv.Perm.sign (cyclicScalarSucc (m := m) (w := w))) with h | h <;>
    simp [h]

/-- The literal cyclic three-diagonal physical matrix
`D + B S + C S⁻¹`. -/
def physicalCyclicMatrix
    (B D C : Fin (m + 1) → Matrix w w R) :
    Matrix (Fin (m + 1) × w) (Fin (m + 1) × w) R :=
  siteBlockDiagonal D +
    siteBlockDiagonal B * cyclicShift +
      siteBlockDiagonal C * cyclicShift⁻¹

/-- The explicit `x,y` augmented coefficient matrix from the paper. -/
def explicitCyclicAugmented
    (B D C : Fin (m + 1) → Matrix w w R) :
    Matrix ((Fin (m + 1) × w) ⊕ (Fin (m + 1) × w))
      ((Fin (m + 1) × w) ⊕ (Fin (m + 1) × w)) R :=
  Matrix.fromBlocks
    (siteBlockDiagonal D + siteBlockDiagonal B * cyclicShift)
    (siteBlockDiagonal C)
    (-1)
    cyclicShift

omit [LinearOrder w] in
/-- The first elimination is completely concrete: eliminating the `y`
variables gives exactly the physical cyclic recurrence. -/
theorem explicitCyclicAugmented_det
    (B D C : Fin (m + 1) → Matrix w w R) :
    (explicitCyclicAugmented B D C).det =
      (cyclicShift (R := R) (m := m) (w := w)).det *
        (physicalCyclicMatrix B D C).det := by
  have hS := cyclicShift_det_isUnit (R := R) (m := m) (w := w)
  let _ : Invertible (cyclicShift (R := R) (m := m) (w := w)) :=
    (cyclicShift (R := R) (m := m) (w := w)).invertibleOfIsUnitDet hS
  rw [explicitCyclicAugmented, Matrix.det_fromBlocks₂₂]
  rw [Matrix.invOf_eq_nonsing_inv]
  congr 2
  simp [physicalCyclicMatrix]

/-- Regroup the site-first state space into all `x` variables followed by
all `y` variables.  The same equivalence is used for rows and columns, hence
this reindexing introduces no determinant sign. -/
def siteStateGrouping :
    (Fin (m + 1) × (w ⊕ w)) ≃
      ((Fin (m + 1) × w) ⊕ (Fin (m + 1) × w)) :=
  Equiv.prodSumDistrib _ _ _

omit [LinearOrder w] in
theorem explicitCyclicAugmented_apply₁₁
    (B D C : Fin (m + 1) → Matrix w w R)
    (j k : Fin (m + 1)) (a b : w) :
    explicitCyclicAugmented B D C (Sum.inl (j, a)) (Sum.inl (k, b)) =
      (if j = k then D j a b else 0) +
        (if k = cyclicSiteSucc j then B j a b else 0) := by
  simp only [explicitCyclicAugmented, Matrix.fromBlocks_apply₁₁,
    Matrix.add_apply]
  rw [siteBlockDiagonal_apply, siteBlockDiagonal_mul_cyclicShift_apply]

omit [LinearOrder w] in
theorem explicitCyclicAugmented_apply₁₂
    (B D C : Fin (m + 1) → Matrix w w R)
    (j k : Fin (m + 1)) (a b : w) :
    explicitCyclicAugmented B D C (Sum.inl (j, a)) (Sum.inr (k, b)) =
      if j = k then C j a b else 0 := by
  simp only [explicitCyclicAugmented, Matrix.fromBlocks_apply₁₂]
  rw [siteBlockDiagonal_apply]

omit [LinearOrder w] in
theorem explicitCyclicAugmented_apply₂₁
    (B D C : Fin (m + 1) → Matrix w w R)
    (j k : Fin (m + 1)) (a b : w) :
    explicitCyclicAugmented B D C (Sum.inr (j, a)) (Sum.inl (k, b)) =
      if j = k then (-(1 : Matrix w w R)) a b else 0 := by
  by_cases hjk : j = k
  · subst k
    by_cases hab : a = b <;>
      simp [explicitCyclicAugmented, Matrix.fromBlocks_apply₂₁,
        hab]
  · simp [explicitCyclicAugmented, Matrix.fromBlocks_apply₂₁,
      hjk]

omit [LinearOrder w] in
theorem explicitCyclicAugmented_apply₂₂
    (B D C : Fin (m + 1) → Matrix w w R)
    (j k : Fin (m + 1)) (a b : w) :
    explicitCyclicAugmented B D C (Sum.inr (j, a)) (Sum.inr (k, b)) =
      if k = cyclicSiteSucc j then (1 : Matrix w w R) a b else 0 := by
  simp only [explicitCyclicAugmented, Matrix.fromBlocks_apply₂₂]
  rw [cyclicShift_apply]

omit [LinearOrder w] in
/-- The row-factorized site recurrence is literally the paper's explicit
augmented matrix after regrouping.  The caller supplies only the natural
invertibility hypotheses, never an elimination certificate. -/
theorem reindex_rawCyclicAugmented_eq_explicit
    (B D C : Fin (m + 1) → Matrix w w R)
    (hB : ∀ j, IsUnit (B j).det) (hm : 0 < m) :
    Matrix.reindex siteStateGrouping siteStateGrouping
        (rawCyclicAugmented B D C) =
      explicitCyclicAugmented B D C := by
  ext i k
  rcases i with ⟨j, a⟩ | ⟨j, a⟩ <;>
    rcases k with ⟨k, b⟩ | ⟨k, b⟩
  · change rawCyclicAugmented B D C (j, Sum.inl a) (k, Sum.inl b) = _
    rw [rawCyclicAugmented_apply B D C hB hm,
      explicitCyclicAugmented_apply₁₁]
    have hfix := periodicSiteSucc_ne_self (m := m) hm j
    by_cases hn : k = periodicSiteSucc j
    · subst k
      simp [cyclicSiteSucc, hfix.symm, stepL]
    · simp [cyclicSiteSucc, hn, stepK, eq_comm]
  · change rawCyclicAugmented B D C (j, Sum.inl a) (k, Sum.inr b) = _
    rw [rawCyclicAugmented_apply B D C hB hm,
      explicitCyclicAugmented_apply₁₂]
    have hfix := periodicSiteSucc_ne_self (m := m) hm j
    by_cases hn : k = periodicSiteSucc j
    · subst k
      simp [hfix.symm, stepL]
    · simp [hn, stepK, eq_comm]
  · change rawCyclicAugmented B D C (j, Sum.inr a) (k, Sum.inl b) = _
    rw [rawCyclicAugmented_apply B D C hB hm,
      explicitCyclicAugmented_apply₂₁]
    have hfix := periodicSiteSucc_ne_self (m := m) hm j
    by_cases hn : k = periodicSiteSucc j
    · subst k
      simp [hfix.symm, stepL]
    · simp [hn, stepK, eq_comm]
  · change rawCyclicAugmented B D C (j, Sum.inr a) (k, Sum.inr b) = _
    rw [rawCyclicAugmented_apply B D C hB hm,
      explicitCyclicAugmented_apply₂₂]
    by_cases hn : k = periodicSiteSucc j
    · subst k
      simp [cyclicSiteSucc, stepL]
    · simp [cyclicSiteSucc, hn, stepK, eq_comm]

omit [LinearOrder w] in
/-- Same-order regrouping preserves the augmented determinant exactly. -/
theorem explicitCyclicAugmented_det_eq_raw
    (B D C : Fin (m + 1) → Matrix w w R)
    (hB : ∀ j, IsUnit (B j).det) (hm : 0 < m) :
    (explicitCyclicAugmented B D C).det =
      (rawCyclicAugmented B D C).det := by
  rw [← reindex_rawCyclicAugmented_eq_explicit B D C hB hm]
  exact Matrix.det_reindex_self siteStateGrouping (rawCyclicAugmented B D C)

/-- The complete ordering sign in the physical Floquet formula.  The first
factor is also the inverse shift sign, since every permutation sign squares
to one. -/
def floquetSign : R :=
  (cyclicShift (R := R) (m := m) (w := w)).det *
    periodicOrderingSign (R := R) (m := m) (n := w ⊕ w)

omit [LinearOrder w] in
theorem cyclicShift_det_spec :
    (cyclicShift (R := R) (m := m) (w := w)).det = 1 ∨
      (cyclicShift (R := R) (m := m) (w := w)).det = -1 := by
  rw [cyclicShift_det]
  rcases Int.units_eq_one_or
    (Equiv.Perm.sign (cyclicScalarSucc (m := m) (w := w))) with h | h <;>
    simp [h]

omit [LinearOrder w] in
theorem cyclicShift_det_sq :
    (cyclicShift (R := R) (m := m) (w := w)).det *
        (cyclicShift (R := R) (m := m) (w := w)).det = 1 := by
  rcases cyclicShift_det_spec (R := R) (m := m) (w := w) with h | h <;>
    simp [h]

omit [LinearOrder w] in
theorem floquetSign_spec :
    floquetSign (R := R) (m := m) (w := w) = 1 ∨
      floquetSign (R := R) (m := m) (w := w) = -1 := by
  rcases cyclicShift_det_spec (R := R) (m := m) (w := w) with hs | hs <;>
    rcases periodicOrderingSign_spec
      (R := R) (m := m) (n := w ⊕ w) with hp | hp <;>
      simp [floquetSign, hs, hp]

omit [LinearOrder w] in
theorem floquetSign_sq :
    floquetSign (R := R) (m := m) (w := w) *
        floquetSign (R := R) (m := m) (w := w) = 1 := by
  rcases floquetSign_spec (R := R) (m := m) (w := w) with h | h <;>
    simp [h]

/-- Concrete Block Floquet identity for the actual cyclic three-diagonal
matrix.  It accepts no `FloquetEliminationData` and no reindexing or
factorization certificate: only the mathematically necessary hypotheses
that there are at least two sites and that every right interface block is
invertible. -/
theorem concrete_block_floquet_identity
    (B D C : Fin (m + 1) → Matrix w w R)
    (hB : ∀ j, IsUnit (B j).det) (hm : 0 < m) :
    (physicalCyclicMatrix B D C).det =
      floquetSign (R := R) (m := m) (w := w) *
        (∏ j, (B j).det) *
          (1 - chronologicalProduct
            (List.ofFn fun j ↦ stepTransfer (B j) (D j) (C j))).det := by
  have haug :
      (cyclicShift (R := R) (m := m) (w := w)).det *
          (physicalCyclicMatrix B D C).det =
        periodicOrderingSign (R := R) (m := m) (n := w ⊕ w) *
          (∏ j, (B j).det) *
            (1 - chronologicalProduct
              (List.ofFn fun j ↦ stepTransfer (B j) (D j) (C j))).det := by
    calc
      _ = (explicitCyclicAugmented B D C).det :=
        (explicitCyclicAugmented_det B D C).symm
      _ = (rawCyclicAugmented B D C).det :=
        explicitCyclicAugmented_det_eq_raw B D C hB hm
      _ = _ := rawCyclicAugmented_det B D C hm
  calc
    (physicalCyclicMatrix B D C).det =
        1 * (physicalCyclicMatrix B D C).det := by simp
    _ = ((cyclicShift (R := R) (m := m) (w := w)).det *
          (cyclicShift (R := R) (m := m) (w := w)).det) *
            (physicalCyclicMatrix B D C).det := by
          rw [cyclicShift_det_sq]
    _ = (cyclicShift (R := R) (m := m) (w := w)).det *
          ((cyclicShift (R := R) (m := m) (w := w)).det *
            (physicalCyclicMatrix B D C).det) := by ring
    _ = (cyclicShift (R := R) (m := m) (w := w)).det *
          (periodicOrderingSign (R := R) (m := m) (n := w ⊕ w) *
            (∏ j, (B j).det) *
              (1 - chronologicalProduct
                (List.ofFn fun j ↦ stepTransfer (B j) (D j) (C j))).det) := by
          rw [haug]
    _ = _ := by simp [floquetSign, mul_assoc]

/-- Certificate-free packet/outside split.  If the chronological list is
written with the packet arc first, the closing monodromy is
`R_outside * R_packet`. -/
theorem concrete_block_floquet_packet_split
    (B D C : Fin (m + 1) → Matrix w w R)
    (hB : ∀ j, IsUnit (B j).det) (hm : 0 < m)
    (packet outside : List (Matrix (w ⊕ w) (w ⊕ w) R))
    (htransfers :
      List.ofFn (fun j ↦ stepTransfer (B j) (D j) (C j)) =
        packet ++ outside) :
    (physicalCyclicMatrix B D C).det =
      floquetSign (R := R) (m := m) (w := w) *
        (∏ j, (B j).det) *
          (1 - chronologicalProduct outside *
            chronologicalProduct packet).det := by
  calc
    (physicalCyclicMatrix B D C).det =
        floquetSign (R := R) (m := m) (w := w) *
          (∏ j, (B j).det) *
            (1 - chronologicalProduct
              (List.ofFn fun j ↦ stepTransfer (B j) (D j) (C j))).det :=
      concrete_block_floquet_identity B D C hB hm
    _ = _ := by rw [htransfers, chronologicalProduct_append]

/-- The paper's three-site packet split, with the packet and outside arcs
chosen canonically as `take 3` and `drop 3`. -/
theorem concrete_block_floquet_first_three_split
    (B D C : Fin (m + 1) → Matrix w w R)
    (hB : ∀ j, IsUnit (B j).det) (hm : 0 < m) :
    let transfers :=
      List.ofFn (fun j ↦ stepTransfer (B j) (D j) (C j))
    (physicalCyclicMatrix B D C).det =
      floquetSign (R := R) (m := m) (w := w) *
        (∏ j, (B j).det) *
          (1 - chronologicalProduct (transfers.drop 3) *
            chronologicalProduct (transfers.take 3)).det := by
  let transfers :=
    List.ofFn (fun j ↦ stepTransfer (B j) (D j) (C j))
  exact concrete_block_floquet_packet_split B D C hB hm
    (transfers.take 3) (transfers.drop 3) (List.take_append_drop 3 transfers).symm

/-- A genuinely denominator-free continuation through singular interface
blocks.  This is a determinant of a matrix affine in `B`, `D`, and `C`, up
to a fixed sign, so unlike the total-inverse expression involving
`stepTransfer`, it remains the intended polynomial on the singular locus. -/
def cyclicFloquetPolynomialExtension
    (B D C : Fin (m + 1) → Matrix w w ℂ) : ℂ :=
  floquetSign (R := ℂ) (m := m) (w := w) *
    (physicalCyclicMatrix B D C).det

/-- On the locus where every `B_j` is invertible, the denominator-free
physical polynomial agrees with the determinant-cleared exterior
expression.  No claim is made that the latter total-inverse formula itself
is polynomial at singular `B`; the left side is the global continuation. -/
theorem cyclicFloquetPolynomialExtension_agrees_on_units
    (B D C : Fin (m + 1) → Matrix w w ℂ)
    (hB : ∀ j, IsUnit (B j).det) (hm : 0 < m) :
    cyclicFloquetPolynomialExtension B D C =
      clearedSignedCompoundTrace
        (determinantClearedSteps
          (List.ofFn fun j ↦
            (B j, stepTransfer (B j) (D j) (C j)))) := by
  have hclear :
      clearedSignedCompoundTrace
          (determinantClearedSteps
            (List.ofFn fun j ↦
              (B j, stepTransfer (B j) (D j) (C j)))) =
        (∏ j, (B j).det) *
          (1 - chronologicalProduct
            (List.ofFn fun j ↦ stepTransfer (B j) (D j) (C j))).det := by
    simpa [Fin.prod_univ_succ, Fin.prod_ofFn, Function.comp_def] using
      (determinant_cleared_floquet_exterior_identity
        (xs := List.ofFn fun j ↦
          (B j, stepTransfer (B j) (D j) (C j))))
  rw [cyclicFloquetPolynomialExtension,
    concrete_block_floquet_identity B D C hB hm]
  calc
    floquetSign (R := ℂ) (m := m) (w := w) *
          (floquetSign (R := ℂ) (m := m) (w := w) *
            (∏ j, (B j).det) *
              (1 - chronologicalProduct
                (List.ofFn fun j ↦ stepTransfer (B j) (D j) (C j))).det) =
        (floquetSign (R := ℂ) (m := m) (w := w) *
          floquetSign (R := ℂ) (m := m) (w := w)) *
            ((∏ j, (B j).det) *
              (1 - chronologicalProduct
                (List.ofFn fun j ↦ stepTransfer (B j) (D j) (C j))).det) := by
          ring
    _ = (∏ j, (B j).det) *
          (1 - chronologicalProduct
            (List.ofFn fun j ↦ stepTransfer (B j) (D j) (C j))).det := by
          rw [floquetSign_sq]
          simp
    _ = _ := hclear.symm

end PhysicalCyclic

end ConcreteAugmented

end ConcretePeriodicSystem

end BernoulliLinearAlgebra
