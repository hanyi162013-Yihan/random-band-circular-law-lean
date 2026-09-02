import CircularLawSection4.PeriodicMatrixCertificate
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# State-copy coordinates for the periodic physical elimination

For `N` physical sites and `m + 1` copies of each site, the old state
coordinates are ordered as

* `Sum.inl (j, k)` for the first `m` copies, and
* `Sum.inr j` for the last (physical anchor) copy.

The matrix `differenceAnchorMatrix` sends these coordinates to the `m`
successive differences and the last anchor.  Its determinant is one.  Thus its
nonsingular inverse is a determinant-one column operation, and the
identification equations become an identity block after applying it.
-/

open scoped Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

/-- Indices of the `m` successive differences at `N` physical sites. -/
abbrev StateDifferenceIndex (N m : ℕ) := Fin N ×ₗ Fin m

/-- State-copy coordinates, ordered as the first `m` copies followed by the
last physical anchor.  There are `N * (m + 1)` coordinates. -/
abbrev StateCopyIndex (N m : ℕ) := StateDifferenceIndex N m ⊕ Fin N

section CyclicRelabel

/-- Translation of the state-row index to its physical cyclic index while
retaining the copy number.  With `offset = -W` and zero-based copy number `k`,
this is the paper's relation `j = i - W + k (mod N)`. -/
def cyclicPhysicalPairEquiv (N d : ℕ) (offset : ZMod N) :
    ZMod N × Fin d ≃ ZMod N × Fin d where
  toFun x := (x.1 + offset + (x.2.val : ZMod N), x.2)
  invFun x := (x.1 - offset - (x.2.val : ZMod N), x.2)
  left_inv x := by
    rcases x with ⟨i, k⟩
    apply Prod.ext
    · dsimp
      abel
    · rfl
  right_inv x := by
    rcases x with ⟨j, k⟩
    apply Prod.ext
    · dsimp
      abel
    · rfl

/-- Split `Fin (m+1)` into the first `m` copy numbers and the final anchor. -/
def finSplitLastEquiv (m : ℕ) : Fin (m + 1) ≃ Fin m ⊕ Unit :=
  (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).symm |>.trans
    (Equiv.sumCongr (Equiv.refl _) finOneEquiv)

/-- Reorder copy coordinates so that all differences come first and the
physical anchors come last. -/
def splitStateCopyEquiv (N m : ℕ) :
    Fin N × Fin (m + 1) ≃ StateCopyIndex N m :=
  ((Equiv.refl (Fin N)).prodCongr (finSplitLastEquiv m)) |>.trans
    (Equiv.prodSumDistrib (Fin N) (Fin m) Unit) |>.trans
    (Equiv.sumCongr toLex (Equiv.prodUnique (Fin N) Unit))

/-- Paper-specific cyclic state-copy relabeling.  It sends `(i,k)` to the
copy labelled by the physical site `j = i + offset + k (mod N)`, then splits
off the last copy as the anchor coordinate. -/
def cyclicStateCopyRelabel (N m : ℕ) [NeZero N] (offset : ZMod N) :
    ZMod N × Fin (m + 1) ≃ StateCopyIndex N m :=
  (cyclicPhysicalPairEquiv N (m + 1) offset) |>.trans
    ((ZMod.finEquiv N).symm.toEquiv.prodCongr (Equiv.refl _)) |>.trans
    (splitStateCopyEquiv N m)

@[simp] theorem splitStateCopyEquiv_castSucc
    (N m : ℕ) (j : Fin N) (k : Fin m) :
    splitStateCopyEquiv N m (j, k.castSucc) =
      Sum.inl (toLex (j, k)) := by
  simp [splitStateCopyEquiv, finSplitLastEquiv]

@[simp] theorem splitStateCopyEquiv_last
    (N m : ℕ) (j : Fin N) :
    splitStateCopyEquiv N m (j, Fin.last m) = Sum.inr j := by
  simp [splitStateCopyEquiv, finSplitLastEquiv]

/-- The first `m` state copies are relabelled by the cyclic physical index
`j = i + offset + k`. -/
@[simp] theorem cyclicStateCopyRelabel_castSucc
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (i : ZMod N) (k : Fin m) :
    cyclicStateCopyRelabel N m offset (i, k.castSucc) =
      Sum.inl (toLex
        ((ZMod.finEquiv N).symm (i + offset + (k.val : ZMod N)), k)) := by
  simp [cyclicStateCopyRelabel, cyclicPhysicalPairEquiv]

/-- The last copy is the surviving physical anchor at cyclic site
`j = i + offset + m`. -/
@[simp] theorem cyclicStateCopyRelabel_last
    (N m : ℕ) [NeZero N] (offset : ZMod N) (i : ZMod N) :
    cyclicStateCopyRelabel N m offset (i, Fin.last m) =
      Sum.inr ((ZMod.finEquiv N).symm
        (i + offset + (m : ZMod N))) := by
  simp [cyclicStateCopyRelabel, cyclicPhysicalPairEquiv]

end CyclicRelabel

section DifferenceAnchor

variable {R : Type*} [CommRing R]
variable (N m : ℕ)

/-- The upper-bidiagonal part of the difference transform.  It maps the first
`m` copies to `v_{j,k} - v_{j,k+1}` except that the last difference uses the
separate anchor block. -/
def stateDifferenceBlock :
    Matrix (StateDifferenceIndex N m) (StateDifferenceIndex N m) R :=
  fun r c =>
    if r = c then 1
    else if r.1 = c.1 ∧ c.2.val = r.2.val + 1 then -1
    else 0

/-- The last difference has coefficient `-1` on the physical anchor. -/
def stateAnchorCoupling : Matrix (StateDifferenceIndex N m) (Fin N) R :=
  fun r j => if r.1 = j ∧ r.2.val + 1 = m then -1 else 0

/-- Explicit coordinate transform
`(v_{j,0},...,v_{j,m}) ↦ (v_{j,0}-v_{j,1},...,v_{j,m-1}-v_{j,m},v_{j,m})`,
simultaneously at every physical site. -/
def differenceAnchorMatrix :
    Matrix (StateCopyIndex N m) (StateCopyIndex N m) R :=
  Matrix.fromBlocks (stateDifferenceBlock (R := R) N m)
    (stateAnchorCoupling (R := R) N m) 0 1

theorem stateDifferenceBlock_isUpperTriangular :
    (stateDifferenceBlock (R := R) N m).IsUpperTriangular := by
  intro r c hcr
  rw [stateDifferenceBlock]
  split_ifs with hrc hnext
  · subst c
    exact (lt_irrefl r hcr).elim
  · rcases hnext with ⟨hj, hk⟩
    apply False.elim
    have hcj : c.1 = r.1 := hj.symm
    have hck : r.2 < c.2 := by
      apply Fin.lt_def.2
      omega
    have hrc' : r < c :=
      Prod.Lex.lt_iff.2 (Or.inr ⟨hj, hck⟩)
    exact (asymm hcr hrc').elim
  · rfl

@[simp] theorem stateDifferenceBlock_diag
    (r : StateDifferenceIndex N m) :
    stateDifferenceBlock (R := R) N m r r = 1 := by
  simp [stateDifferenceBlock]

@[simp] theorem stateDifferenceBlock_det :
    (stateDifferenceBlock (R := R) N m).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular
    (stateDifferenceBlock_isUpperTriangular (R := R) N m)]
  simp

@[simp] theorem differenceAnchorMatrix_det :
    (differenceAnchorMatrix (R := R) N m).det = 1 := by
  rw [differenceAnchorMatrix, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- The determinant-one inverse column operation that recovers all state
copies from the differences and anchors. -/
def differenceAnchorRight :
    Matrix (StateCopyIndex N m) (StateCopyIndex N m) R :=
  (differenceAnchorMatrix (R := R) N m)⁻¹

/-- The vector which is one on every state copy of the physical site `j` and
zero on all copies belonging to the other physical sites. -/
def stateCopyAnchorLift (j : Fin N) : StateCopyIndex N m → R
  | Sum.inl r => if r.1 = j then 1 else 0
  | Sum.inr i => if i = j then 1 else 0

@[simp] theorem stateCopyAnchorLift_inl
    (j : Fin N) (r : StateDifferenceIndex N m) :
    stateCopyAnchorLift (R := R) N m j (Sum.inl r) =
      if r.1 = j then 1 else 0 := rfl

@[simp] theorem stateCopyAnchorLift_inr
    (j i : Fin N) :
    stateCopyAnchorLift (R := R) N m j (Sum.inr i) =
      if i = j then 1 else 0 := rfl

private theorem stateDifferenceBlock_mulVec_anchorLift
    (j : Fin N) (r : StateDifferenceIndex N m) :
    (stateDifferenceBlock (R := R) N m).mulVec
        (stateCopyAnchorLift (R := R) N m j ∘ Sum.inl) r =
      if r.2.val + 1 = m then (if r.1 = j then 1 else 0) else 0 := by
  classical
  by_cases hlast : r.2.val + 1 = m
  · have hrow : stateDifferenceBlock (R := R) N m r = Pi.single r 1 := by
      funext c
      by_cases hrc : r = c
      · subst c
        simp [stateDifferenceBlock]
      · have hn : ¬ (r.1 = c.1 ∧ c.2.val = r.2.val + 1) := by
          intro hc
          omega
        simp [stateDifferenceBlock, hrc, hn]
    rw [Matrix.mulVec, hrow, single_dotProduct]
    simp [hlast]
  · have hlt : r.2.val + 1 < m := by omega
    let s : StateDifferenceIndex N m :=
      ⟨r.1, ⟨r.2.val + 1, hlt⟩⟩
    have hs_ne : s ≠ r := by
      intro hsr
      have hv := congrArg (fun x : StateDifferenceIndex N m => x.2.val) hsr
      simp [s] at hv
    have hadj (c : StateDifferenceIndex N m) :
        (r.1 = c.1 ∧ c.2.val = r.2.val + 1) ↔ c = s := by
      constructor
      · rintro ⟨hc1, hc2⟩
        apply Prod.ext
        · simpa [s] using hc1.symm
        · apply Fin.ext
          simpa [s] using hc2
      · rintro rfl
        simp [s]
    have hrow : stateDifferenceBlock (R := R) N m r =
        Pi.single r 1 - Pi.single s 1 := by
      funext c
      by_cases hrc : r = c
      · subst c
        simp [stateDifferenceBlock, hs_ne]
      · by_cases hcs : c = s
        · subst c
          have ha : r.1 = s.1 ∧ s.2.val = r.2.val + 1 :=
            (hadj s).2 rfl
          simp [stateDifferenceBlock, hs_ne.symm, ha]
        · have hn : ¬ (r.1 = c.1 ∧ c.2.val = r.2.val + 1) := by
            intro ha
            exact hcs ((hadj c).1 ha)
          simp [stateDifferenceBlock, hrc, hcs, hn]
    rw [Matrix.mulVec, hrow, sub_dotProduct, single_dotProduct,
      single_dotProduct]
    simp only [one_mul, Function.comp_apply, stateCopyAnchorLift_inl]
    have hs_site : s.1 = r.1 := by rfl
    rw [hs_site]
    simp [hlast]

private theorem stateAnchorCoupling_mulVec_anchorLift
    (j : Fin N) (r : StateDifferenceIndex N m) :
    (stateAnchorCoupling (R := R) N m).mulVec
        (stateCopyAnchorLift (R := R) N m j ∘ Sum.inr) r =
      if r.2.val + 1 = m then -(if r.1 = j then 1 else 0) else 0 := by
  classical
  by_cases hlast : r.2.val + 1 = m
  · have hrow : stateAnchorCoupling (R := R) N m r =
        Pi.single r.1 (-1) := by
      funext i
      by_cases hi : r.1 = i
      · subst i
        simp [stateAnchorCoupling, hlast]
      · simp [stateAnchorCoupling, hi]
    rw [Matrix.mulVec, hrow, single_dotProduct]
    by_cases hrj : r.1 = j <;> simp [hlast, hrj]
  · have hrow : stateAnchorCoupling (R := R) N m r = 0 := by
      funext i
      simp [stateAnchorCoupling, hlast]
    rw [Matrix.mulVec, hrow, zero_dotProduct]
    simp [hlast]

/-- Applying the difference/anchor transform to the lift of a physical site
kills every difference coordinate and leaves the corresponding anchor. -/
theorem differenceAnchorMatrix_mulVec_stateCopyAnchorLift
    (j : Fin N) :
    (differenceAnchorMatrix (R := R) N m).mulVec
        (stateCopyAnchorLift (R := R) N m j) =
      Pi.single (Sum.inr j) 1 := by
  funext c
  rcases c with r | i
  · simp only [differenceAnchorMatrix, fromBlocks_mulVec, Sum.elim_inl,
      Pi.single_apply, Sum.inl_ne_inr, ↓reduceIte, Pi.add_apply]
    rw [stateDifferenceBlock_mulVec_anchorLift,
      stateAnchorCoupling_mulVec_anchorLift]
    by_cases hlast : r.2.val + 1 = m <;> simp [hlast]
  · simp only [differenceAnchorMatrix, fromBlocks_mulVec, Sum.elim_inr,
      Pi.single_apply, Sum.inr.injEq, Pi.add_apply]
    simp [Matrix.zero_mulVec, Matrix.one_mulVec]

@[simp] theorem differenceAnchorRight_det :
    (differenceAnchorRight (R := R) N m).det = 1 := by
  rw [differenceAnchorRight, Matrix.det_nonsing_inv, differenceAnchorMatrix_det]
  simp

theorem differenceAnchorMatrix_mul_right :
    differenceAnchorMatrix (R := R) N m *
        differenceAnchorRight (R := R) N m = 1 := by
  apply Matrix.mul_nonsing_inv
  simp

theorem differenceAnchorRight_mul_matrix :
    differenceAnchorRight (R := R) N m *
        differenceAnchorMatrix (R := R) N m = 1 := by
  apply Matrix.nonsing_inv_mul
  simp

/-- Coefficient matrix of the `N*m` equations
`v_{j,k} - v_{j,k+1} = 0`. -/
def stateIdentificationMatrix :
    Matrix (StateDifferenceIndex N m) (StateCopyIndex N m) R :=
  fun r c => differenceAnchorMatrix (R := R) N m (Sum.inl r) c

/-- After the determinant-one column change, all state-copy identification
equations form the row block `[I, 0]`. -/
theorem stateIdentification_mul_right :
    stateIdentificationMatrix (R := R) N m *
        differenceAnchorRight (R := R) N m =
      fun r c => if c = Sum.inl r then 1 else 0 := by
  ext r c
  have h := congrArg
    (fun M : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R =>
      M (Sum.inl r) c)
    (differenceAnchorMatrix_mul_right (R := R) N m)
  simpa [Matrix.mul_apply, stateIdentificationMatrix, Matrix.one_apply,
    eq_comm] using h

/-- The coordinate transform is bijective on state-coordinate vectors. -/
theorem differenceAnchor_mulVec_bijective :
    Function.Bijective
      (fun v : StateCopyIndex N m → R =>
        (differenceAnchorMatrix (R := R) N m).mulVec v) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have h := congrArg
      (fun z => (differenceAnchorRight (R := R) N m).mulVec z) hxy
    change
      (differenceAnchorRight (R := R) N m).mulVec
          ((differenceAnchorMatrix (R := R) N m).mulVec x) =
        (differenceAnchorRight (R := R) N m).mulVec
          ((differenceAnchorMatrix (R := R) N m).mulVec y) at h
    rw [Matrix.mulVec_mulVec,
      differenceAnchorRight_mul_matrix (R := R) N m,
      Matrix.one_mulVec] at h
    rw [Matrix.mulVec_mulVec,
      differenceAnchorRight_mul_matrix (R := R) N m,
      Matrix.one_mulVec] at h
    exact h
  · intro y
    refine ⟨(differenceAnchorRight (R := R) N m).mulVec y, ?_⟩
    change
      (differenceAnchorMatrix (R := R) N m).mulVec
          ((differenceAnchorRight (R := R) N m).mulVec y) = y
    rw [Matrix.mulVec_mulVec,
      differenceAnchorMatrix_mul_right (R := R) N m,
      Matrix.one_mulVec]

/-- The anchor column of the inverse difference transform is one on every
copy of that physical site and zero on every other state copy. -/
theorem differenceAnchorRight_anchorColumn
    (j : Fin N) :
    (differenceAnchorRight (R := R) N m).col (Sum.inr j) =
      stateCopyAnchorLift (R := R) N m j := by
  apply (differenceAnchor_mulVec_bijective (R := R) N m).1
  change
    (differenceAnchorMatrix (R := R) N m).mulVec
        ((differenceAnchorRight (R := R) N m).col (Sum.inr j)) =
      (differenceAnchorMatrix (R := R) N m).mulVec
        (stateCopyAnchorLift (R := R) N m j)
  rw [differenceAnchorMatrix_mulVec_stateCopyAnchorLift]
  rw [← Matrix.mulVec_single_one]
  rw [Matrix.mulVec_mulVec,
    differenceAnchorMatrix_mul_right (R := R) N m,
    Matrix.one_mulVec]

end DifferenceAnchor

section OrderedPhysicalCertificate

variable {R : Type*} [CommRing R]
variable (N m : ℕ)

/-- The physical block left after applying the difference/anchor column
change to an already reindexed state matrix. -/
def stateCopyPhysicalBlock
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R) :
    Matrix (Fin N) (Fin N) R :=
  fun i j =>
    (state * differenceAnchorRight (R := R) N m) (Sum.inr i) (Sum.inr j)

/-- Coefficients of the difference variables in the remaining `N` equations,
after the difference/anchor column change. -/
def stateCopyResidualBlock
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R) :
    Matrix (Fin N) (StateDifferenceIndex N m) R :=
  fun i r =>
    (state * differenceAnchorRight (R := R) N m) (Sum.inr i) (Sum.inl r)

/-- Determinant-one row operation clearing the remaining occurrences of the
difference variables from the last `N` equations. -/
def stateCopyPhysicalLeft
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R) :
    Matrix (StateCopyIndex N m) (StateCopyIndex N m) R :=
  Matrix.fromBlocks 1 0 (-(stateCopyResidualBlock (R := R) N m state)) 1

@[simp] theorem stateCopyPhysicalLeft_det
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R) :
    (stateCopyPhysicalLeft (R := R) N m state).det = 1 := by
  rw [stateCopyPhysicalLeft, Matrix.det_fromBlocks_zero₁₂]
  simp

/-- If the first `N*m` rows of `state` are exactly the state-copy
identifications, the difference/anchor inverse turns `state` into the block
matrix `[I,0; C,physical]`. -/
theorem state_mul_differenceAnchorRight_eq
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R)
    (hident : ∀ r c,
      state (Sum.inl r) c = stateIdentificationMatrix (R := R) N m r c) :
    state * differenceAnchorRight (R := R) N m =
      Matrix.fromBlocks 1 0
        (stateCopyResidualBlock (R := R) N m state)
        (stateCopyPhysicalBlock (R := R) N m state) := by
  ext i j
  rcases i with r | i <;> rcases j with c | j
  · rw [Matrix.mul_apply]
    simp_rw [hident]
    have h := congrArg
      (fun M : Matrix (StateDifferenceIndex N m) (StateCopyIndex N m) R =>
        M r (Sum.inl c))
      (stateIdentification_mul_right (R := R) N m)
    simpa [Matrix.mul_apply, Matrix.one_apply, eq_comm] using h
  · rw [Matrix.mul_apply]
    simp_rw [hident]
    have h := congrArg
      (fun M : Matrix (StateDifferenceIndex N m) (StateCopyIndex N m) R =>
        M r (Sum.inr j))
      (stateIdentification_mul_right (R := R) N m)
    simpa [Matrix.mul_apply] using h
  · rfl
  · rfl

/-- Matrix-level state-copy elimination: the identification rows give the
identity pivot, the explicit determinant-one column operation introduces
differences and anchors, and the determinant-one lower row operation clears
the residual difference coefficients. -/
theorem stateCopyPhysical_reduction
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R)
    (hident : ∀ r c,
      state (Sum.inl r) c = stateIdentificationMatrix (R := R) N m r c) :
    stateCopyPhysicalLeft (R := R) N m state * state *
        differenceAnchorRight (R := R) N m =
      Matrix.fromBlocks (1 : Matrix (StateDifferenceIndex N m)
          (StateDifferenceIndex N m) R) 0 0
        (stateCopyPhysicalBlock (R := R) N m state) := by
  rw [Matrix.mul_assoc,
    state_mul_differenceAnchorRight_eq (R := R) N m state hident,
    stateCopyPhysicalLeft, fromBlocks_mul_fromBlocks]
  simp

/-- A constructor feeding the concrete state-copy elimination directly into
`PhysicalEliminationCertificate`.  The input matrix is assumed to have already
been reindexed so that its identification rows and early-copy columns come
first; independent row/column permutations can be composed outside this
constructor. -/
def orderedStateCopyPhysicalCertificate
    (state : Matrix (StateCopyIndex N m) (StateCopyIndex N m) R)
    (hident : ∀ r c,
      state (Sum.inl r) c = stateIdentificationMatrix (R := R) N m r c) :
    PhysicalEliminationCertificate (a := StateDifferenceIndex N m)
      (stateCopyPhysicalBlock (R := R) N m state) state 1 where
  order := Equiv.refl _
  rowScaling := 1
  left := stateCopyPhysicalLeft (R := R) N m state
  right := differenceAnchorRight (R := R) N m
  leftSign := 1
  rightSign := 1
  leftSign_spec := Or.inl rfl
  rightSign_spec := Or.inl rfl
  det_rowScaling := Matrix.det_one
  det_left := stateCopyPhysicalLeft_det (R := R) N m state
  det_right := differenceAnchorRight_det (R := R) N m
  reduction := by
    simpa using stateCopyPhysical_reduction (R := R) N m state hident

end OrderedPhysicalCertificate

section ConcreteCyclicCompanion

/-- Row relabeling for the cyclic state equations.  Difference rows use the
physical site shared by `s_{i+1,k}` and `s_{i,k+1}`, independently of the
column relabeling. -/
def cyclicStateEquationRelabel (N m : ℕ) [NeZero N]
    (offset : ZMod N) :
    ZMod N × Fin (m + 1) ≃ StateCopyIndex N m :=
  (cyclicPhysicalPairEquiv N (m + 1) (offset + 1)) |>.trans
    ((ZMod.finEquiv N).symm.toEquiv.prodCongr (Equiv.refl _)) |>.trans
    (splitStateCopyEquiv N m)

/-- The ordered physical-site/copy index of the equation
`s_{i+1,k} - s_{i,k+1} = 0`. -/
def cyclicEquationDifferenceIndex (N m : ℕ) [NeZero N]
    (offset : ZMod N) (i : ZMod N) (k : Fin m) :
    StateDifferenceIndex N m :=
  toLex ((ZMod.finEquiv N).symm
    (i + offset + 1 + (k.val : ZMod N)), k)

@[simp] theorem cyclicStateEquationRelabel_castSucc
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (i : ZMod N) (k : Fin m) :
    cyclicStateEquationRelabel N m offset (i, k.castSucc) =
      Sum.inl (cyclicEquationDifferenceIndex N m offset i k) := by
  simp [cyclicStateEquationRelabel, cyclicPhysicalPairEquiv,
    cyclicEquationDifferenceIndex, add_assoc]

@[simp] theorem cyclicStateEquationRelabel_last
    (N m : ℕ) [NeZero N] (offset : ZMod N) (i : ZMod N) :
    cyclicStateEquationRelabel N m offset (i, Fin.last m) =
      Sum.inr ((ZMod.finEquiv N).symm
        (i + offset + 1 + (m : ZMod N))) := by
  simp [cyclicStateEquationRelabel, cyclicPhysicalPairEquiv, add_assoc]

/-- A cyclic companion state matrix on the raw coordinates
`ZMod N × Fin (m+1)`.  Its first `m` rows at site `i` are the state-copy
equations `s_{i+1,k} - s_{i,k+1} = 0`; its last row is supplied by
`lastRow i`. -/
def cyclicCompanionStateMatrix
    {R : Type*} [CommRing R] (N m : ℕ) [NeZero N]
    (offset : ZMod N)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R)) :
    Matrix (ZMod N × Fin (m + 1)) (ZMod N × Fin (m + 1)) R :=
  fun row col => Fin.lastCases (lastRow row.1 col) (fun k =>
    stateIdentificationMatrix (R := R) N m
      (cyclicEquationDifferenceIndex N m offset row.1 k)
      (cyclicStateCopyRelabel N m offset col)) row.2

@[simp] theorem cyclicCompanionStateMatrix_castSucc
    {R : Type*} [CommRing R] (N m : ℕ) [NeZero N]
    (offset : ZMod N)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R))
    (i : ZMod N) (k : Fin m) (col : ZMod N × Fin (m + 1)) :
    cyclicCompanionStateMatrix N m offset lastRow (i, k.castSucc) col =
      stateIdentificationMatrix (R := R) N m
        (cyclicEquationDifferenceIndex N m offset i k)
        (cyclicStateCopyRelabel N m offset col) := by
  simp [cyclicCompanionStateMatrix]

@[simp] theorem cyclicCompanionStateMatrix_last
    {R : Type*} [CommRing R] (N m : ℕ) [NeZero N]
    (offset : ZMod N)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R))
    (i : ZMod N) (col : ZMod N × Fin (m + 1)) :
    cyclicCompanionStateMatrix N m offset lastRow (i, Fin.last m) col =
      lastRow i col := by
  simp [cyclicCompanionStateMatrix]

/-- The cyclic companion state matrix after independent equation-row and
state-copy-column relabelings. -/
def orderedCyclicCompanionState
    {R : Type*} [CommRing R] (N m : ℕ) [NeZero N]
    (offset : ZMod N)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R)) :
    Matrix (StateCopyIndex N m) (StateCopyIndex N m) R :=
  Matrix.reindex (cyclicStateEquationRelabel N m offset)
    (cyclicStateCopyRelabel N m offset)
    (cyclicCompanionStateMatrix N m offset lastRow)

/-- After the independent row/column reindexings, the first `N*m` rows are
exactly the state-identification block. -/
theorem orderedCyclicCompanionState_identification
    {R : Type*} [CommRing R] (N m : ℕ) [NeZero N]
    (offset : ZMod N)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R))
    (r : StateDifferenceIndex N m) (c : StateCopyIndex N m) :
    orderedCyclicCompanionState N m offset lastRow (Sum.inl r) c =
      stateIdentificationMatrix (R := R) N m r c := by
  let rowEquiv := cyclicStateEquationRelabel N m offset
  let colEquiv := cyclicStateCopyRelabel N m offset
  let rawRow := rowEquiv.symm (Sum.inl r)
  let rawCol := colEquiv.symm c
  rcases hraw : rawRow with ⟨i, k⟩
  have hrow : rowEquiv (i, k) = Sum.inl r := by
    rw [← hraw]
    exact rowEquiv.apply_symm_apply (Sum.inl r)
  have hk : k ≠ Fin.last m := by
    intro hk
    subst k
    simp [rowEquiv] at hrow
  let k' : Fin m := Fin.castPred k hk
  have hk' : k'.castSucc = k := Fin.castSucc_castPred k hk
  have hr : cyclicEquationDifferenceIndex N m offset i k' = r := by
    rw [← Sum.inl.injEq]
    rw [← hrow]
    rw [← hk']
    exact (cyclicStateEquationRelabel_castSucc N m offset i k').symm
  rw [← hr]
  change cyclicCompanionStateMatrix N m offset lastRow
      (rowEquiv.symm (Sum.inl (cyclicEquationDifferenceIndex N m offset i k')))
      rawCol = _
  have hrowSymm :
      rowEquiv.symm (Sum.inl (cyclicEquationDifferenceIndex N m offset i k')) =
        (i, k'.castSucc) := by
    apply rowEquiv.injective
    rw [rowEquiv.apply_symm_apply]
    exact (cyclicStateEquationRelabel_castSucc N m offset i k').symm
  rw [hrowSymm]
  simp [rawCol, colEquiv]

/-- The concrete cyclic state system fed into the generic ordered state-copy
physical elimination.  The surviving physical block is intentionally left
abstract at this stage. -/
noncomputable def cyclicCompanionPhysicalCertificate
    {R : Type*} [CommRing R] (N m : ℕ) [NeZero N]
    (offset : ZMod N)
    (lastRow : ZMod N → (ZMod N × Fin (m + 1) → R)) :
    PhysicalEliminationCertificate (a := StateDifferenceIndex N m)
      (stateCopyPhysicalBlock (R := R) N m
        (orderedCyclicCompanionState N m offset lastRow))
      (orderedCyclicCompanionState N m offset lastRow) 1 :=
  orderedStateCopyPhysicalCertificate (R := R) N m
    (orderedCyclicCompanionState N m offset lastRow)
    (orderedCyclicCompanionState_identification N m offset lastRow)

end ConcreteCyclicCompanion

end CircularLawSection4
