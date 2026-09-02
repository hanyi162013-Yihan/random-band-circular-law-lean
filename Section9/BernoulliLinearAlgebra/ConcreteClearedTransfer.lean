import BernoulliLinearAlgebra.BlockFloquet
import BernoulliLinearAlgebra.JacobiConcrete
import BernoulliLinearAlgebra.CyclicFloquetConcrete

/-!
# Polynomially cleared companion transfers

The transfer matrix `stepTransfer B D C` uses the nonsingular inverse of the
right-interface block `B`.  On `det B ≠ 0`, Jacobi's complementary-minor
identity shows that a *single* factor `det B` clears every exterior degree:

`det B • compound k (stepTransfer B D C)`.

This file constructs the resulting matrix directly from complementary minors,
so its definition remains meaningful when `B` is singular.  In particular,
we never interpret a totalized matrix inverse at a singular point as the
polynomial continuation of the transfer expression.
-/

open Filter Topology
open scoped BigOperators Matrix Topology

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard

section ClearedInverseCompound

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- The row/column reindexing sign in Jacobi's complementary-minor formula. -/
def jacobiReindexSign {k m : ℕ} (hm : m + k = Fintype.card ι)
    (s t : powersetCard ι k) : ℂ :=
  ((Equiv.Perm.sign
    ((subsetSplitEquiv hm s).symm.trans (subsetSplitEquiv hm t)) : ℤ) : ℂ)

/-- Exact determinant, including its sign, of the matrix used in the concrete
Jacobi proof. -/
theorem det_jacobiReindexMatrix_eq_sign_mul {k m : ℕ}
    (hm : m + k = Fintype.card ι) (E : Matrix ι ι ℂ)
    (s t : powersetCard ι k) :
    (jacobiReindexMatrix hm E s t).det =
      jacobiReindexSign hm s t * E.det := by
  change (Matrix.reindex (subsetSplitEquiv hm t).symm
    (subsetSplitEquiv hm s).symm E).det = _
  rw [Matrix.det_reindex]
  rfl

/-- The sign in the reindexed Jacobi chart squares to one. -/
theorem jacobiReindexSign_sq {k m : ℕ}
    (hm : m + k = Fintype.card ι) (s t : powersetCard ι k) :
    jacobiReindexSign hm s t * jacobiReindexSign hm s t = 1 := by
  unfold jacobiReindexSign
  rcases Int.units_eq_one_or
    (Equiv.Perm.sign
      ((subsetSplitEquiv hm s).symm.trans (subsetSplitEquiv hm t))) with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- A denominator-free matrix of complementary minors.  For an invertible
`E`, this is `det E • compound k E⁻¹`; unlike that expression, the definition
is meaningful for every `E`.  Degrees above the ambient dimension are zero. -/
def clearedInverseCompound (k : ℕ) (E : Matrix ι ι ℂ) :
    Matrix (powersetCard ι k) (powersetCard ι k) ℂ :=
  if hk : k ≤ Fintype.card ι then
    let hm : Fintype.card ι - k + k = Fintype.card ι :=
      Nat.sub_add_cancel hk
    (show Matrix (powersetCard ι k) (powersetCard ι k) ℂ from
      fun s t ↦ jacobiReindexSign hm s t *
        minor (Fintype.card ι - k) E
          (powersetCard.compl hm t) (powersetCard.compl hm s))
  else 0

@[simp]
theorem clearedInverseCompound_apply_of_le (k : ℕ) (E : Matrix ι ι ℂ)
    (hk : k ≤ Fintype.card ι) (s t : powersetCard ι k) :
    clearedInverseCompound k E s t =
      jacobiReindexSign (Nat.sub_add_cancel hk) s t *
        minor (Fintype.card ι - k) E
          (powersetCard.compl (Nat.sub_add_cancel hk) t)
          (powersetCard.compl (Nat.sub_add_cancel hk) s) := by
  unfold clearedInverseCompound
  split
  · rfl
  · contradiction

/-- On the invertible locus, the complementary-minor matrix is exactly the
single-determinant clearing of the inverse compound. -/
theorem clearedInverseCompound_eq_det_smul_compound_inv
    (E : Matrix ι ι ℂ) (hE : IsUnit E.det)
    (k : ℕ) (hk : k ≤ Fintype.card ι) :
    clearedInverseCompound k E = E.det • compound k E⁻¹ := by
  let hm : Fintype.card ι - k + k = Fintype.card ι :=
    Nat.sub_add_cancel hk
  ext s t
  rw [clearedInverseCompound_apply_of_le k E hk,
    Matrix.smul_apply, compound_apply]
  let M := jacobiReindexMatrix hm E s t
  have hEne : E.det ≠ 0 := isUnit_iff_ne_zero.mp hE
  have hMdet : M.det = jacobiReindexSign hm s t * E.det :=
    det_jacobiReindexMatrix_eq_sign_mul hm E s t
  have hsignSq :
      jacobiReindexSign hm s t * jacobiReindexSign hm s t = 1 :=
    jacobiReindexSign_sq hm s t
  have hsignNe : jacobiReindexSign hm s t ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hsignSq
    exact zero_ne_one hsignSq
  have hMne : M.det ≠ 0 := by
    rw [hMdet]
    exact mul_ne_zero hsignNe hEne
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr hMne
  have hblock :=
    det_inv_topLeft_eq_det_bottomRight_div_det_of_isUnit M hM
  rw [det_inv_topLeft_jacobiReindexMatrix,
    det_bottomRight_jacobiReindexMatrix] at hblock
  rw [hblock, hMdet]
  have hsignInv : (jacobiReindexSign hm s t)⁻¹ =
      jacobiReindexSign hm s t :=
    inv_eq_of_mul_eq_one_right hsignSq
  symm
  calc
    E.det * ((jacobiReindexSign hm s t * E.det)⁻¹ *
        minor (Fintype.card ι - k) E
          (powersetCard.compl hm t) (powersetCard.compl hm s)) =
        (E.det * E.det⁻¹) *
          (jacobiReindexSign hm s t *
            minor (Fintype.card ι - k) E
              (powersetCard.compl hm t) (powersetCard.compl hm s)) := by
      rw [_root_.mul_inv_rev, hsignInv]
      ring
    _ = jacobiReindexSign hm s t *
        minor (Fintype.card ι - k) E
          (powersetCard.compl hm t) (powersetCard.compl hm s) := by
      rw [mul_inv_cancel₀ hEne, one_mul]

end ClearedInverseCompound

section ClearedStepCompound

variable {W : Type*} [Fintype W] [LinearOrder W]

local instance clearedStepCompoundSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift' (fun x : W ⊕ W ↦ (toLex x : W ⊕ₗ W))
    (fun _ _ h ↦ toLex.injective h)

/-- Exterior powers turn matrix negation into the scalar `(-1)^k`. -/
theorem compound_neg (k : ℕ) (A : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    compound k (-A) = (-1 : ℂ) ^ k • compound k A := by
  ext s t
  simp only [Matrix.smul_apply, compound_apply, smul_eq_mul]
  unfold minor
  rw [Matrix.submatrix_neg]
  change det (-(A.submatrix (ofFinEmbEquiv.symm s)
    (ofFinEmbEquiv.symm t))) = _
  rw [Matrix.det_neg, Fintype.card_fin]

/-- The explicit denominator-free `k`th exterior operator for one companion
transfer step.  Its ingredients are complementary minors of `stepL B` and
ordinary minors of `stepK D C`; in particular, no inverse occurs here. -/
def clearedStepCompound (k : ℕ) (B D C : Matrix W W ℂ) :
    Matrix (powersetCard (W ⊕ W) k) (powersetCard (W ⊕ W) k) ℂ :=
  (-1 : ℂ) ^ k •
    (clearedInverseCompound k (stepL B) * compound k (stepK D C))

/-- On `det B ≠ 0`, the explicit one-step matrix is exactly the single-factor
clearing `det B • compound k (stepTransfer B D C)`. -/
theorem clearedStepCompound_eq_det_smul_compound_stepTransfer
    (k : ℕ) (hk : k ≤ Fintype.card (W ⊕ W))
    (B D C : Matrix W W ℂ) (hB : IsUnit B.det) :
    clearedStepCompound k B D C =
      B.det • compound k (stepTransfer B D C) := by
  have hL : IsUnit (stepL B).det := by simpa using hB
  unfold clearedStepCompound
  rw [stepTransfer, compound_mul, compound_neg,
    clearedInverseCompound_eq_det_smul_compound_inv (stepL B) hL k hk,
    ← stepL_det B]
  ext s t
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The same result with the paper's block companion matrix displayed
literally. -/
theorem clearedStepCompound_eq_det_smul_compound_companion
    (k : ℕ) (hk : k ≤ Fintype.card (W ⊕ W))
    (B D C : Matrix W W ℂ) (hB : IsUnit B.det) :
    clearedStepCompound k B D C =
      B.det • compound k
        (Matrix.fromBlocks (-(B⁻¹ * D)) (-(B⁻¹ * C)) 1 0) := by
  rw [← stepTransfer_eq_companion B D C hB]
  exact clearedStepCompound_eq_det_smul_compound_stepTransfer
    k hk B D C hB

end ClearedStepCompound

section GlobalPolynomialExteriorTrace

/-- The three physical blocks defining one companion-transfer step. -/
structure CompanionStep (W : Type*) where
  B : Matrix W W ℂ
  D : Matrix W W ℂ
  C : Matrix W W ℂ

variable {W : Type*} [Fintype W] [LinearOrder W]

local instance globalPolynomialExteriorTraceSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift' (fun x : W ⊕ W ↦ (toLex x : W ⊕ₗ W))
    (fun _ _ h ↦ toLex.injective h)

/-- Chronological product of the explicit cleared exterior operators.  This
definition is denominator-free for arbitrary, possibly singular, `B` blocks. -/
def polynomialClearedCompoundProduct (k : ℕ) :
    List (CompanionStep W) →
      Matrix (powersetCard (W ⊕ W) k) (powersetCard (W ⊕ W) k) ℂ
  | [] => compound k 1
  | x :: xs =>
      polynomialClearedCompoundProduct k xs *
        clearedStepCompound k x.B x.D x.C

/-- The old scalar-plus-total-transfer data.  It is used only for comparison
on the locus where every `B` is invertible, never as the singular extension. -/
def inverseTransferClearingData (xs : List (CompanionStep W)) :
    List (ℂ × Matrix (W ⊕ W) (W ⊕ W) ℂ) :=
  xs.map fun x ↦ (x.B.det, stepTransfer x.B x.D x.C)

/-- If every interface block is invertible, the direct polynomial product is
the existing product of scalar-cleared total-inverse transfers. -/
theorem polynomialClearedCompoundProduct_eq_clearedCompoundProduct
    (xs : List (CompanionStep W))
    (hxs : ∀ x ∈ xs, IsUnit x.B.det)
    (k : ℕ) (hk : k ≤ Fintype.card (W ⊕ W)) :
    polynomialClearedCompoundProduct k xs =
      clearedCompoundProduct k (inverseTransferClearingData xs) := by
  induction xs with
  | nil =>
      simp [polynomialClearedCompoundProduct, inverseTransferClearingData,
        clearedCompoundProduct]
  | cons x xs ih =>
      have hx : IsUnit x.B.det := hxs x (by simp)
      have htail : ∀ y ∈ xs, IsUnit y.B.det := by
        intro y hy
        exact hxs y (by simp [hy])
      simp only [polynomialClearedCompoundProduct,
        inverseTransferClearingData, List.map_cons, clearedCompoundProduct]
      rw [ih htail,
        clearedStepCompound_eq_det_smul_compound_stepTransfer
          k hk x.B x.D x.C hx]
      rfl

/-- The global denominator-free exterior expression.  Every summand is a
product of matrices whose entries are polynomial expressions in the physical
blocks, so this definition remains the intended expression at singular `B`. -/
def polynomialClearedSignedCompoundTrace
    (xs : List (CompanionStep W)) : ℂ :=
  ∑ s : Finset (W ⊕ W), (-1 : ℂ) ^ s.card *
    polynomialClearedCompoundProduct s.card xs
      (ofCard rfl) (ofCard rfl)

/-- On the invertible locus, the global polynomial expression can be
substituted directly into the already established `clearedSignedCompoundTrace`. -/
theorem polynomialClearedSignedCompoundTrace_eq_clearedSignedCompoundTrace
    (xs : List (CompanionStep W))
    (hxs : ∀ x ∈ xs, IsUnit x.B.det) :
    polynomialClearedSignedCompoundTrace xs =
      clearedSignedCompoundTrace (inverseTransferClearingData xs) := by
  unfold polynomialClearedSignedCompoundTrace clearedSignedCompoundTrace
  apply Finset.sum_congr rfl
  intro s _
  rw [polynomialClearedCompoundProduct_eq_clearedCompoundProduct
    xs hxs s.card (Finset.card_le_univ s)]

/-- Global form of the denominator-cleared Floquet exterior identity.  The
left side is defined for all blocks, including singular ones; the equality to
the monodromy expression is asserted only when all interface determinants are
units. -/
theorem polynomialClearedSignedCompoundTrace_eq_detProduct_mul_floquet
    (xs : List (CompanionStep W))
    (hxs : ∀ x ∈ xs, IsUnit x.B.det) :
    polynomialClearedSignedCompoundTrace xs =
      (xs.map fun x ↦ x.B.det).prod *
        (1 - chronologicalProduct
          (xs.map fun x ↦ stepTransfer x.B x.D x.C)).det := by
  rw [polynomialClearedSignedCompoundTrace_eq_clearedSignedCompoundTrace
    xs hxs]
  simpa [inverseTransferClearingData, clearingFactor, transferList,
    List.map_map, Function.comp_def] using
      (cleared_floquet_exterior_identity
        (xs := inverseTransferClearingData xs))

end GlobalPolynomialExteriorTrace

section PhysicalCyclicPolynomialContinuation

variable {m : ℕ} {W : Type*} [Fintype W] [LinearOrder W]

local instance physicalCyclicContinuationSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift' (fun x : W ⊕ W ↦ (toLex x : W ⊕ₗ W))
    (fun _ _ h ↦ toLex.injective h)

/-- Package an indexed physical cyclic system as the chronological list of
companion steps used by the denominator-free exterior expression. -/
def companionStepList
    (B D C : Fin (m + 1) → Matrix W W ℂ) : List (CompanionStep W) :=
  List.ofFn fun j ↦ ⟨B j, D j, C j⟩

/-- Simultaneously perturb the interface block of every step in a list. -/
def perturbCompanionStepList (xs : List (CompanionStep W)) (z : ℂ) :
    List (CompanionStep W) :=
  xs.map fun x ↦ ⟨scalarPerturb x.B z, x.D, x.C⟩

@[simp]
theorem perturbCompanionStepList_zero (xs : List (CompanionStep W)) :
    perturbCompanionStepList xs 0 = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [perturbCompanionStepList]

@[simp]
theorem perturbCompanionStepList_companionStepList
    (B D C : Fin (m + 1) → Matrix W W ℂ) (z : ℂ) :
    perturbCompanionStepList (companionStepList B D C) z =
      companionStepList (fun j ↦ scalarPerturb (B j) z) D C := by
  simp [perturbCompanionStepList, companionStepList, List.map_ofFn,
    Function.comp_def]

/-- Exterior compounds are continuous in the entries of their matrix. -/
theorem continuous_compound_of_continuous
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι]
    (k : ℕ) {A : X → Matrix ι ι ℂ} (hA : Continuous A) :
    Continuous (fun x ↦ compound k (A x)) := by
  apply continuous_matrix
  intro s t
  simp only [compound_apply]
  unfold minor
  exact (hA.matrix_submatrix (ofFinEmbEquiv.symm s)
    (ofFinEmbEquiv.symm t)).matrix_det

/-- The explicit complementary-minor clearing is continuous even across the
singular locus. -/
theorem continuous_clearedInverseCompound_of_continuous
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι]
    (k : ℕ) {A : X → Matrix ι ι ℂ} (hA : Continuous A) :
    Continuous (fun x ↦ clearedInverseCompound k (A x)) := by
  by_cases hk : k ≤ Fintype.card ι
  · apply continuous_matrix
    intro s t
    simp_rw [clearedInverseCompound_apply_of_le k _ hk]
    unfold minor
    exact continuous_const.mul
      ((hA.matrix_submatrix
        (ofFinEmbEquiv.symm (powersetCard.compl
          (Nat.sub_add_cancel hk) t))
        (ofFinEmbEquiv.symm (powersetCard.compl
          (Nat.sub_add_cancel hk) s))).matrix_det)
  · have hzero : (fun x ↦ clearedInverseCompound k (A x)) =
        (fun _ ↦ 0) := by
      funext x
      simp [clearedInverseCompound, hk]
    rw [hzero]
    exact continuous_const

/-- A simultaneously scalar-perturbed one-step cleared exterior matrix is
continuous in the perturbation parameter. -/
theorem continuous_clearedStepCompound_scalarPerturb
    (k : ℕ) (B D C : Matrix W W ℂ) :
    Continuous (fun z ↦
      clearedStepCompound k (scalarPerturb B z) D C) := by
  have hL : Continuous (fun z ↦ stepL (scalarPerturb B z)) := by
    exact (continuous_scalarPerturb B).matrix_fromBlocks
      continuous_const continuous_const continuous_const
  have hInv : Continuous (fun z ↦
      clearedInverseCompound k (stepL (scalarPerturb B z))) :=
    continuous_clearedInverseCompound_of_continuous
      (X := ℂ) (ι := W ⊕ W) k hL
  have hmul : Continuous (fun z ↦
      clearedInverseCompound k (stepL (scalarPerturb B z)) *
        compound k (stepK D C)) :=
    hInv.matrix_mul continuous_const
  exact hmul.const_smul ((-1 : ℂ) ^ k)

/-- Every entry of the chronological product of direct cleared compounds is
continuous under a common scalar perturbation of all interface blocks. -/
theorem continuous_polynomialClearedCompoundProduct_perturb
    (k : ℕ) (xs : List (CompanionStep W)) :
    Continuous (fun z ↦ polynomialClearedCompoundProduct k
      (perturbCompanionStepList xs z)) := by
  induction xs with
  | nil =>
      simp only [perturbCompanionStepList, List.map_nil,
        polynomialClearedCompoundProduct]
      exact continuous_const
  | cons x xs ih =>
      simp only [perturbCompanionStepList, List.map_cons,
        polynomialClearedCompoundProduct]
      exact ih.matrix_mul
        (continuous_clearedStepCompound_scalarPerturb k x.B x.D x.C)

/-- The full denominator-free exterior trace is continuous under a common
scalar perturbation of all interface blocks. -/
theorem continuous_polynomialClearedSignedCompoundTrace_perturb
    (xs : List (CompanionStep W)) :
    Continuous (fun z ↦ polynomialClearedSignedCompoundTrace
      (perturbCompanionStepList xs z)) := by
  unfold polynomialClearedSignedCompoundTrace
  apply continuous_finsetSum
  intro s _
  exact continuous_const.mul
    ((continuous_polynomialClearedCompoundProduct_perturb s.card xs).matrix_elem
      (ofCard rfl) (ofCard rfl))

/-- Scalar perturbation of the full site-block diagonal is exactly simultaneous
scalar perturbation of all its diagonal blocks. -/
theorem siteBlockDiagonal_scalarPerturb
    (B : Fin (m + 1) → Matrix W W ℂ) (z : ℂ) :
    siteBlockDiagonal (fun j ↦ scalarPerturb (B j) z) =
      scalarPerturb (siteBlockDiagonal B) z := by
  ext ⟨j, a⟩ ⟨k, b⟩
  by_cases hjk : j = k
  · subst k
    by_cases hab : a = b
    · subst b
      simp [siteBlockDiagonal_apply, scalarPerturb, Matrix.scalar_apply]
    · have hpair : (j, a) ≠ (j, b) := by
        intro h
        exact hab (congrArg Prod.snd h)
      simp [siteBlockDiagonal_apply, scalarPerturb, Matrix.scalar_apply,
        hab, hpair]
  · have hpair : (j, a) ≠ (k, b) := by
      intro h
      exact hjk (congrArg Prod.fst h)
    simp [siteBlockDiagonal_apply, scalarPerturb, Matrix.scalar_apply,
      hjk, hpair]

omit [Fintype W] [LinearOrder W] in
/-- A site-block diagonal matrix varies continuously when all of its blocks
vary continuously. -/
theorem continuous_siteBlockDiagonal_of_continuous
    {X : Type*} [TopologicalSpace X]
    {A : X → Fin (m + 1) → Matrix W W ℂ} (hA : Continuous A) :
    Continuous (fun x ↦ siteBlockDiagonal (A x)) := by
  apply continuous_matrix
  rintro ⟨j, a⟩ ⟨k, b⟩
  by_cases hjk : j = k
  · subst k
    simp only [siteBlockDiagonal_apply, if_pos]
    exact ((continuous_apply j).comp hA).matrix_elem a b
  · simp only [siteBlockDiagonal_apply, if_neg hjk]
    exact continuous_const

/-- The physical cyclic determinant polynomial is continuous under the same
simultaneous scalar perturbation of all interface blocks. -/
theorem continuous_cyclicFloquetPolynomialExtension_scalarPerturb
    (B D C : Fin (m + 1) → Matrix W W ℂ) :
    Continuous (fun z ↦ cyclicFloquetPolynomialExtension
      (fun j ↦ scalarPerturb (B j) z) D C) := by
  have hB : Continuous (fun z ↦
      (fun j ↦ scalarPerturb (B j) z)) :=
    continuous_pi fun j ↦ continuous_scalarPerturb (B j)
  have hdiag : Continuous (fun z ↦
      siteBlockDiagonal (fun j ↦ scalarPerturb (B j) z)) :=
    continuous_siteBlockDiagonal_of_continuous hB
  have hphysical : Continuous (fun z ↦ physicalCyclicMatrix
      (fun j ↦ scalarPerturb (B j) z) D C) := by
    change Continuous (fun z ↦
      siteBlockDiagonal D +
        siteBlockDiagonal (fun j ↦ scalarPerturb (B j) z) * cyclicShift +
          siteBlockDiagonal C * cyclicShift⁻¹)
    exact (continuous_const.add
      (hdiag.matrix_mul continuous_const)).add
        (continuous_const.matrix_mul continuous_const)
  exact continuous_const.mul hphysical.matrix_det

/-- On the open locus where every interface block is invertible, the direct
complementary-minor expression agrees with the physical cyclic determinant
polynomial (including the fixed Floquet sign). -/
theorem polynomialClearedSignedCompoundTrace_companionStepList_eq_extension_of_units
    (B D C : Fin (m + 1) → Matrix W W ℂ)
    (hB : ∀ j, IsUnit (B j).det) (hm : 0 < m) :
    polynomialClearedSignedCompoundTrace (companionStepList B D C) =
      cyclicFloquetPolynomialExtension B D C := by
  rw [polynomialClearedSignedCompoundTrace_eq_clearedSignedCompoundTrace]
  · symm
    simpa [companionStepList, inverseTransferClearingData,
      determinantClearedSteps, List.map_ofFn, Function.comp_def] using
        (cyclicFloquetPolynomialExtension_agrees_on_units B D C hB hm)
  · simpa [companionStepList] using
      (List.forall_mem_ofFn_iff.mpr hB)

/-- Polynomial continuation across singular interface blocks.  All interface
blocks are perturbed by the same scalar.  Nonsingularity of their one large
site-block diagonal implies nonsingularity of every block, so the equality on
the invertible locus passes to the limit by continuity. -/
theorem polynomialClearedSignedCompoundTrace_companionStepList_eq_extension
    (B D C : Fin (m + 1) → Matrix W W ℂ) (hm : 0 < m) :
    polynomialClearedSignedCompoundTrace (companionStepList B D C) =
      cyclicFloquetPolynomialExtension B D C := by
  rcases exists_scalarPerturbationSequence (siteBlockDiagonal B) with
    ⟨ε, hε0, hεdet⟩
  have hBε : ∀ q j, IsUnit (scalarPerturb (B j) (ε q)).det := by
    intro q j
    apply isUnit_iff_ne_zero.mpr
    have hprod : (∏ r, (scalarPerturb (B r) (ε q)).det) ≠ 0 := by
      rw [← siteBlockDiagonal_det]
      rw [siteBlockDiagonal_scalarPerturb]
      exact hεdet q
    exact Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ j)
  have heq (q : ℕ) :
      polynomialClearedSignedCompoundTrace
          (companionStepList (fun j ↦ scalarPerturb (B j) (ε q)) D C) =
        cyclicFloquetPolynomialExtension
          (fun j ↦ scalarPerturb (B j) (ε q)) D C :=
    polynomialClearedSignedCompoundTrace_companionStepList_eq_extension_of_units
      (fun j ↦ scalarPerturb (B j) (ε q)) D C (hBε q) hm
  have hpolynomial : Tendsto
      (fun q ↦ polynomialClearedSignedCompoundTrace
        (companionStepList (fun j ↦ scalarPerturb (B j) (ε q)) D C))
      atTop
      (nhds (polynomialClearedSignedCompoundTrace
        (companionStepList B D C))) := by
    have h :=
      (continuous_polynomialClearedSignedCompoundTrace_perturb
        (companionStepList B D C)).continuousAt.tendsto.comp hε0
    simpa [Function.comp_def] using h
  have hphysical : Tendsto
      (fun q ↦ cyclicFloquetPolynomialExtension
        (fun j ↦ scalarPerturb (B j) (ε q)) D C)
      atTop (nhds (cyclicFloquetPolynomialExtension B D C)) := by
    have h :=
      (continuous_cyclicFloquetPolynomialExtension_scalarPerturb B D C)
        |>.continuousAt.tendsto.comp hε0
    simpa [Function.comp_def] using h
  have heventually :
      (fun q ↦ polynomialClearedSignedCompoundTrace
        (companionStepList (fun j ↦ scalarPerturb (B j) (ε q)) D C)) =ᶠ[atTop]
      (fun q ↦ cyclicFloquetPolynomialExtension
        (fun j ↦ scalarPerturb (B j) (ε q)) D C) :=
    Filter.Eventually.of_forall heq
  exact tendsto_nhds_unique hpolynomial
    (hphysical.congr' heventually.symm)

/-- The Section 9.3 denominator-cleared exterior formula, valid for arbitrary
(possibly singular) interface blocks, equals the literal physical cyclic
determinant up to the fixed Floquet sign. -/
theorem polynomialClearedSignedCompoundTrace_companionStepList_eq_physical
    (B D C : Fin (m + 1) → Matrix W W ℂ) (hm : 0 < m) :
    polynomialClearedSignedCompoundTrace (companionStepList B D C) =
      floquetSign (R := ℂ) (m := m) (w := W) *
        (physicalCyclicMatrix B D C).det := by
  rw [
    polynomialClearedSignedCompoundTrace_companionStepList_eq_extension B D C hm]
  rfl

/-- Literal `List.ofFn` form of the global singular-interface identity. -/
theorem polynomialClearedSignedCompoundTrace_listOfFn_eq_physical
    (B D C : Fin (m + 1) → Matrix W W ℂ) (hm : 0 < m) :
    polynomialClearedSignedCompoundTrace
        (List.ofFn fun j ↦ (CompanionStep.mk (B j) (D j) (C j))) =
      floquetSign (R := ℂ) (m := m) (w := W) *
        (physicalCyclicMatrix B D C).det := by
  simpa [companionStepList] using
    (polynomialClearedSignedCompoundTrace_companionStepList_eq_physical
      B D C hm)

end PhysicalCyclicPolynomialContinuation

end BernoulliLinearAlgebra
