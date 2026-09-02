import BernoulliLinearAlgebra.ThreeBlockTerminal
import Mathlib.Tactic

/-!
# Valid monomial masks in the concrete three-block determinant

This file isolates the genuine combinatorics behind the all-minor estimate.
A squarefree monomial can contribute to the determinant only when its fresh
entries form a partial row-column matching.  Because the deterministic
matrix is supported on the outer coordinates, every contributing matching
also covers every central row and every central column.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard MvPolynomial

section AffineProductCoefficient

variable {v : Type*} [DecidableEq v]

/-- A squarefree exponent remembers its underlying finite set. -/
theorem squarefreeExponent_injective :
    Function.Injective (@squarefreeExponent v _) := by
  intro S T h
  ext x
  have hx := congrArg (fun d : v →₀ ℕ => d x) h
  constructor
  · intro hxS
    by_contra hxT
    simp [squarefreeExponent, Finsupp.indicator_apply, hxS, hxT] at hx
  · intro hxT
    by_contra hxS
    simp [squarefreeExponent, Finsupp.indicator_apply, hxS, hxT] at hx

/-- Reindexing a product of pairwise distinct variables by its image does
not change that product. -/
theorem prod_X_image_of_injective
    {i : Type*} {R : Type*} [CommSemiring R]
    (e : i → v) (he : Function.Injective e) (t : Finset i) :
    (∏ a ∈ t, (X (e a) : MvPolynomial v R)) =
      ∏ x ∈ t.image e, (X x : MvPolynomial v R) := by
  rw [Finset.prod_image]
  intro a _ b _ hab
  exact he hab

theorem prod_X_eq_monomial
    {R : Type*} [CommSemiring R] (s : Finset v) :
    (∏ x ∈ s, (X x : MvPolynomial v R)) =
      monomial (squarefreeExponent s) 1 := by
  simpa [squarefreeExponent] using
    (MvPolynomial.prod_X_pow (R := R) (fun _ : v => 1) s)

theorem coeff_monomial_mul_prod_C
    {i : Type*} {R : Type*} [CommSemiring R]
    (m n : v →₀ ℕ) (t : Finset i) (a : i → R) :
    coeff m (monomial n 1 * ∏ j ∈ t, C (a j)) =
      if n = m then ∏ j ∈ t, a j else 0 := by
  rw [← map_prod, C_apply, monomial_mul, add_zero, one_mul,
    coeff_monomial]

/-- The coefficient of a squarefree monomial in a product of affine,
pairwise-distinct variables is the product of the complementary constant
terms. -/
theorem coeff_prod_X_add_C_of_injective
    {i : Type*} {R : Type*} [Fintype i] [DecidableEq i]
    [CommSemiring R]
    (e : i → v) (he : Function.Injective e) (a : i → R)
    (S : Finset v) :
    coeff (squarefreeExponent S)
        (∏ j, ((X (e j) : MvPolynomial v R) + C (a j))) =
      if S ⊆ Finset.univ.image e then
        ∏ j with e j ∉ S, a j
      else 0 := by
  classical
  rw [Fintype.prod_add]
  simp_rw [prod_X_image_of_injective e he]
  simp_rw [prod_X_eq_monomial]
  simp only [coeff_sum]
  simp_rw [coeff_monomial_mul_prod_C]
  split_ifs with hS
  · let t₀ : Finset i := Finset.univ.filter (fun j => e j ∈ S)
    have ht₀ : t₀.image e = S := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
        simpa [t₀] using hj
      · intro hx
        rcases Finset.mem_image.mp (hS hx) with ⟨j, -, rfl⟩
        exact Finset.mem_image.mpr ⟨j, by simp [t₀, hx], rfl⟩
    rw [Finset.sum_eq_single t₀]
    · rw [if_pos (congrArg squarefreeExponent ht₀)]
      congr 1
      ext j
      simp [t₀]
    · intro t _ hne
      rw [if_neg]
      intro heq
      apply hne
      exact (Finset.image_inj he).mp
        (squarefreeExponent_injective
          (heq.trans (congrArg squarefreeExponent ht₀).symm))
    · simp
  · rw [Finset.sum_eq_zero]
    intro t _
    rw [if_neg]
    intro heq
    apply hS
    intro x hx
    have hx' : x ∈ t.image e := by
      have hcoeff := congrArg (fun d : v →₀ ℕ => d x) heq
      by_contra hxt
      simp [squarefreeExponent, Finsupp.indicator_apply, hx, hxt] at hcoeff
    rcases Finset.mem_image.mp hx' with ⟨j, -, rfl⟩
    exact Finset.mem_image_of_mem e (Finset.mem_univ j)

end AffineProductCoefficient

section PermutationExpansion

variable {w : Type*} [Fintype w] [DecidableEq w]

local instance threeBlockMaskExpansionVariableDecidableEq :
    DecidableEq (ThreeBlockVariable w) := Classical.decEq _

/-- Columns on which a determinant permutation visits a fresh cell. -/
abbrev ThreeBlockFreshColumn (σ : Equiv.Perm (ThreeBlockIndex w)) :=
  {j : ThreeBlockIndex w // threeBlockFresh (σ j) j}

/-- The fresh variable visited by a permutation at a fresh column. -/
def threeBlockPermutationVariable
    (σ : Equiv.Perm (ThreeBlockIndex w))
    (j : ThreeBlockFreshColumn σ) : ThreeBlockVariable w :=
  ⟨(σ j, j), j.2⟩

omit [Fintype w] [DecidableEq w] in
theorem threeBlockPermutationVariable_injective
    (σ : Equiv.Perm (ThreeBlockIndex w)) :
    Function.Injective (threeBlockPermutationVariable σ) := by
  intro i j h
  apply Subtype.ext
  exact congrArg (fun e : ThreeBlockVariable w => e.1.2) h

/-- The full squarefree graph monomial associated with a determinant
permutation, restricted to the fresh cells it visits. -/
def threeBlockPermutationGraph
    (σ : Equiv.Perm (ThreeBlockIndex w)) :
    Finset (ThreeBlockVariable w) :=
  Finset.univ.image (threeBlockPermutationVariable σ)

/-- Constant factors at the nonfresh cells visited by a permutation. -/
def threeBlockPermutationNonfreshProduct
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (σ : Equiv.Perm (ThreeBlockIndex w)) : ℂ :=
  ∏ j : {j : ThreeBlockIndex w // ¬threeBlockFresh (σ j) j},
    threeBlockEmb Q (σ j) j

/-- Constant factors at fresh visited cells whose variables are not in the
target monomial. -/
def threeBlockPermutationFreshComplementProduct
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (S : Finset (ThreeBlockVariable w))
    (σ : Equiv.Perm (ThreeBlockIndex w)) : ℂ :=
  ∏ j : ThreeBlockFreshColumn σ with
    threeBlockPermutationVariable σ j ∉ S,
      threeBlockEmb Q (σ j) j

theorem threeBlockHPolynomial_zero_apply
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (i j : ThreeBlockIndex w) :
    threeBlockHPolynomial Q 0 i j =
      (if h : threeBlockFresh i j then X ⟨(i, j), h⟩ else 0) +
        C (threeBlockEmb Q i j) := by
  simp [threeBlockHPolynomial, threeBlockDeltaPolynomial]

/-- Split one Leibniz product into its pairwise-distinct affine fresh
variables and its purely constant nonfresh factors. -/
theorem threeBlockPermutationPolynomialProduct_eq
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (σ : Equiv.Perm (ThreeBlockIndex w)) :
    (∏ j, threeBlockHPolynomial Q 0 (σ j) j) =
      (∏ j : ThreeBlockFreshColumn σ,
        (X (threeBlockPermutationVariable σ j) +
          C (threeBlockEmb Q (σ j) j))) *
      C (threeBlockPermutationNonfreshProduct Q σ) := by
  have hfresh :
      (∏ j : ThreeBlockFreshColumn σ,
        threeBlockHPolynomial Q 0 (σ (j : ThreeBlockIndex w))
          (j : ThreeBlockIndex w)) =
        ∏ j : ThreeBlockFreshColumn σ,
          (X (threeBlockPermutationVariable σ j) +
            C (threeBlockEmb Q (σ j) j)) := by
    apply Fintype.prod_congr
    intro j
    simp [threeBlockHPolynomial_zero_apply,
      threeBlockPermutationVariable, j.2]
  have hnonfresh :
      (∏ j : {j : ThreeBlockIndex w //
          ¬threeBlockFresh (σ j) j},
        threeBlockHPolynomial Q 0 (σ (j : ThreeBlockIndex w))
          (j : ThreeBlockIndex w)) =
        C (threeBlockPermutationNonfreshProduct Q σ) := by
    change (∏ j : {j : ThreeBlockIndex w //
        ¬threeBlockFresh (σ j) j},
      threeBlockHPolynomial Q 0 (σ (j : ThreeBlockIndex w))
        (j : ThreeBlockIndex w)) =
      C (∏ j : {j : ThreeBlockIndex w //
        ¬threeBlockFresh (σ j) j},
          threeBlockEmb Q (σ j) j)
    calc
      _ = ∏ j : {j : ThreeBlockIndex w //
          ¬threeBlockFresh (σ j) j},
            C (threeBlockEmb Q (σ j) j) := by
        apply Fintype.prod_congr
        intro j
        simp [threeBlockHPolynomial_zero_apply, j.2]
      _ = _ := by
        simp
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun j : ThreeBlockIndex w => threeBlockFresh (σ j) j)
    (fun j => threeBlockHPolynomial Q 0 (σ j) j),
    hfresh, hnonfresh]

/-- Exact coefficient of one Leibniz product.  It is zero unless the target
mask lies in the permutation graph; otherwise it is the complementary
product of deterministic entries. -/
theorem coeff_threeBlockPermutationPolynomialProduct
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (S : Finset (ThreeBlockVariable w))
    (σ : Equiv.Perm (ThreeBlockIndex w)) :
    coeff (squarefreeExponent S)
        (∏ j, threeBlockHPolynomial Q 0 (σ j) j) =
      threeBlockPermutationNonfreshProduct Q σ *
        (if S ⊆
            Finset.univ.image (threeBlockPermutationVariable σ) then
          ∏ j : ThreeBlockFreshColumn σ with
              threeBlockPermutationVariable σ j ∉ S,
            threeBlockEmb Q (σ j) j
        else 0) := by
  rw [threeBlockPermutationPolynomialProduct_eq, mul_comm,
    coeff_C_mul, coeff_prod_X_add_C_of_injective
      (threeBlockPermutationVariable σ)
      (threeBlockPermutationVariable_injective σ)]

/-- The literal Leibniz/matching expansion of an actual determinant
coefficient. -/
def threeBlockMatchingExpansion
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (S : Finset (ThreeBlockVariable w)) : ℂ :=
  ∑ σ : Equiv.Perm (ThreeBlockIndex w),
    Equiv.Perm.sign σ •
      (threeBlockPermutationNonfreshProduct Q σ *
        if S ⊆
            Finset.univ.image (threeBlockPermutationVariable σ) then
          ∏ j : ThreeBlockFreshColumn σ with
              threeBlockPermutationVariable σ j ∉ S,
            threeBlockEmb Q (σ j) j
        else 0)

theorem threeBlockDetCoefficient_zero_eq_matchingExpansion
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (S : Finset (ThreeBlockVariable w)) :
    threeBlockDetCoefficient Q 0 S =
      threeBlockMatchingExpansion Q S := by
  rw [threeBlockDetCoefficient, threeBlockDetPolynomial, Matrix.det_apply]
  simp only [coeff_sum, coeff_smul]
  apply Finset.sum_congr rfl
  intro σ _
  exact congrArg (fun z : ℂ => Equiv.Perm.sign σ • z)
    (coeff_threeBlockPermutationPolynomialProduct Q S σ)

end PermutationExpansion

section ValidMatching

variable {w : Type*} [Fintype w] [DecidableEq w]

/-- Rows occupied by a squarefree fresh monomial. -/
def threeBlockMatchingRows (S : Finset (ThreeBlockVariable w)) :
    Finset (ThreeBlockIndex w) :=
  S.image (fun e => e.1.1)

/-- Columns occupied by a squarefree fresh monomial. -/
def threeBlockMatchingCols (S : Finset (ThreeBlockVariable w)) :
    Finset (ThreeBlockIndex w) :=
  S.image (fun e => e.1.2)

/-- A valid determinant monomial: distinct selected entries have distinct
rows and columns, and all central coordinates are selected. -/
def IsValidThreeBlockMatching (S : Finset (ThreeBlockVariable w)) : Prop :=
  Set.InjOn (fun e : ThreeBlockVariable w => e.1.1) S ∧
  Set.InjOn (fun e : ThreeBlockVariable w => e.1.2) S ∧
  (∀ i : w, Sum.inr i ∈ threeBlockMatchingRows S) ∧
  (∀ j : w, Sum.inr j ∈ threeBlockMatchingCols S)

/-- The finite type of genuine atom monomials. -/
abbrev ValidThreeBlockMatching (w : Type*) [Fintype w] [DecidableEq w] :=
  {S : Finset (ThreeBlockVariable w) // IsValidThreeBlockMatching S}

instance : Fintype (ValidThreeBlockMatching w) := Fintype.ofFinite _

/-- Outer rows left for the deterministic `Q`-minor. -/
def threeBlockUnmatchedOuterRows (S : Finset (ThreeBlockVariable w)) :
    Finset (ThreeBlockOuter w) :=
  Finset.univ.filter (fun i =>
    Sum.inl i ∉ threeBlockMatchingRows S)

/-- Outer columns left for the deterministic `Q`-minor. -/
def threeBlockUnmatchedOuterCols (S : Finset (ThreeBlockVariable w)) :
    Finset (ThreeBlockOuter w) :=
  Finset.univ.filter (fun j =>
    Sum.inl j ∉ threeBlockMatchingCols S)

theorem threeBlockMatchingRows_card (a : ValidThreeBlockMatching w) :
    (threeBlockMatchingRows a.1).card = a.1.card := by
  exact Finset.card_image_of_injOn a.2.1

theorem threeBlockMatchingCols_card (a : ValidThreeBlockMatching w) :
    (threeBlockMatchingCols a.1).card = a.1.card := by
  exact Finset.card_image_of_injOn a.2.2.1

/-- Since all central rows are occupied, every unmatched full row is the
inclusion of a unique unmatched outer row. -/
theorem threeBlockUnmatchedOuterRows_image (a : ValidThreeBlockMatching w) :
    (threeBlockUnmatchedOuterRows a.1).image
        (fun i => (Sum.inl i : ThreeBlockIndex w)) =
      Finset.univ \ threeBlockMatchingRows a.1 := by
  ext i
  rcases i with i | i
  · simp [threeBlockUnmatchedOuterRows]
  · simp [threeBlockUnmatchedOuterRows, a.2.2.2.1 i]

/-- The analogous column statement. -/
theorem threeBlockUnmatchedOuterCols_image (a : ValidThreeBlockMatching w) :
    (threeBlockUnmatchedOuterCols a.1).image
        (fun j => (Sum.inl j : ThreeBlockIndex w)) =
      Finset.univ \ threeBlockMatchingCols a.1 := by
  ext j
  rcases j with j | j
  · simp [threeBlockUnmatchedOuterCols]
  · simp [threeBlockUnmatchedOuterCols, a.2.2.2.2 j]

/-- A partial permutation leaves equally many rows and columns; after the
central coordinates have been covered, these are precisely the outer rows
and columns of the `Q`-minor. -/
theorem threeBlockUnmatchedOuter_card_eq (a : ValidThreeBlockMatching w) :
    (threeBlockUnmatchedOuterRows a.1).card =
      (threeBlockUnmatchedOuterCols a.1).card := by
  have hrowImage := congrArg Finset.card
    (threeBlockUnmatchedOuterRows_image a)
  have hcolImage := congrArg Finset.card
    (threeBlockUnmatchedOuterCols_image a)
  rw [Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_sdiff_of_subset
      (Finset.subset_univ (threeBlockMatchingRows a.1))] at hrowImage
  rw [Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_sdiff_of_subset
      (Finset.subset_univ (threeBlockMatchingCols a.1))] at hcolImage
  rw [threeBlockMatchingRows_card a] at hrowImage
  rw [threeBlockMatchingCols_card a] at hcolImage
  omega

/-- The square minor selected by a valid atom monomial. -/
def threeBlockMatchingMinorIndex (a : ValidThreeBlockMatching w) :
    SquareMinorIndex (ThreeBlockOuter w) :=
  ⟨threeBlockUnmatchedOuterCols a.1,
    ⟨threeBlockUnmatchedOuterRows a.1, by
      simp [threeBlockUnmatchedOuter_card_eq a]⟩⟩

/-- The actual determinant coefficient restricted to valid atom monomials. -/
def threeBlockValidCoefficient
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (a : ValidThreeBlockMatching w) : ℂ :=
  threeBlockDetCoefficient Q 0 a.1

/-- Its finite squared energy. -/
def threeBlockValidCoefficientEnergy
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) : ℝ :=
  finiteEnergy (threeBlockValidCoefficient Q)

end ValidMatching

end BernoulliLinearAlgebra
