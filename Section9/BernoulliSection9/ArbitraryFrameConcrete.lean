import BernoulliSection9.ArbitraryFrameDeduction
import BernoulliSection9.TerminalReverse
import BernoulliLinearAlgebra.ConcreteBoundaryFinal
import BernoulliLinearAlgebra.ConcreteBoundaryExterior
import BernoulliLinearAlgebra.GlobalBoundarySquarefree
import BernoulliLinearAlgebra.GramVolumeReindex
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Interval

/-!
# Literal boundary polynomials in the arbitrary-frame deduction

This file constructs the exterior coefficient tensors occurring in Section
9.2 directly from the inverse-free boundary trace.  Coefficients are extracted
on the finite Boolean cube by Möbius inversion.  This avoids introducing a
caller-supplied coefficient tensor or a polynomial-valued inverse.
-/

open scoped BigOperators Matrix ComplexConjugate

noncomputable section

namespace BernoulliSection9

set_option maxHeartbeats 500000

open Filter Matrix Set Set.powersetCard MvPolynomial
open BernoulliLinearAlgebra

section BooleanCoefficient

variable {v : Type*} [Fintype v] [DecidableEq v]

/-- The `0`--`1` point associated with a finite set of variables. -/
def booleanCubePoint (T : Finset v) : v → ℂ :=
  fun i ↦ if i ∈ T then 1 else 0

/-- Möbius extraction of the squarefree coefficient indexed by `S`. -/
def booleanCoefficient (S : Finset v) (f : (v → ℂ) → ℂ) : ℂ :=
  (-1 : ℂ) ^ S.card *
    ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * f (booleanCubePoint T)

@[simp] theorem booleanCoefficient_zero (S : Finset v) :
    booleanCoefficient S (fun _ ↦ 0) = 0 := by
  simp [booleanCoefficient]

theorem booleanCoefficient_add (S : Finset v)
    (f g : (v → ℂ) → ℂ) :
    booleanCoefficient S (fun x ↦ f x + g x) =
      booleanCoefficient S f + booleanCoefficient S g := by
  simp only [booleanCoefficient, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib]

theorem booleanCoefficient_const_mul (S : Finset v) (a : ℂ)
    (f : (v → ℂ) → ℂ) :
    booleanCoefficient S (fun x ↦ a * f x) =
      a * booleanCoefficient S f := by
  unfold booleanCoefficient
  have hsum :
      (∑ T ∈ S.powerset,
          (-1 : ℂ) ^ T.card * (a * f (booleanCubePoint T))) =
        a * ∑ T ∈ S.powerset,
          (-1 : ℂ) ^ T.card * f (booleanCubePoint T) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [hsum]
  ring

theorem booleanCoefficient_finset_sum {i : Type*} (S : Finset v)
    (t : Finset i) (f : i → (v → ℂ) → ℂ) :
    booleanCoefficient S (fun x ↦ ∑ j ∈ t, f j x) =
      ∑ j ∈ t, booleanCoefficient S (f j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert j t hj ih =>
      simp only [Finset.sum_insert hj]
      rw [booleanCoefficient_add, ih]

theorem booleanCoefficient_congr (S : Finset v)
    {f g : (v → ℂ) → ℂ} (h : ∀ x, f x = g x) :
    booleanCoefficient S f = booleanCoefficient S g := by
  unfold booleanCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro T _
  rw [h]

theorem booleanCubePoint_monomial (A T : Finset v) :
    (∏ i ∈ A, booleanCubePoint T i) = if A ⊆ T then 1 else 0 := by
  by_cases h : A ⊆ T
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [booleanCubePoint, h hi]
  · rw [if_neg h]
    rcases Finset.not_subset.mp h with ⟨i, hiA, hiT⟩
    exact Finset.prod_eq_zero hiA (by simp [booleanCubePoint, hiT])

private theorem alternating_interval_sum (A S : Finset v) (hAS : A ⊆ S) :
    ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
        (if A ⊆ T then 1 else 0) =
      if A = S then (-1 : ℂ) ^ A.card else 0 := by
  classical
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  rw [← Finset.Icc_eq_filter_powerset A S]
  rw [Finset.Icc_eq_image_powerset hAS]
  rw [Finset.sum_image]
  · have hcard : ∀ T ∈ (S \ A).powerset,
        (A ∪ T).card = A.card + T.card := by
      intro T hT
      exact Finset.card_union_of_disjoint
        (Finset.disjoint_of_subset_right
          (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff)
    have hsumCard :
        (∑ T ∈ (S \ A).powerset, (-1 : ℂ) ^ (A ∪ T).card) =
          ∑ T ∈ (S \ A).powerset,
            (-1 : ℂ) ^ (A.card + T.card) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [hcard T hT]
    rw [hsumCard]
    have hfactor :
        (∑ T ∈ (S \ A).powerset,
            (-1 : ℂ) ^ (A.card + T.card)) =
          (-1 : ℂ) ^ A.card *
            ∑ T ∈ (S \ A).powerset, (-1 : ℂ) ^ T.card := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      rw [pow_add]
    rw [hfactor]
    have halt :
        (∑ T ∈ (S \ A).powerset, (-1 : ℂ) ^ T.card) =
          if S \ A = ∅ then 1 else 0 := by
      exact_mod_cast
        (Finset.sum_powerset_neg_one_pow_card (x := S \ A))
    rw [halt]
    by_cases hEq : A = S
    · subst A
      simp
    · have hdiff : S \ A ≠ ∅ := by
        intro hzero
        have hSA : S ⊆ A :=
          Finset.sdiff_eq_empty_iff_subset.mp hzero
        exact hEq (Finset.Subset.antisymm hAS hSA)
      simp [hEq, hdiff]
  · intro T hT U hU hEq
    apply Finset.disjoint_injOn_union_left A
      (Finset.disjoint_of_subset_right
        (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff)
      (Finset.disjoint_of_subset_right
        (Finset.mem_powerset.mp hU) Finset.disjoint_sdiff)
    simpa [Finset.union_comm] using hEq

/-- Möbius extraction is Kronecker on squarefree monomials. -/
theorem booleanCoefficient_squarefreeMonomial (S A : Finset v) :
    booleanCoefficient S (fun x ↦ ∏ i ∈ A, x i) =
      if A = S then 1 else 0 := by
  unfold booleanCoefficient
  simp_rw [booleanCubePoint_monomial]
  by_cases hAS : A ⊆ S
  · rw [alternating_interval_sum A S hAS]
    by_cases h : A = S
    · subst A
      simp only [if_true]
      rw [← pow_add]
      have hcard : S.card + S.card = 2 * S.card := by omega
      rw [hcard, pow_mul]
      norm_num
    · simp [h]
  · have hz : ∀ T ∈ S.powerset, ¬ A ⊆ T := by
      intro T hT hAT
      exact hAS (hAT.trans (Finset.mem_powerset.mp hT))
    have hsum :
        (∑ T ∈ S.powerset,
            (-1 : ℂ) ^ T.card * if A ⊆ T then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro T hT
      rw [if_neg (hz T hT), mul_zero]
    rw [hsum, mul_zero, if_neg]
    exact fun hEq ↦ hAS hEq.le

/-- Boolean Möbius inversion recovers every coefficient of a squarefree
polynomial. -/
theorem booleanCoefficient_eval_eq_coeff
    (p : MvPolynomial v ℂ) (hp : HasSquarefreeSupport p)
    (S : Finset v) :
    booleanCoefficient S (fun x ↦ MvPolynomial.eval x p) =
      coeff (squarefreeExponent S) p := by
  let c : CoeffSpace v :=
    WithLp.toLp 2 (fun A ↦ coeff (squarefreeExponent A) p)
  have hpEq : squarefreePolynomial c = p := by
    simpa [c] using squarefreePolynomial_coefficients_eq p hp
  rw [← hpEq]
  rw [show (fun x ↦ MvPolynomial.eval x (squarefreePolynomial c)) =
      (fun x ↦ TerminalAssembly.evalComplexSquarefree
        (fun A ↦ c A) x) by
    funext x
    exact TerminalAssembly.eval_squarefreePolynomial_eq_evalComplexSquarefree c x]
  rw [coeff_squarefreePolynomial]
  unfold TerminalAssembly.evalComplexSquarefree
  rw [booleanCoefficient_finset_sum]
  simp_rw [booleanCoefficient_const_mul,
    booleanCoefficient_squarefreeMonomial]
  rw [Finset.sum_eq_single S]
  · simp [c]
  · intro A _ hAS
    simp [hAS]
  · simp

end BooleanCoefficient

section ExteriorTraceCoefficients

theorem booleanCoefficient_mul_const {v : Type*} [Fintype v] [DecidableEq v]
    (S : Finset v) (f : (v → ℂ) → ℂ) (a : ℂ) :
    booleanCoefficient S (fun x ↦ f x * a) = booleanCoefficient S f * a := by
  simpa [mul_comm] using booleanCoefficient_const_mul S a f

/-- Rebundle a diagonal sum indexed by all finite subsets into the usual
finite sum of traces over exterior degree. -/
theorem finsetDiagonalSum_eq_degreeTrace
    {iota : Type*} [Fintype iota] [DecidableEq iota] [LinearOrder iota]
    (M : (k : ℕ) →
      Matrix (powersetCard iota k) (powersetCard iota k) ℂ) :
    (∑ s : Finset iota, M s.card (ofCard rfl) (ofCard rfl)) =
      ∑ k ∈ Finset.range (Fintype.card iota + 1), Matrix.trace (M k) := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ)
    (t := Finset.range (Fintype.card iota + 1))
    (g := Finset.card) (fun s : Finset iota ↦ by
      intro _
      simp only [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.card_le_univ s))]
  apply Finset.sum_congr rfl
  intro k _
  unfold Matrix.trace
  refine Finset.sum_bij
    (s := Finset.univ.filter (fun s : Finset iota ↦ s.card = k))
    (t := Finset.univ)
    (fun s hs ↦
      (⟨s, (Finset.mem_filter.mp hs).2⟩ : powersetCard iota k)) ?_ ?_ ?_ ?_
  · intro _ _
    simp
  · intro s₁ _ s₂ _ h
    exact congrArg Subtype.val h
  · intro s _
    refine ⟨s.val, ?_, ?_⟩
    · simp
    · apply Subtype.ext
      rfl
  · intro s hs
    have hcard : s.card = k := (Finset.mem_filter.mp hs).2
    subst k
    rfl

theorem finsetSignedDiagonalSum_eq_degreeTrace
    {iota : Type*} [Fintype iota] [DecidableEq iota] [LinearOrder iota]
    (M : (k : ℕ) →
      Matrix (powersetCard iota k) (powersetCard iota k) ℂ) :
    (∑ s : Finset iota, (-1 : ℂ) ^ s.card *
        M s.card (ofCard rfl) (ofCard rfl)) =
      ∑ k ∈ Finset.range (Fintype.card iota + 1),
        (-1 : ℂ) ^ k * Matrix.trace (M k) := by
  simpa [Matrix.trace, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum] using
    (finsetDiagonalSum_eq_degreeTrace
      (fun k ↦ (-1 : ℂ) ^ k • M k))

variable {W : Type*} [Fintype W] [LinearOrder W]

local instance arbitraryFrameConcreteVariableDecidableEq :
    DecidableEq (ThreeBlockVariable W) := Subtype.instDecidableEq

local instance arbitraryFrameConcreteSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W ↦ (toLex x : W ⊕ₗ W)) toLex.injective

/-- The three literal companion steps appearing in the inverse-free boundary
trace after evaluation of the seven fresh packet blocks. -/
def literalBoundaryCompanionSteps
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (x : ThreeBlockVariable W → ℂ) : List (CompanionStep W) :=
  boundaryCompanionSteps
    (threeBlockBL x) (threeBlockBC x) BR
    (threeBlockAL x - z • 1) (threeBlockAC x - z • 1)
    (threeBlockAR x - z • 1) CL (threeBlockCC x) (threeBlockCR x)

/-- The coefficient tensor `Q_b^(k)` extracted directly from the
denominator-free exterior product.  No inverse, chart, or certificate occurs
in this definition. -/
def literalBoundaryExteriorTensor
    (z : ℂ) (CL BR : Matrix W W ℂ) (k : ℕ)
    (S : Finset (ThreeBlockVariable W)) :
    Matrix (powersetCard (W ⊕ W) k) (powersetCard (W ⊕ W) k) ℂ :=
  fun i j ↦ booleanCoefficient S (fun x ↦
    polynomialClearedCompoundProduct k
      (literalBoundaryCompanionSteps z CL BR x) i j)

private theorem booleanCoefficient_mulMatrix_diagonal
    (z : ℂ) (CL BR : Matrix W W ℂ) (k : ℕ)
    (S : Finset (ThreeBlockVariable W))
    (B : Matrix (powersetCard (W ⊕ W) k)
      (powersetCard (W ⊕ W) k) ℂ)
    (i : powersetCard (W ⊕ W) k) :
    booleanCoefficient S (fun x ↦
        (polynomialClearedCompoundProduct k
          (literalBoundaryCompanionSteps z CL BR x) * B) i i) =
      (literalBoundaryExteriorTensor z CL BR k S * B) i i := by
  simp only [Matrix.mul_apply]
  rw [booleanCoefficient_finset_sum]
  simp_rw [booleanCoefficient_mul_const]
  rfl

/-- Literal coefficient identity from (7.42) and (7.44): every squarefree coefficient of
the displayed five-block determinant is the finite signed trace of the
internally constructed inverse-free exterior tensors. -/
theorem coeff_globalBoundaryDetPolynomial_eq_exteriorTrace
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (S : Finset (ThreeBlockVariable W)) :
    coeff (squarefreeExponent S)
        (globalBoundaryDetPolynomial z CL BR Theta) =
      ∑ k ∈ Finset.range (Fintype.card (W ⊕ W) + 1),
        (-1 : ℂ) ^ k * Matrix.trace
          (literalBoundaryExteriorTensor z CL BR k S * compound k Theta) := by
  calc
    coeff (squarefreeExponent S)
        (globalBoundaryDetPolynomial z CL BR Theta) =
        booleanCoefficient S (fun x ↦ MvPolynomial.eval x
          (globalBoundaryDetPolynomial z CL BR Theta)) :=
      (booleanCoefficient_eval_eq_coeff
        (globalBoundaryDetPolynomial z CL BR Theta)
        (hasSquarefreeSupport_globalBoundaryDetPolynomial z CL BR Theta) S).symm
    _ = booleanCoefficient S (fun x ↦ polynomialClearedBoundaryTrace
          (literalBoundaryCompanionSteps z CL BR x) Theta) := by
      apply booleanCoefficient_congr
      intro x
      simpa only [literalBoundaryCompanionSteps] using
        (eval_globalBoundaryDetPolynomial_eq_polynomialClearedBoundaryTrace
          z CL BR Theta x)
    _ = ∑ k ∈ Finset.range (Fintype.card (W ⊕ W) + 1),
          (-1 : ℂ) ^ k * Matrix.trace
            (literalBoundaryExteriorTensor z CL BR k S * compound k Theta) := by
      unfold polynomialClearedBoundaryTrace
      rw [booleanCoefficient_finset_sum]
      simp_rw [booleanCoefficient_const_mul]
      simp_rw [booleanCoefficient_mulMatrix_diagonal]
      exact finsetSignedDiagonalSum_eq_degreeTrace
        (fun k ↦ literalBoundaryExteriorTensor z CL BR k S * compound k Theta)

/-- The coefficient obtained by contracting the internally constructed
exterior tensors against a boundary relation. -/
def literalBoundaryExteriorCoefficient
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (S : Finset (ThreeBlockVariable W)) : ℂ :=
  ∑ k ∈ Finset.range (Fintype.card (W ⊕ W) + 1),
    (-1 : ℂ) ^ k * Matrix.trace
      (literalBoundaryExteriorTensor z CL BR k S * compound k Theta)

/-- The corresponding complete squarefree coefficient vector. -/
def literalBoundaryExteriorCoeffVector
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    CoeffSpace (ThreeBlockVariable W) :=
  WithLp.toLp 2 (literalBoundaryExteriorCoefficient z CL BR Theta)

/-- Its Euclidean norm. -/
def literalBoundaryExteriorCoefficientNorm
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) : ℝ :=
  ‖literalBoundaryExteriorCoeffVector z CL BR Theta‖

theorem literalBoundaryExteriorCoefficient_eq_coeff
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (S : Finset (ThreeBlockVariable W)) :
    literalBoundaryExteriorCoefficient z CL BR Theta S =
      coeff (squarefreeExponent S)
        (globalBoundaryDetPolynomial z CL BR Theta) := by
  exact (coeff_globalBoundaryDetPolynomial_eq_exteriorTrace
    z CL BR Theta S).symm

theorem literalBoundaryExteriorCoeffVector_eq_global
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    literalBoundaryExteriorCoeffVector z CL BR Theta =
      globalBoundaryCoeffVector z CL BR Theta := by
  ext S
  exact literalBoundaryExteriorCoefficient_eq_coeff z CL BR Theta S

/-- The exterior construction has literally the globally defined coefficient
norm; no norm-comparison or coefficient certificate is needed. -/
theorem literalBoundaryExteriorCoefficientNorm_eq_global
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    literalBoundaryExteriorCoefficientNorm z CL BR Theta =
      globalBoundaryCoefficientNorm z CL BR Theta := by
  rw [literalBoundaryExteriorCoefficientNorm,
    literalBoundaryExteriorCoeffVector_eq_global,
    globalBoundaryCoefficientNorm]

/-- Evaluation of the finite squarefree monomial basis. -/
def literalBoundaryMonomial
    (S : Finset (ThreeBlockVariable W))
    (x : ThreeBlockVariable W → ℂ) : ℂ :=
  ∏ i ∈ S, x i

/-- The polynomial value assembled from the inverse-free exterior tensors. -/
def literalBoundaryExteriorPolynomialValue
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (x : ThreeBlockVariable W → ℂ) : ℂ :=
  ∑ S : Finset (ThreeBlockVariable W),
    literalBoundaryExteriorCoefficient z CL BR Theta S *
      literalBoundaryMonomial S x

/-- The exterior-tensor polynomial is pointwise the literal displayed
five-block determinant polynomial. -/
theorem literalBoundaryExteriorPolynomialValue_eq_eval
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (x : ThreeBlockVariable W → ℂ) :
    literalBoundaryExteriorPolynomialValue z CL BR Theta x =
      MvPolynomial.eval x (globalBoundaryDetPolynomial z CL BR Theta) := by
  calc
    literalBoundaryExteriorPolynomialValue z CL BR Theta x =
        TerminalAssembly.evalComplexSquarefree
          (fun S ↦ globalBoundaryCoeffVector z CL BR Theta S) x := by
      unfold literalBoundaryExteriorPolynomialValue
      unfold TerminalAssembly.evalComplexSquarefree literalBoundaryMonomial
      apply Finset.sum_congr rfl
      intro S _
      rw [literalBoundaryExteriorCoefficient_eq_coeff]
      change coeff (squarefreeExponent S)
          (globalBoundaryDetPolynomial z CL BR Theta) * _ =
        globalBoundaryCoeffVector z CL BR Theta S * _
      rw [globalBoundaryCoeffVector_apply]
    _ = MvPolynomial.eval x
        (squarefreePolynomial (globalBoundaryCoeffVector z CL BR Theta)) :=
      (TerminalAssembly.eval_squarefreePolynomial_eq_evalComplexSquarefree
        (globalBoundaryCoeffVector z CL BR Theta) x).symm
    _ = MvPolynomial.eval x
        (globalBoundaryDetPolynomial z CL BR Theta) := by
      rw [← globalBoundaryDetPolynomial_eq_squarefreePolynomial]

end ExteriorTraceCoefficients

section SelectedExteriorLimit

variable {iota : Type*} [Fintype iota] [DecidableEq iota] [LinearOrder iota]

/-- Number of selected directions occurring in an exterior coordinate. -/
def selectedCount {r k : ℕ} (L : powersetCard iota r)
    (s : powersetCard iota k) : ℕ :=
  (Finset.univ.filter fun j : Fin k ↦
    ofFinEmbEquiv.symm s j ∈ L.val).card

theorem selectedCount_le_degree {r k : ℕ}
    (L : powersetCard iota r) (s : powersetCard iota k) :
    selectedCount L s ≤ k := by
  unfold selectedCount
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin k))
    (fun j : Fin k ↦ ofFinEmbEquiv.symm s j ∈ L.val)

theorem selectedCount_le_rank {r k : ℕ}
    (L : powersetCard iota r) (s : powersetCard iota k) :
    selectedCount L s ≤ r := by
  classical
  let chosen : Finset iota :=
    (Finset.univ.filter fun j : Fin k ↦
      ofFinEmbEquiv.symm s j ∈ L.val).map
        (ofFinEmbEquiv.symm s).toEmbedding
  have hsub : chosen ⊆ L.val := by
    intro x hx
    simp only [chosen, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    rcases hx with ⟨j, hj, rfl⟩
    exact hj
  have hc := Finset.card_le_card hsub
  simpa [chosen, selectedCount, L.prop] using hc

theorem selectedCount_eq_rank_iff {r : ℕ}
    (L s : powersetCard iota r) :
    selectedCount L s = r ↔ s = L := by
  classical
  constructor
  · intro hc
    have hall :
        Finset.univ.filter (fun j : Fin r ↦
          ofFinEmbEquiv.symm s j ∈ L.val) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      simpa only [Finset.card_univ, Fintype.card_fin, selectedCount] using hc.ge
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases (mem_range_ofFinEmbEquiv_symm_iff_mem s x).mpr hx with ⟨j, hj⟩
      have hmem : ofFinEmbEquiv.symm s j ∈ L.val := by
        have : j ∈ Finset.univ.filter (fun q : Fin r ↦
            ofFinEmbEquiv.symm s q ∈ L.val) := by
          rw [hall]
          simp
        simpa using (Finset.mem_filter.mp this).2
      simpa [← hj] using hmem
    · simpa [s.prop, L.prop]
  · intro hs
    subst s
    unfold selectedCount
    have hall : ∀ j : Fin r, ofFinEmbEquiv.symm L j ∈ L.val := by
      intro j
      simpa [ofFinEmbEquiv_symm_apply] using
        (Finset.orderEmbOfFin_mem L.val L.prop j)
    rw [Finset.filter_eq_self.mpr (fun j _ ↦ hall j)]
    simp

/-- Diagonal amplification along an arbitrary selected `r`-subset. -/
def selectedAmplificationDiagonal {r : ℕ}
    (L : powersetCard iota r) (lambda : ℂ) : Matrix iota iota ℂ :=
  Matrix.diagonal fun i ↦ if i ∈ L.val then lambda else lambda⁻¹

theorem selectedAmplificationDiagonal_det_isUnit {r : ℕ}
    (L : powersetCard iota r) (lambda : ℂ) (hlambda : lambda ≠ 0) :
    IsUnit (selectedAmplificationDiagonal L lambda).det := by
  rw [selectedAmplificationDiagonal, Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ by
    split_ifs
    · exact hlambda
    · exact inv_ne_zero hlambda

theorem selectedAmplification_product_eq {r k : ℕ}
    (L : powersetCard iota r) (s : powersetCard iota k) (x : ℂ) :
    (∏ j : Fin k,
      if ofFinEmbEquiv.symm s j ∈ L.val then x⁻¹ else x) =
      x⁻¹ ^ selectedCount L s * x ^ (k - selectedCount L s) := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  congr 2
  unfold selectedCount
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k)))
    (fun j : Fin k ↦ ofFinEmbEquiv.symm s j ∈ L.val)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  have hle := Finset.card_filter_le (Finset.univ : Finset (Fin k))
    (fun j : Fin k ↦ ofFinEmbEquiv.symm s j ∈ L.val)
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  omega

theorem normalized_selectedAmplification_product_eq {r k : ℕ}
    (L : powersetCard iota r) (s : powersetCard iota k)
    (x : ℂ) (hx : x ≠ 0) :
    x ^ r * (∏ j : Fin k,
      if ofFinEmbEquiv.symm s j ∈ L.val then x⁻¹ else x) =
      x ^ ((r - selectedCount L s) + (k - selectedCount L s)) := by
  rw [selectedAmplification_product_eq]
  rw [← mul_assoc, inv_pow]
  rw [← pow_sub₀ x hx (selectedCount_le_rank L s)]
  rw [← pow_add]

/-- The normalized diagonal exterior matrix along the cofinal sequence. -/
def normalizedSelectedDiagonalCompound {r : ℕ}
    (L : powersetCard iota r) (k q : ℕ) :
    Matrix (powersetCard iota k) (powersetCard iota k) ℂ :=
  inverseNaturalLambda q ^ r •
    compound k (selectedAmplificationDiagonal L (naturalLambda q))

theorem normalizedSelectedDiagonalCompound_apply {r k q : ℕ}
    (L : powersetCard iota r)
    (s t : powersetCard iota k) :
    normalizedSelectedDiagonalCompound L k q s t =
      if s = t then inverseNaturalLambda q ^
        ((r - selectedCount L s) + (k - selectedCount L s)) else 0 := by
  classical
  rw [normalizedSelectedDiagonalCompound, Matrix.smul_apply,
    selectedAmplificationDiagonal, compound_diagonal_apply]
  by_cases hst : s = t
  · rw [if_pos hst, if_pos hst]
    subst t
    simp only [naturalLambda, inv_inv, smul_eq_mul]
    exact normalized_selectedAmplification_product_eq L s
      (inverseNaturalLambda q) (inverseNaturalLambda_ne_zero q)
  · simp [hst]

/-- Rank-one coordinate projection onto the selected exterior coordinate. -/
def selectedExteriorProjection {r : ℕ} (L : powersetCard iota r) :
    Matrix (powersetCard iota r) (powersetCard iota r) ℂ :=
  fun s t ↦ if s = L ∧ t = L then 1 else 0

theorem normalizedSelectedDiagonalCompound_otherDegree_tendsto
    {r k : ℕ} (L : powersetCard iota r) (hkr : k ≠ r)
    (s t : powersetCard iota k) :
    Tendsto (fun q ↦ normalizedSelectedDiagonalCompound L k q s t)
      atTop (nhds 0) := by
  by_cases hst : s = t
  · subst t
    rw [show (fun q ↦ normalizedSelectedDiagonalCompound L k q s s) =
        (fun q ↦ inverseNaturalLambda q ^
          ((r - selectedCount L s) + (k - selectedCount L s))) by
      funext q
      simp [normalizedSelectedDiagonalCompound_apply]]
    have har := selectedCount_le_rank L s
    have hak := selectedCount_le_degree L s
    have he : 0 < (r - selectedCount L s) +
        (k - selectedCount L s) := by omega
    simpa [zero_pow he.ne'] using inverseNaturalLambda_tendsto.pow
      ((r - selectedCount L s) + (k - selectedCount L s))
  · rw [show (fun q ↦ normalizedSelectedDiagonalCompound L k q s t) =
        (fun _ ↦ 0) by
      funext q
      simp [normalizedSelectedDiagonalCompound_apply, hst]]
    exact tendsto_const_nhds

theorem normalizedSelectedDiagonalCompound_rankDegree_tendsto
    {r : ℕ} (L : powersetCard iota r)
    (s t : powersetCard iota r) :
    Tendsto (fun q ↦ normalizedSelectedDiagonalCompound L r q s t)
      atTop (nhds (selectedExteriorProjection L s t)) := by
  by_cases hst : s = t
  · subst t
    by_cases hs : s = L
    · subst s
      have hc : selectedCount L L = r :=
        (selectedCount_eq_rank_iff L L).2 rfl
      rw [show (fun q ↦ normalizedSelectedDiagonalCompound L r q L L) =
          (fun _ ↦ 1) by
        funext q
        simp [normalizedSelectedDiagonalCompound_apply, hc]]
      simpa [selectedExteriorProjection] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (nhds 1))
    · rw [show (fun q ↦ normalizedSelectedDiagonalCompound L r q s s) =
          (fun q ↦ inverseNaturalLambda q ^
            ((r - selectedCount L s) + (r - selectedCount L s))) by
        funext q
        simp [normalizedSelectedDiagonalCompound_apply]]
      have ha := selectedCount_le_rank L s
      have hane : selectedCount L s ≠ r := by
        simpa [selectedCount_eq_rank_iff] using hs
      have he : 0 < (r - selectedCount L s) +
          (r - selectedCount L s) := by omega
      have ht := inverseNaturalLambda_tendsto.pow
        ((r - selectedCount L s) + (r - selectedCount L s))
      simpa [zero_pow he.ne', selectedExteriorProjection, hs] using ht
  · rw [show (fun q ↦ normalizedSelectedDiagonalCompound L r q s t) =
        (fun _ ↦ 0) by
      funext q
      simp [normalizedSelectedDiagonalCompound_apply, hst]]
    have hp : selectedExteriorProjection L s t = 0 := by
      rw [selectedExteriorProjection, if_neg]
      intro hb
      exact hst (hb.1.trans hb.2.symm)
    rw [hp]
    exact tendsto_const_nhds

/-- Artificial boundary relation in an arbitrary finite coordinate type,
with the selected exterior coordinate `L`. -/
def selectedArtificialTheta {r : ℕ} (L : powersetCard iota r)
    (A B : Matrix iota iota ℂ) (lambda : ℂ) : Matrix iota iota ℂ :=
  A * selectedAmplificationDiagonal L lambda * B

/-- Normalized exterior power of the selected artificial relation. -/
def normalizedSelectedArtificialCompound {r : ℕ}
    (L : powersetCard iota r) (A B : Matrix iota iota ℂ)
    (k q : ℕ) :
    Matrix (powersetCard iota k) (powersetCard iota k) ℂ :=
  inverseNaturalLambda q ^ r •
    compound k (selectedArtificialTheta L A B (naturalLambda q))

theorem normalizedSelectedArtificialCompound_eq {r : ℕ}
    (L : powersetCard iota r) (A B : Matrix iota iota ℂ)
    (k q : ℕ) :
    normalizedSelectedArtificialCompound L A B k q =
      compound k A * normalizedSelectedDiagonalCompound L k q *
        compound k B := by
  rw [normalizedSelectedArtificialCompound, selectedArtificialTheta,
    compound_mul, compound_mul, normalizedSelectedDiagonalCompound]
  rw [mul_smul_comm, smul_mul_assoc]

/-- The limiting rank-one exterior operator for the selected coordinate. -/
def selectedArtificialExteriorRankOne {r : ℕ}
    (L : powersetCard iota r) (A B : Matrix iota iota ℂ) :
    Matrix (powersetCard iota r) (powersetCard iota r) ℂ :=
  compound r A * selectedExteriorProjection L * compound r B

theorem normalizedSelectedArtificialCompound_otherDegree_tendsto
    {r k : ℕ} (L : powersetCard iota r)
    (A B : Matrix iota iota ℂ) (hkr : k ≠ r)
    (s t : powersetCard iota k) :
    Tendsto (fun q ↦ normalizedSelectedArtificialCompound L A B k q s t)
      atTop (nhds 0) := by
  rw [show (fun q ↦ normalizedSelectedArtificialCompound L A B k q s t) =
      (fun q ↦ (compound k A * normalizedSelectedDiagonalCompound L k q *
        compound k B) s t) by
    funext q
    rw [normalizedSelectedArtificialCompound_eq]]
  have ht := tendsto_fixed_mul_entry
    (compound k A) (compound k B)
    (0 : Matrix (powersetCard iota k) (powersetCard iota k) ℂ)
    (fun q ↦ normalizedSelectedDiagonalCompound L k q)
    (fun i j ↦
      normalizedSelectedDiagonalCompound_otherDegree_tendsto L hkr i j) s t
  simpa using ht

theorem normalizedSelectedArtificialCompound_rankDegree_tendsto
    {r : ℕ} (L : powersetCard iota r)
    (A B : Matrix iota iota ℂ)
    (s t : powersetCard iota r) :
    Tendsto (fun q ↦ normalizedSelectedArtificialCompound L A B r q s t)
      atTop (nhds (selectedArtificialExteriorRankOne L A B s t)) := by
  rw [show (fun q ↦ normalizedSelectedArtificialCompound L A B r q s t) =
      (fun q ↦ (compound r A * normalizedSelectedDiagonalCompound L r q *
        compound r B) s t) by
    funext q
    rw [normalizedSelectedArtificialCompound_eq]]
  exact tendsto_fixed_mul_entry
    (compound r A) (compound r B) (selectedExteriorProjection L)
    (fun q ↦ normalizedSelectedDiagonalCompound L r q)
    (fun i j ↦
      normalizedSelectedDiagonalCompound_rankDegree_tendsto L i j) s t

section SelectedCoefficientLimit

variable {a : Type*} [Fintype a]

/-- Coefficients of the normalized artificial polynomial in an arbitrary
finite coordinate type. -/
def selectedNormalizedExteriorCoefficient {r : ℕ}
    (L : powersetCard iota r) (A B : Matrix iota iota ℂ)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard iota k) (powersetCard iota k) ℂ)
    (q : ℕ) (b : a) : ℂ :=
  ∑ k ∈ Finset.range (Fintype.card iota + 1), (-1 : ℂ) ^ k *
    Matrix.trace (Q k b * normalizedSelectedArtificialCompound L A B k q)

/-- Limiting arbitrary-frame coefficient in the selected coordinate model. -/
def selectedLimitingFrameCoefficient {r : ℕ}
    (L : powersetCard iota r) (A B : Matrix iota iota ℂ)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard iota k) (powersetCard iota k) ℂ)
    (b : a) : ℂ :=
  (-1 : ℂ) ^ r * Matrix.trace
    (Q r b * selectedArtificialExteriorRankOne L A B)

theorem selectedNormalizedExteriorCoefficient_tendsto {r : ℕ}
    (L : powersetCard iota r) (A B : Matrix iota iota ℂ)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard iota k) (powersetCard iota k) ℂ)
    (b : a) :
    Tendsto (fun q ↦ selectedNormalizedExteriorCoefficient L A B Q q b)
      atTop (nhds (selectedLimitingFrameCoefficient L A B Q b)) := by
  let z : ℂ := selectedLimitingFrameCoefficient L A B Q b
  have hterm : ∀ k ∈ Finset.range (Fintype.card iota + 1),
      Tendsto (fun q ↦ (-1 : ℂ) ^ k * Matrix.trace
        (Q k b * normalizedSelectedArtificialCompound L A B k q))
        atTop (nhds (if k = r then z else 0)) := by
    intro k hk
    by_cases hkr : k = r
    · subst k
      have ht := tendsto_trace_mul (Q r b)
        (selectedArtificialExteriorRankOne L A B)
        (fun q ↦ normalizedSelectedArtificialCompound L A B r q)
        (fun i j ↦ normalizedSelectedArtificialCompound_rankDegree_tendsto
          L A B i j)
      simpa [z, selectedLimitingFrameCoefficient] using
        ht.const_mul ((-1 : ℂ) ^ r)
    · have ht := tendsto_trace_mul (Q k b)
        (0 : Matrix (powersetCard iota k) (powersetCard iota k) ℂ)
        (fun q ↦ normalizedSelectedArtificialCompound L A B k q)
        (fun i j ↦ normalizedSelectedArtificialCompound_otherDegree_tendsto
          L A B hkr i j)
      simpa [hkr] using ht.const_mul ((-1 : ℂ) ^ k)
  have hsum := tendsto_finset_sum
    (Finset.range (Fintype.card iota + 1)) hterm
  have hrle : r ≤ Fintype.card iota := by
    simpa [L.prop] using Finset.card_le_univ L.val
  have hrmem : r ∈ Finset.range (Fintype.card iota + 1) := by
    simpa [Finset.mem_range, Nat.lt_succ_iff] using hrle
  simpa [selectedNormalizedExteriorCoefficient,
    selectedLimitingFrameCoefficient, z, hrmem] using hsum

private theorem trace_mul_smul_right
    {d : Type*} [Fintype d] (Q C : Matrix d d ℂ) (a : ℂ) :
    Matrix.trace (Q * (a • C)) = a * Matrix.trace (Q * C) := by
  rw [mul_smul_comm]
  simp [Matrix.trace, Finset.mul_sum]

/-- Pull the common normalization scalar outside the finite exterior-degree
coefficient sum. -/
theorem selectedNormalizedExteriorCoefficient_eq_scaled {r : ℕ}
    (L : powersetCard iota r) (A B : Matrix iota iota ℂ)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard iota k) (powersetCard iota k) ℂ)
    (q : ℕ) (b : a) :
    selectedNormalizedExteriorCoefficient L A B Q q b =
      inverseNaturalLambda q ^ r *
        ∑ k ∈ Finset.range (Fintype.card iota + 1), (-1 : ℂ) ^ k *
          Matrix.trace (Q k b * compound k
            (selectedArtificialTheta L A B (naturalLambda q))) := by
  unfold selectedNormalizedExteriorCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [normalizedSelectedArtificialCompound,
    trace_mul_smul_right]
  ring

def selectedNormalizedExteriorCoefficientNorm {r : ℕ}
    (L : powersetCard iota r) (A B : Matrix iota iota ℂ)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard iota k) (powersetCard iota k) ℂ)
    (q : ℕ) : ℝ :=
  ‖(WithLp.toLp 2
    (fun b ↦ selectedNormalizedExteriorCoefficient L A B Q q b) :
      EuclideanSpace ℂ a)‖

def selectedFrameCoefficientNorm {r : ℕ}
    (L : powersetCard iota r) (A B : Matrix iota iota ℂ)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard iota k) (powersetCard iota k) ℂ) : ℝ :=
  ‖(WithLp.toLp 2
    (fun b ↦ selectedLimitingFrameCoefficient L A B Q b) :
      EuclideanSpace ℂ a)‖

theorem selectedNormalizedExteriorCoefficientNorm_tendsto {r : ℕ}
    (L : powersetCard iota r) (A B : Matrix iota iota ℂ)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard iota k) (powersetCard iota k) ℂ) :
    Tendsto (selectedNormalizedExteriorCoefficientNorm L A B Q)
      atTop (nhds (selectedFrameCoefficientNorm L A B Q)) := by
  exact finiteCoefficientNorm_tendsto _ _
    (fun b ↦ selectedNormalizedExteriorCoefficient_tendsto L A B Q b)

end SelectedCoefficientLimit

end SelectedExteriorLimit

section CommonScaleConclusion

open MeasureTheory

/-- All fields of the terminal conclusion are invariant under multiplying
both the coefficient norm and the polynomial value by one common nonzero
complex scalar.  This invariance of the complete conclusion record allows
the artificial-frame passage to use one terminal input for every value of
the amplification parameter. -/
noncomputable def TerminalSmallBallConclusion.commonScale
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {coefficientNorm baseLoss badProbability : ℝ} {value : Omega → ℂ}
    (C : TerminalSmallBallConclusion mu coefficientNorm value
      baseLoss badProbability)
    (a : ℂ) (ha : a ≠ 0) :
    TerminalSmallBallConclusion mu (‖a‖ * coefficientNorm)
      (fun omega ↦ a * value omega) baseLoss badProbability := by
  have hnormA : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnormA0 : ‖a‖ ≠ 0 := hnormA.ne'
  have hcoefficient0 : coefficientNorm ≠ 0 := C.coefficientNorm_pos.ne'
  refine
    { coefficientNorm_pos := mul_pos hnormA C.coefficientNorm_pos
      capped := ?_
      zero_probability := ?_
      reverse_event := C.reverse_event
      reverse := ?_
      parseval := ?_ }
  · intro T hT
    have hfun :
        (fun omega ↦ cappedLogLoss T (‖a‖ * coefficientNorm)
          (a * value omega)) =
        (fun omega ↦ cappedLogLoss T coefficientNorm (value omega)) := by
      funext omega
      exact cappedLogLoss_common_scale T coefficientNorm (value omega) a ha
    rw [hfun]
    exact C.capped T hT
  · have hset : {omega | a * value omega = 0} =
        {omega | value omega = 0} := by
      ext omega
      exact common_scale_eq_zero_iff (value omega) a ha
    rw [hset]
    exact C.zero_probability
  · intro omega homega
    have hratio :
        ‖a * value omega‖ / (‖a‖ * coefficientNorm) =
          ‖value omega‖ / coefficientNorm := by
      rw [norm_mul]
      field_simp [hnormA0, hcoefficient0]
    rw [hratio]
    exact C.reverse omega homega
  · calc
      (‖a‖ * coefficientNorm) ^ 2 =
          ‖a‖ ^ 2 * coefficientNorm ^ 2 := by ring
      _ = ‖a‖ ^ 2 * ∫ omega, ‖value omega‖ ^ 2 ∂mu := by
        rw [C.parseval]
      _ = ∫ omega, ‖a‖ ^ 2 * ‖value omega‖ ^ 2 ∂mu := by
        rw [MeasureTheory.integral_const_mul]
      _ = ∫ omega, ‖a * value omega‖ ^ 2 ∂mu := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with omega
        rw [norm_mul]
        ring

end CommonScaleConclusion

section LiteralArtificialFrames

/-- The canonical rebracketing of the two `W` endpoint blocks as the paper's
ambient `2W` coordinates. -/
def boundaryCoordinateEquiv (W : ℕ) :
    (Fin W ⊕ Fin W) ≃ Fin (2 * W) :=
  finSumFinEquiv.trans (finCongr (Nat.two_mul W).symm)

local instance literalArtificialSumLinearOrder (W : ℕ) :
    LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift'
    (fun x : Fin W ⊕ Fin W ↦ (toLex x : Fin W ⊕ₗ Fin W))
    toLex.injective

/-- The selected endpoint coordinate corresponding to the first `r`
directions in the internally completed frame. -/
def boundaryLeadingPowerset {W r : ℕ} (h : r ≤ 2 * W) :
    powersetCard (Fin W ⊕ Fin W) r :=
  powersetCard.map r (boundaryCoordinateEquiv W).symm.toEmbedding
    (leadingPowerset h)

/-- Reindex the internally selected unitary completion into the literal
left/right endpoint coordinates used by the boundary determinant. -/
def boundaryCompletedFrameMatrix {W r : ℕ}
    (U : ComplexFrame r (2 * W)) (h : r ≤ 2 * W) :
    Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ :=
  Matrix.reindex (boundaryCoordinateEquiv W).symm
    (boundaryCoordinateEquiv W).symm (completedFrameMatrix U h)

/-- The selected diagonal is exactly the standard leading-coordinate
diagonal after the canonical endpoint reindexing. -/
theorem selectedAmplificationDiagonal_boundaryLeading_eq_reindex
    {W r : ℕ} (h : r ≤ 2 * W) (lambda : ℂ) :
    selectedAmplificationDiagonal (boundaryLeadingPowerset h) lambda =
      Matrix.reindex (boundaryCoordinateEquiv W).symm
        (boundaryCoordinateEquiv W).symm
        (amplificationDiagonal (n := 2 * W) r lambda) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [selectedAmplificationDiagonal, boundaryLeadingPowerset,
      powersetCard.map, amplificationDiagonal, Matrix.reindex_apply,
      leadingPowerset]
  · simp [selectedAmplificationDiagonal, amplificationDiagonal,
      Matrix.reindex_apply, hij]

theorem boundaryCompletedFrameMatrix_det_isUnit {W r : ℕ}
    (U : ComplexFrame r (2 * W)) (h : r ≤ 2 * W) :
    IsUnit (boundaryCompletedFrameMatrix U h).det := by
  rw [boundaryCompletedFrameMatrix, Matrix.det_reindex_self]
  exact completedFrameMatrix_det_isUnit U h

/-- The literal endpoint-coordinate artificial relation
`Theta_lambda^(r;U,V)`.  Both completions remain internal. -/
def literalArtificialTheta {W r : ℕ}
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (lambda : ℂ) : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ :=
  selectedArtificialTheta (boundaryLeadingPowerset h)
    (boundaryCompletedFrameMatrix V h)
    ((boundaryCompletedFrameMatrix U h)ᴴ) lambda

/-- The literal endpoint-coordinate artificial relation is the canonical
simultaneous reindexing of equation (9.47). -/
theorem literalArtificialTheta_eq_reindex {W r : ℕ}
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (lambda : ℂ) :
    literalArtificialTheta U V h lambda =
      Matrix.reindex (boundaryCoordinateEquiv W).symm
        (boundaryCoordinateEquiv W).symm
        (artificialTheta U V h lambda) := by
  let R := Matrix.reindexRingEquiv ℂ (boundaryCoordinateEquiv W).symm
  have hstar :
      (R (completedFrameMatrix U h))ᴴ =
        R ((completedFrameMatrix U h)ᴴ) := by
    ext i j
    rfl
  rw [literalArtificialTheta, selectedArtificialTheta,
    selectedAmplificationDiagonal_boundaryLeading_eq_reindex,
    boundaryCompletedFrameMatrix, artificialTheta]
  change R (completedFrameMatrix V h) *
      R (amplificationDiagonal (n := 2 * W) r lambda) *
        (R (completedFrameMatrix U h))ᴴ =
    R (completedFrameMatrix V h *
      amplificationDiagonal (n := 2 * W) r lambda *
        (completedFrameMatrix U h)ᴴ)
  rw [hstar, map_mul, map_mul]

/-- Simultaneous endpoint reindexing does not change the artificial graph
volume. -/
theorem gramVolume_literalArtificialTheta_eq {W r : ℕ}
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (lambda : ℂ) :
    gramVolume (literalArtificialTheta U V h lambda) =
      gramVolume (artificialTheta U V h lambda) := by
  rw [literalArtificialTheta_eq_reindex]
  exact gramVolume_submatrix_equiv
    (boundaryCoordinateEquiv W) (artificialTheta U V h lambda)

/-- Left and right unitary factors preserve the determinant defining the
Gram energy. -/
theorem gramEnergy_unitary_mul_mul
    {iota : Type*} [Fintype iota] [DecidableEq iota] [LinearOrder iota]
    (A M B : Matrix iota iota ℂ)
    (hA : A ∈ Matrix.unitaryGroup iota ℂ)
    (hB : B ∈ Matrix.unitaryGroup iota ℂ) :
    gramEnergy (A * M * B) = gramEnergy M := by
  have hAstarA : Aᴴ * A = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hA)
  have hBstarB : Bᴴ * B = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hB)
  have hgram :
      1 + (A * M * B)ᴴ * (A * M * B) =
        Bᴴ * (1 + Mᴴ * M) * B := by
    calc
      1 + (A * M * B)ᴴ * (A * M * B) =
          1 + Bᴴ * Mᴴ * (Aᴴ * A) * M * B := by
        simp only [Matrix.conjTranspose_mul]
        noncomm_ring
      _ = 1 + Bᴴ * (Mᴴ * M) * B := by
        rw [hAstarA]
        noncomm_ring
      _ = Bᴴ * (1 + Mᴴ * M) * B := by
        rw [Matrix.mul_add, Matrix.add_mul]
        simp only [Matrix.mul_one]
        rw [hBstarB]
  have hdetB : (Bᴴ).det * B.det = 1 := by
    rw [← Matrix.det_mul, hBstarB, Matrix.det_one]
  have hdet :
      (Bᴴ * (1 + Mᴴ * M) * B).det =
        (1 + Mᴴ * M).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    calc
      (Bᴴ).det * (1 + Mᴴ * M).det * B.det =
          (1 + Mᴴ * M).det * ((Bᴴ).det * B.det) := by ring
      _ = (1 + Mᴴ * M).det := by rw [hdetB, mul_one]
  unfold gramEnergy
  rw [hgram, hdet]

/-- Consequently both completed frames disappear from the artificial Gram
energy. -/
theorem gramEnergy_artificialTheta_eq_amplification {W r : ℕ}
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (lambda : ℂ) :
    gramEnergy (artificialTheta U V h lambda) =
      gramEnergy (amplificationDiagonal (n := 2 * W) r lambda) := by
  rw [artificialTheta]
  apply gramEnergy_unitary_mul_mul
  · exact completedFrameMatrix_mem_unitary V h
  · simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.star_mem (completedFrameMatrix_mem_unitary U h)

/-- Exact singular-value product for the standard diagonal amplification. -/
theorem gramEnergy_amplificationDiagonal {n r : ℕ} (h : r ≤ n)
    (lambda : ℂ) :
    gramEnergy (amplificationDiagonal (n := n) r lambda) =
      (1 + ‖lambda‖ ^ 2) ^ r *
        (1 + ‖lambda⁻¹‖ ^ 2) ^ (n - r) := by
  let g : Fin n → ℝ := fun i ↦
    if i.val < r then 1 + ‖lambda‖ ^ 2 else 1 + ‖lambda⁻¹‖ ^ 2
  have hstarMul (x : ℂ) :
      star x * x = (((‖x‖ ^ 2 : ℝ) : ℂ)) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have hmatrix :
      1 + (amplificationDiagonal (n := n) r lambda)ᴴ *
          amplificationDiagonal (n := n) r lambda =
        Matrix.diagonal (fun i ↦ ((g i : ℝ) : ℂ)) := by
    rw [amplificationDiagonal, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one,
      Matrix.diagonal_add]
    congr 1
    funext i
    by_cases hi : i.val < r
    · simp only [g, hi, if_pos, Pi.star_apply]
      rw [hstarMul]
      norm_cast
    · simp only [g, hi, if_neg, Pi.star_apply]
      rw [hstarMul]
      norm_cast
  have hselected :
      ((Finset.univ.filter fun i : Fin n ↦ i.val < r).card) = r := by
    simpa [min_eq_right h] using
      (Fin.card_filter_val_lt (n := n) (m := r))
  have hunselected :
      ((Finset.univ.filter fun i : Fin n ↦ ¬ i.val < r).card) = n - r := by
    have hc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n ↦ i.val < r)
    simp only [Finset.card_univ, Fintype.card_fin, hselected] at hc
    omega
  unfold gramEnergy
  rw [hmatrix, Matrix.det_diagonal]
  rw [← Complex.ofReal_prod]
  rw [Complex.ofReal_re]
  unfold g
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, hselected, hunselected]

theorem norm_inverseNaturalLambda_eq_real (q : ℕ) :
    ‖inverseNaturalLambda q‖ = inverseNaturalLambdaReal q := by
  have hden : ‖((q : ℂ) + 1)‖ = (q : ℝ) + 1 := by
    rw [show (q : ℂ) + 1 = (((q : ℝ) + 1 : ℝ) : ℂ) by norm_num]
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  unfold inverseNaturalLambda inverseNaturalLambdaReal
  rw [norm_div, norm_one, hden]

theorem norm_naturalLambda_eq_real_inv (q : ℕ) :
    ‖naturalLambda q‖ = (inverseNaturalLambdaReal q)⁻¹ := by
  rw [naturalLambda, norm_inv, norm_inverseNaturalLambda_eq_real]

theorem norm_naturalLambda_inv_eq_real (q : ℕ) :
    ‖(naturalLambda q)⁻¹‖ = inverseNaturalLambdaReal q := by
  rw [naturalLambda, inv_inv, norm_inverseNaturalLambda_eq_real]

/-- Equation (9.54) for the literal artificial boundary relation. -/
theorem normalized_literalArtificialTheta_gramVolume {W r : ℕ}
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W) (q : ℕ) :
    ‖inverseNaturalLambda q ^ r‖ *
        gramVolume (literalArtificialTheta U V h (naturalLambda q)) =
      normalizedGraphProduct W q := by
  have hvolumeSq :
      gramVolume (literalArtificialTheta U V h (naturalLambda q)) ^ 2 =
        (1 + ‖naturalLambda q‖ ^ 2) ^ r *
          (1 + ‖(naturalLambda q)⁻¹‖ ^ 2) ^ (2 * W - r) := by
    rw [gramVolume_literalArtificialTheta_eq,
      gramVolume_sq, gramEnergy_artificialTheta_eq_amplification,
      gramEnergy_amplificationDiagonal h]
  have hleftSq :
      (‖inverseNaturalLambda q ^ r‖ *
          gramVolume (literalArtificialTheta U V h (naturalLambda q))) ^ 2 =
        normalizedGraphMultiplicityProduct W r q := by
    rw [mul_pow, norm_pow, hvolumeSq,
      norm_inverseNaturalLambda_eq_real,
      norm_naturalLambda_eq_real_inv,
      norm_naturalLambda_inv_eq_real,
      normalizedGraphMultiplicityProduct]
    rw [show (inverseNaturalLambdaReal q ^ r) ^ 2 =
        (inverseNaturalLambdaReal q ^ 2) ^ r by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm r 2]]
    ring
  have hsquare :
      (‖inverseNaturalLambda q ^ r‖ *
          gramVolume (literalArtificialTheta U V h (naturalLambda q))) ^ 2 =
        normalizedGraphProduct W q ^ 2 := by
    rw [hleftSq, normalizedGraphProduct_sq_eq_multiplicityProduct W r q h]
  apply (sq_eq_sq₀
    (mul_nonneg (norm_nonneg _) (gramVolume_nonneg _))
    (by unfold normalizedGraphProduct; positivity)).mp
  exact hsquare

/-- The fully explicit coefficient--volume comparison constant inherited
from the literal terminal polynomial and the two endpoint factors. -/
def literalBoundaryFrameComparisonConstant (W : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  threeBlockConcreteComparisonConstant (W := Fin W) z *
    endpointExteriorConstant CL BR

theorem literalBoundaryFrameComparisonConstant_one_le
    (W : ℕ) (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ) :
    1 ≤ literalBoundaryFrameComparisonConstant W z CL BR := by
  apply one_le_mul_of_one_le_of_one_le
  · unfold threeBlockConcreteComparisonConstant
    exact one_le_mul_of_one_le_of_one_le
      (threeBlockZeroComparisonConstant_one_le (w := Fin W))
      (threeBlockTranslationFactor_one_le (w := Fin W) z)
  · exact one_le_exactExteriorConditioningConstant
      (endpointFactor CL BR)

theorem literalBoundaryFrameComparisonConstant_pos
    (W : ℕ) (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ) :
    0 < literalBoundaryFrameComparisonConstant W z CL BR :=
  zero_lt_one.trans_le
    (literalBoundaryFrameComparisonConstant_one_le W z CL BR)

theorem literalArtificialTheta_det_isUnit {W r : ℕ}
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (lambda : ℂ) (hlambda : lambda ≠ 0) :
    IsUnit (literalArtificialTheta U V h lambda).det := by
  rw [literalArtificialTheta, selectedArtificialTheta,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  exact ((boundaryCompletedFrameMatrix_det_isUnit V h).mul
    (selectedAmplificationDiagonal_det_isUnit
      (boundaryLeadingPowerset h) lambda hlambda)).mul
        (boundaryCompletedFrameMatrix_det_isUnit U h).star

/-- The concrete inverse-free tensors for the literal boundary polynomial. -/
def literalBoundaryFrameTensor (W : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (k : ℕ) (S : Finset (ThreeBlockVariable (Fin W))) :
    Matrix (powersetCard (Fin W ⊕ Fin W) k)
      (powersetCard (Fin W ⊕ Fin W) k) ℂ :=
  literalBoundaryExteriorTensor z CL BR k S

/-- Normalized coefficients of the actual artificial boundary determinant,
expressed entirely through the internally constructed literal tensors. -/
def literalArtificialCoefficient {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (q : ℕ) (S : Finset (ThreeBlockVariable (Fin W))) : ℂ :=
  selectedNormalizedExteriorCoefficient
    (boundaryLeadingPowerset h)
    (boundaryCompletedFrameMatrix V h)
    ((boundaryCompletedFrameMatrix U h)ᴴ)
    (literalBoundaryFrameTensor W z CL BR) q S

/-- The limiting arbitrary-frame boundary coefficient obtained from the
literal inverse-free tensors. -/
def literalFrameCoefficient {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (S : Finset (ThreeBlockVariable (Fin W))) : ℂ :=
  selectedLimitingFrameCoefficient
    (boundaryLeadingPowerset h)
    (boundaryCompletedFrameMatrix V h)
    ((boundaryCompletedFrameMatrix U h)ᴴ)
    (literalBoundaryFrameTensor W z CL BR) S

/-- Equation (9.53) for the actual boundary polynomial, with neither `Q`
tensors nor a frame completion in the theorem signature. -/
theorem literalArtificialCoefficient_tendsto {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (S : Finset (ThreeBlockVariable (Fin W))) :
    Tendsto (fun q ↦ literalArtificialCoefficient z CL BR U V h q S)
      atTop (nhds (literalFrameCoefficient z CL BR U V h S)) := by
  exact selectedNormalizedExteriorCoefficient_tendsto
    (boundaryLeadingPowerset h)
    (boundaryCompletedFrameMatrix V h)
    ((boundaryCompletedFrameMatrix U h)ᴴ)
    (literalBoundaryFrameTensor W z CL BR) S

/-- The normalized artificial coefficient is literally the common scalar
`lambda_q^{-r}` times the coefficient of the actual displayed determinant. -/
theorem literalArtificialCoefficient_eq_scaled_coeff {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (q : ℕ) (S : Finset (ThreeBlockVariable (Fin W))) :
    literalArtificialCoefficient z CL BR U V h q S =
      inverseNaturalLambda q ^ r *
        coeff (squarefreeExponent S)
          (globalBoundaryDetPolynomial z CL BR
            (literalArtificialTheta U V h (naturalLambda q))) := by
  rw [literalArtificialCoefficient,
    selectedNormalizedExteriorCoefficient_eq_scaled]
  change inverseNaturalLambda q ^ r *
      literalBoundaryExteriorCoefficient z CL BR
        (literalArtificialTheta U V h (naturalLambda q)) S = _
  rw [literalBoundaryExteriorCoefficient_eq_coeff]

/-- Euclidean norm of the normalized actual artificial coefficients. -/
def literalArtificialCoefficientNorm {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (q : ℕ) : ℝ :=
  ‖(WithLp.toLp 2
    (literalArtificialCoefficient z CL BR U V h q) :
      EuclideanSpace ℂ (Finset (ThreeBlockVariable (Fin W))))‖

/-- Euclidean norm of the actual limiting arbitrary-frame coefficients. -/
def literalFrameCoefficientNorm {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W) : ℝ :=
  ‖(WithLp.toLp 2
    (literalFrameCoefficient z CL BR U V h) :
      EuclideanSpace ℂ (Finset (ThreeBlockVariable (Fin W))))‖

/-- Exact scaled form of the artificial coefficient norm. -/
theorem literalArtificialCoefficientNorm_eq_scaled_global {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W) (q : ℕ) :
    literalArtificialCoefficientNorm z CL BR U V h q =
      ‖inverseNaturalLambda q ^ r‖ *
        globalBoundaryCoefficientNorm z CL BR
          (literalArtificialTheta U V h (naturalLambda q)) := by
  let a : ℂ := inverseNaturalLambda q ^ r
  have hvec :
      (WithLp.toLp 2
        (literalArtificialCoefficient z CL BR U V h q) :
          EuclideanSpace ℂ (Finset (ThreeBlockVariable (Fin W)))) =
        a • globalBoundaryCoeffVector z CL BR
          (literalArtificialTheta U V h (naturalLambda q)) := by
    ext S
    change literalArtificialCoefficient z CL BR U V h q S =
      a * globalBoundaryCoeffVector z CL BR
        (literalArtificialTheta U V h (naturalLambda q)) S
    rw [literalArtificialCoefficient_eq_scaled_coeff,
      globalBoundaryCoeffVector_apply]
  rw [literalArtificialCoefficientNorm, hvec, norm_smul,
    globalBoundaryCoefficientNorm]

/-- The concrete global coefficient comparison and equation (9.54) give the
two scaled estimates required by the limiting deduction, with no additional
certificate in the signature. -/
theorem literalArtificialCoefficientNorm_scaled_bounds {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W) (q : ℕ) :
    (literalBoundaryFrameComparisonConstant W z CL BR)⁻¹ *
          normalizedGraphProduct W q ≤
        literalArtificialCoefficientNorm z CL BR U V h q ∧
      literalArtificialCoefficientNorm z CL BR U V h q ≤
        literalBoundaryFrameComparisonConstant W z CL BR *
          normalizedGraphProduct W q := by
  let Theta := literalArtificialTheta U V h (naturalLambda q)
  let scale := ‖inverseNaturalLambda q ^ r‖
  have hLambda : naturalLambda q ≠ 0 :=
    inv_ne_zero (inverseNaturalLambda_ne_zero q)
  have hTheta : IsUnit Theta.det := by
    exact literalArtificialTheta_det_isUnit
      U V h (naturalLambda q) hLambda
  have hb := globalBoundaryCoefficientNorm_bounds_fullyInstantiated
    z CL BR hCL hBR Theta hTheta
  have hscale : 0 ≤ scale := norm_nonneg _
  have hvolume : scale * gramVolume Theta = normalizedGraphProduct W q := by
    exact normalized_literalArtificialTheta_gramVolume U V h q
  have hnorm : literalArtificialCoefficientNorm z CL BR U V h q =
      scale * globalBoundaryCoefficientNorm z CL BR Theta := by
    exact literalArtificialCoefficientNorm_eq_scaled_global
      z CL BR U V h q
  constructor
  · calc
      (literalBoundaryFrameComparisonConstant W z CL BR)⁻¹ *
          normalizedGraphProduct W q =
          scale * ((literalBoundaryFrameComparisonConstant W z CL BR)⁻¹ *
            gramVolume Theta) := by rw [← hvolume]; ring
      _ ≤ scale * globalBoundaryCoefficientNorm z CL BR Theta :=
        mul_le_mul_of_nonneg_left hb.1 hscale
      _ = literalArtificialCoefficientNorm z CL BR U V h q := hnorm.symm
  · calc
      literalArtificialCoefficientNorm z CL BR U V h q =
          scale * globalBoundaryCoefficientNorm z CL BR Theta := hnorm
      _ ≤ scale * (literalBoundaryFrameComparisonConstant W z CL BR *
          gramVolume Theta) := mul_le_mul_of_nonneg_left hb.2 hscale
      _ = literalBoundaryFrameComparisonConstant W z CL BR *
          normalizedGraphProduct W q := by rw [← hvolume]; ring

/-- Equation (9.55) for the literal boundary polynomial. -/
theorem literalArtificialCoefficientNorm_tendsto {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W) :
    Tendsto (literalArtificialCoefficientNorm z CL BR U V h)
      atTop (nhds (literalFrameCoefficientNorm z CL BR U V h)) := by
  exact finiteCoefficientNorm_tendsto _ _
    (fun S ↦ literalArtificialCoefficient_tendsto z CL BR U V h S)

/-- Pointwise evaluation of the normalized actual artificial polynomial. -/
def literalArtificialPolynomialValue {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (q : ℕ) (x : ThreeBlockVariable (Fin W) → ℂ) : ℂ :=
  ∑ S : Finset (ThreeBlockVariable (Fin W)),
    literalArtificialCoefficient z CL BR U V h q S *
      literalBoundaryMonomial S x

/-- Pointwise evaluation of the limiting actual arbitrary-frame polynomial. -/
def literalFramePolynomialValue {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (x : ThreeBlockVariable (Fin W) → ℂ) : ℂ :=
  ∑ S : Finset (ThreeBlockVariable (Fin W)),
    literalFrameCoefficient z CL BR U V h S * literalBoundaryMonomial S x

/-- The normalized artificial polynomial is literally the scaled displayed
five-block determinant, at every assignment of its fresh variables. -/
theorem literalArtificialPolynomialValue_eq_scaled_eval {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (q : ℕ) (x : ThreeBlockVariable (Fin W) → ℂ) :
    literalArtificialPolynomialValue z CL BR U V h q x =
      inverseNaturalLambda q ^ r * MvPolynomial.eval x
        (globalBoundaryDetPolynomial z CL BR
          (literalArtificialTheta U V h (naturalLambda q))) := by
  unfold literalArtificialPolynomialValue
  simp_rw [literalArtificialCoefficient_eq_scaled_coeff]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [← literalBoundaryExteriorPolynomialValue_eq_eval z CL BR
    (literalArtificialTheta U V h (naturalLambda q)) x]
  congr 1
  unfold literalBoundaryExteriorPolynomialValue
  apply Finset.sum_congr rfl
  intro S _
  rw [literalBoundaryExteriorCoefficient_eq_coeff]

/-- Equation (9.53), evaluated pointwise for the actual literal boundary
polynomial. -/
theorem literalArtificialPolynomialValue_tendsto {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (x : ThreeBlockVariable (Fin W) → ℂ) :
    Tendsto (fun q ↦ literalArtificialPolynomialValue z CL BR U V h q x)
      atTop (nhds (literalFramePolynomialValue z CL BR U V h x)) := by
  unfold literalArtificialPolynomialValue literalFramePolynomialValue
  apply tendsto_finset_sum Finset.univ
  intro S _
  exact (literalArtificialCoefficient_tendsto z CL BR U V h S).mul_const
    (literalBoundaryMonomial S x)

section LiteralRandomValues

open MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The actual iid assignment of the seven fresh packet blocks. -/
def literalBoundaryRandomAssignment {W : ℕ}
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W))) (omega : Omega) :
    ThreeBlockVariable (Fin W) → ℂ :=
  fun i ↦ (X.atom i omega : ℂ)

/-- The normalized literal artificial determinant evaluated at the iid
packet. -/
def literalArtificialRandomValue {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W))) (q : ℕ) (omega : Omega) : ℂ :=
  literalArtificialPolynomialValue z CL BR U V h q
    (literalBoundaryRandomAssignment X omega)

/-- The limiting arbitrary-frame polynomial evaluated at the same iid
packet. -/
def literalFrameRandomValue {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W))) (omega : Omega) : ℂ :=
  literalFramePolynomialValue z CL BR U V h
    (literalBoundaryRandomAssignment X omega)

theorem literalArtificialRandomValue_eq_evalSquarefree {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W))) (q : ℕ) (omega : Omega) :
    literalArtificialRandomValue z CL BR U V h X q omega =
      evalSquarefree (literalArtificialCoefficient z CL BR U V h q)
        X.atom omega := by
  simp [literalArtificialRandomValue, literalArtificialPolynomialValue,
    literalBoundaryRandomAssignment, literalBoundaryMonomial,
    evalSquarefree, squarefreeMonomial, Complex.ofReal_prod]

theorem literalFrameRandomValue_eq_evalSquarefree {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W))) (omega : Omega) :
    literalFrameRandomValue z CL BR U V h X omega =
      evalSquarefree (literalFrameCoefficient z CL BR U V h)
        X.atom omega := by
  simp [literalFrameRandomValue, literalFramePolynomialValue,
    literalBoundaryRandomAssignment, literalBoundaryMonomial,
    evalSquarefree, squarefreeMonomial, Complex.ofReal_prod]

theorem literalArtificialRandomValue_measurable {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W))) (q : ℕ) :
    Measurable (literalArtificialRandomValue z CL BR U V h X q) := by
  rw [show literalArtificialRandomValue z CL BR U V h X q =
      evalSquarefree (literalArtificialCoefficient z CL BR U V h q)
        X.atom by
    funext omega
    exact literalArtificialRandomValue_eq_evalSquarefree
      z CL BR U V h X q omega]
  exact TerminalAssembly.measurable_evalSquarefree _ _ X.measurable_atom

theorem literalFrameRandomValue_measurable {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W))) :
    Measurable (literalFrameRandomValue z CL BR U V h X) := by
  rw [show literalFrameRandomValue z CL BR U V h X =
      evalSquarefree (literalFrameCoefficient z CL BR U V h) X.atom by
    funext omega
    exact literalFrameRandomValue_eq_evalSquarefree
      z CL BR U V h X omega]
  exact TerminalAssembly.measurable_evalSquarefree _ _ X.measurable_atom

theorem literalArtificialRandomValue_tendsto {W r : ℕ}
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W))) (omega : Omega) :
    Tendsto (fun q ↦ literalArtificialRandomValue z CL BR U V h X q omega)
      atTop (nhds (literalFrameRandomValue z CL BR U V h X omega)) := by
  exact literalArtificialPolynomialValue_tendsto z CL BR U V h
    (literalBoundaryRandomAssignment X omega)

/-- The only probabilistic input needed by the concrete arbitrary-frame
bridge: the already assembled coordinate terminal theorem for the actual
displayed boundary determinant.  It is one theorem uniform in the boundary
relation, not a caller-supplied family of artificial certificates. -/
def LiteralCoordinateTerminalTheorem {W : ℕ}
    (mu : Measure Omega)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W)))
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (baseLoss badProbability : ℝ) :=
  ∀ Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ,
    IsUnit Theta.det →
      TerminalSmallBallConclusion mu
        (globalBoundaryCoefficientNorm z CL BR Theta)
        (fun omega ↦ MvPolynomial.eval
          (literalBoundaryRandomAssignment X omega)
          (globalBoundaryDetPolynomial z CL BR Theta))
        baseLoss badProbability

/-- A single concrete coordinate terminal theorem supplies every normalized
artificial relation internally.  In particular the signature contains no
`Q` tensor, monomial atom, completion, or `q`-indexed terminal family. -/
noncomputable def literalArtificialTerminalConclusion
    {W r : ℕ} [IsProbabilityMeasure mu]
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W)))
    (baseLoss badProbability : ℝ)
    (coordinateTerminal : LiteralCoordinateTerminalTheorem
      mu X z CL BR baseLoss badProbability) (q : ℕ) :
    TerminalSmallBallConclusion mu
      (literalArtificialCoefficientNorm z CL BR U V h q)
      (literalArtificialRandomValue z CL BR U V h X q)
      baseLoss badProbability := by
  let a : ℂ := inverseNaturalLambda q ^ r
  have ha : a ≠ 0 := pow_ne_zero r (inverseNaturalLambda_ne_zero q)
  have hLambda : naturalLambda q ≠ 0 :=
    inv_ne_zero (inverseNaturalLambda_ne_zero q)
  have C := coordinateTerminal
    (literalArtificialTheta U V h (naturalLambda q))
    (literalArtificialTheta_det_isUnit U V h (naturalLambda q) hLambda)
  have hscaled := C.commonScale a ha
  have hnorm : literalArtificialCoefficientNorm z CL BR U V h q =
      ‖a‖ * globalBoundaryCoefficientNorm z CL BR
        (literalArtificialTheta U V h (naturalLambda q)) := by
    simpa only [a] using
      (literalArtificialCoefficientNorm_eq_scaled_global
        z CL BR U V h q)
  have hvalue : literalArtificialRandomValue z CL BR U V h X q =
      (fun omega ↦ a * MvPolynomial.eval
        (literalBoundaryRandomAssignment X omega)
        (globalBoundaryDetPolynomial z CL BR
          (literalArtificialTheta U V h (naturalLambda q)))) := by
    funext omega
    unfold literalArtificialRandomValue
    simpa only [a] using
      (literalArtificialPolynomialValue_eq_scaled_eval
        z CL BR U V h q (literalBoundaryRandomAssignment X omega))
  rw [hnorm, hvalue]
  exact hscaled

/-- The complete limiting small-ball deduction for the literal boundary
polynomial.  Compared with the abstract deduction, the exterior tensors,
monomial atoms, frame completions, and the whole `q`-indexed terminal family
have all been constructed internally.  The two displayed deterministic
bounds are the exact remaining coefficient--volume estimates; the theorem
below is designed so that they can be discharged directly from the concrete
global boundary comparison and equation (9.54). -/
theorem literalArbitraryFrame_smallBall_deduction_of_scaled_bounds
    {W r : ℕ} [IsProbabilityMeasure mu]
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W)))
    (lower upper baseLoss badProbability : ℝ)
    (hlowerPos : 0 < lower) (hbase : 0 ≤ baseLoss)
    (hlower : ∀ q,
      lower * normalizedGraphProduct W q ≤
        literalArtificialCoefficientNorm z CL BR U V h q)
    (hupper : ∀ q,
      literalArtificialCoefficientNorm z CL BR U V h q ≤
        upper * normalizedGraphProduct W q)
    (coordinateTerminal : LiteralCoordinateTerminalTheorem
      mu X z CL BR baseLoss badProbability) :
    ArbitraryFrameDeductionConclusion mu
      (literalArtificialCoefficientNorm z CL BR U V h)
      (literalFrameCoefficientNorm z CL BR U V h)
      (literalArtificialRandomValue z CL BR U V h X)
      (literalFrameRandomValue z CL BR U V h X)
      lower upper baseLoss badProbability := by
  have hnorm : Tendsto
      (literalArtificialCoefficientNorm z CL BR U V h) atTop
      (nhds (literalFrameCoefficientNorm z CL BR U V h)) :=
    literalArtificialCoefficientNorm_tendsto z CL BR U V h
  have hvalue : ∀ omega, Tendsto
      (fun q ↦ literalArtificialRandomValue z CL BR U V h X q omega)
      atTop (nhds (literalFrameRandomValue z CL BR U V h X omega)) :=
    fun omega ↦ literalArtificialRandomValue_tendsto z CL BR U V h X omega
  have hbounds : lower ≤ literalFrameCoefficientNorm z CL BR U V h ∧
      literalFrameCoefficientNorm z CL BR U V h ≤ upper :=
    limit_mem_interval_of_scaled_bounds hnorm
      (normalizedGraphProduct_tendsto W) hlower hupper
  have hnormPos : 0 < literalFrameCoefficientNorm z CL BR U V h :=
    hlowerPos.trans_le hbounds.1
  have hterminal : ∀ q, TerminalSmallBallConclusion mu
      (literalArtificialCoefficientNorm z CL BR U V h q)
      (literalArtificialRandomValue z CL BR U V h X q)
      baseLoss badProbability :=
    fun q ↦ literalArtificialTerminalConclusion
      z CL BR U V h X baseLoss badProbability coordinateTerminal q
  have hseqMeas : ∀ q, AEStronglyMeasurable
      (literalArtificialRandomValue z CL BR U V h X q) mu :=
    fun q ↦ (literalArtificialRandomValue_measurable
      z CL BR U V h X q).aestronglyMeasurable
  have hframeMeas : Measurable
      (literalFrameRandomValue z CL BR U V h X) :=
    literalFrameRandomValue_measurable z CL BR U V h X
  have hcapped : ∀ T : ℝ, 0 < T →
      ∫ omega, cappedLogLoss T
          (literalFrameCoefficientNorm z CL BR U V h)
          (literalFrameRandomValue z CL BR U V h X omega) ∂mu ≤
        baseLoss + badProbability * T := by
    intro T hT
    exact cappedIntegral_limit_le_of_uniform_bound mu T hT.le hnorm hnormPos
      (fun q ↦ (hterminal q).coefficientNorm_pos) hseqMeas
      (Filter.Eventually.of_forall hvalue)
      (baseLoss + badProbability * T) (fun q ↦ (hterminal q).capped T hT)
  have hzero : mu.real
      {omega | literalFrameRandomValue z CL BR U V h X omega = 0} ≤
        badProbability := by
    apply zeroProbability_of_all_capped_bounds hbase
    intro T hT
    exact (cap_mul_zeroProbability_le_integral mu T
      (literalFrameCoefficientNorm z CL BR U V h) hT.le hnormPos
      (literalFrameRandomValue z CL BR U V h X) hframeMeas).trans
        (hcapped T hT)
  exact
    { coefficientNorm_limit := hnorm
      value_limit := hvalue
      coefficientNorm_pos := hnormPos
      coefficientNorm_bounds := hbounds
      capped := hcapped
      zero_probability := hzero }

/-- Concrete arbitrary-frame small-ball deduction.  All deterministic
coefficient bounds are discharged from the stable literal boundary
comparison and the exact normalized graph-volume identity.  The sole
probabilistic input is the genuine coordinate terminal theorem, uniform over
all invertible boundary relations. -/
theorem literalArbitraryFrame_smallBall_deduction
    {W r : ℕ} [IsProbabilityMeasure mu]
    (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W)))
    (baseLoss badProbability : ℝ) (hbase : 0 ≤ baseLoss)
    (coordinateTerminal : LiteralCoordinateTerminalTheorem
      mu X z CL BR baseLoss badProbability) :
    ArbitraryFrameDeductionConclusion mu
      (literalArtificialCoefficientNorm z CL BR U V h)
      (literalFrameCoefficientNorm z CL BR U V h)
      (literalArtificialRandomValue z CL BR U V h X)
      (literalFrameRandomValue z CL BR U V h X)
      (literalBoundaryFrameComparisonConstant W z CL BR)⁻¹
      (literalBoundaryFrameComparisonConstant W z CL BR)
      baseLoss badProbability := by
  apply literalArbitraryFrame_smallBall_deduction_of_scaled_bounds
    z CL BR U V h X
    (literalBoundaryFrameComparisonConstant W z CL BR)⁻¹
    (literalBoundaryFrameComparisonConstant W z CL BR)
    baseLoss badProbability
  · exact inv_pos.mpr
      (literalBoundaryFrameComparisonConstant_pos W z CL BR)
  · exact hbase
  · intro q
    exact (literalArtificialCoefficientNorm_scaled_bounds
      z CL BR hCL hBR U V h q).1
  · intro q
    exact (literalArtificialCoefficientNorm_scaled_bounds
      z CL BR hCL hBR U V h q).2
  · exact coordinateTerminal

end LiteralRandomValues

end LiteralArtificialFrames

end BernoulliSection9
