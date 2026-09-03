import ShortRingAnchor.SingularValues
import ShortRingAnchor.HardEdge
import ShortRingAnchor.EventualInputAdapters
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Hermitization and singular-value counting

This file supplies the deterministic bridge between the Hermitian dilation
used in v3 Corollary 3.5 and the small-singular-value count used in the proof
of v3 Proposition 3.6.

No probabilistic result is used here.  For a square complex matrix `B`, its
Hermitization is

`[[0, B], [Bᴴ, 0]]`.

The key linear-algebra fact is that each right singular vector of `B` gives
an eigenvector of this Hermitization with eigenvalue equal to the
corresponding singular value.  The resulting vectors are linearly
independent.  A finite-dimensional spectral-subspace argument therefore
bounds the number of singular values in `[0,a]` by the number of
Hermitization eigenvalues in `[-a,a]`.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

namespace ShortRingAnchor

open Module InnerProductSpace WithLp

/-- The `2n`-element index type of the Hermitian dilation. -/
abbrev HermitizationIndex (n : Nat) := Fin n ⊕ Fin n

@[simp]
theorem card_hermitizationIndex (n : Nat) :
    Fintype.card (HermitizationIndex n) = 2 * n := by
  simp [HermitizationIndex, two_mul]

/-- Hermitian dilation `[[0,B],[Bᴴ,0]]` of a square complex matrix. -/
def hermitization {n : Nat} (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ :=
  Matrix.fromBlocks 0 B B.conjTranspose 0

/-- The block dilation is Hermitian. -/
theorem hermitization_isHermitian {n : Nat}
    (B : Matrix (Fin n) (Fin n) ℂ) :
    (hermitization B).IsHermitian := by
  exact Matrix.IsHermitian.fromBlocks
    Matrix.isHermitian_zero rfl Matrix.isHermitian_zero

/-- The eigenvalues of the Hermitization, with algebraic multiplicity, in
mathlib's decreasing order. -/
def hermitizationEigenvalue {n : Nat}
    (B : Matrix (Fin n) (Fin n) ℂ) : HermitizationIndex n → Real :=
  (hermitization_isHermitian B).eigenvalues

/-- Indices of Hermitization eigenvalues in the symmetric interval
`[-a,a]`. -/
def smallHermitizationEigenvalueIndices {n : Nat}
    (B : Matrix (Fin n) (Fin n) ℂ) (a : Real) :
    Finset (HermitizationIndex n) :=
  Finset.univ.filter fun i => -a ≤ hermitizationEigenvalue B i ∧
    hermitizationEigenvalue B i ≤ a

/-- The spectral subspace spanned by the canonical eigenvectors whose
eigenvalues lie in `[-a,a]`. -/
def symmetricEigenvalueBandSubmodule
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {N : Nat}
    (hN : finrank ℂ E = N) (a : Real) : Submodule ℂ E :=
  Submodule.span ℂ (Set.range fun j :
    {j : Fin N // -a ≤ hT.eigenvalues hN j ∧ hT.eigenvalues hN j ≤ a} =>
      hT.eigenvectorBasis hN j.1)

/-- The dimension of the preceding spectral subspace is exactly the number
of canonical eigenvalues in `[-a,a]`, with multiplicity. -/
theorem finrank_symmetricEigenvalueBandSubmodule
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {N : Nat}
    (hN : finrank ℂ E = N) (a : Real) :
    finrank ℂ (symmetricEigenvalueBandSubmodule hT hN a) =
      (Finset.univ.filter fun j : Fin N =>
        -a ≤ hT.eigenvalues hN j ∧ hT.eigenvalues hN j ≤ a).card := by
  let J := {j : Fin N //
    -a ≤ hT.eigenvalues hN j ∧ hT.eigenvalues hN j ≤ a}
  have hli : LinearIndependent ℂ
      (fun j : J => hT.eigenvectorBasis hN j.1) :=
    (hT.eigenvectorBasis hN).toBasis.linearIndependent.comp
      (fun j : J => j.1) Subtype.val_injective
  rw [symmetricEigenvalueBandSubmodule]
  calc
    finrank ℂ (Submodule.span ℂ (Set.range fun j : J =>
        hT.eigenvectorBasis hN j.1)) = Fintype.card J :=
      finrank_span_eq_card hli
    _ = (Finset.univ.filter fun j : Fin N =>
        -a ≤ hT.eigenvalues hN j ∧ hT.eigenvalues hN j ≤ a).card := by
      apply Fintype.card_of_subtype
      intro j
      simp

/-- An eigenvector whose real eigenvalue lies in `[-a,a]` belongs to the
corresponding spectral band subspace. -/
theorem mem_symmetricEigenvalueBandSubmodule_of_apply_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {N : Nat}
    (hN : finrank ℂ E = N) (a mu : Real) (x : E)
    (hx : T x = (mu : ℂ) • x) (hmu : -a ≤ mu ∧ mu ≤ a) :
    x ∈ symmetricEigenvalueBandSubmodule hT hN a := by
  let b := (hT.eigenvectorBasis hN).toBasis
  rw [← b.sum_repr x]
  apply Submodule.sum_mem
  intro j _hj
  by_cases hj : -a ≤ hT.eigenvalues hN j ∧
      hT.eigenvalues hN j ≤ a
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
  · have hne : hT.eigenvalues hN j ≠ mu := by
      intro heq
      exact hj (heq ▸ hmu)
    have hcoordEq :
        (hT.eigenvalues hN j : ℂ) * (b.repr x) j =
          (mu : ℂ) * (b.repr x) j := by
      have h := congrArg (fun y : E => (b.repr y) j) hx
      calc
        (hT.eigenvalues hN j : ℂ) * (b.repr x) j =
            (b.repr (T x)) j := by
          symm
          exact hT.eigenvectorBasis_apply_self_apply hN x j
        _ = (b.repr ((mu : ℂ) • x)) j := h
        _ = (mu : ℂ) * (b.repr x) j := by
          rw [map_smul]
          rfl
    have hneC : (hT.eigenvalues hN j : ℂ) ≠ (mu : ℂ) := by
      exact_mod_cast hne
    have hcoord : (b.repr x) j = 0 := by
      have hzero :
          ((hT.eigenvalues hN j : ℂ) - (mu : ℂ)) * (b.repr x) j = 0 := by
        rw [sub_mul, hcoordEq, sub_self]
      exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hneC)
    simp [hcoord]

/-- A linearly independent family of eigenvectors in `[-a,a]` cannot be
larger than the canonical eigenvalue count in that interval.  This packages
the multiplicity bookkeeping used by the Hermitization argument. -/
theorem card_le_symmetricEigenvalueBand_of_linearIndependent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {N : Nat}
    (hN : finrank ℂ E = N) (a : Real)
    {kappa : Type*} [Fintype kappa]
    (v : kappa → E) (mu : kappa → Real)
    (hli : LinearIndependent ℂ v)
    (heigen : ∀ i, T (v i) = (mu i : ℂ) • v i)
    (hband : ∀ i, -a ≤ mu i ∧ mu i ≤ a) :
    Fintype.card kappa ≤
      (Finset.univ.filter fun j : Fin N =>
        -a ≤ hT.eigenvalues hN j ∧ hT.eigenvalues hN j ≤ a).card := by
  rw [← finrank_symmetricEigenvalueBandSubmodule hT hN a]
  rw [← finrank_span_eq_card hli]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact mem_symmetricEigenvalueBandSubmodule_of_apply_eq
    hT hN a (mu i) (v i) (heigen i) (hband i)

/-- A chosen orthonormal basis of right singular vectors.  It is the
eigenvector basis of `BᴴB` used by mathlib's definition of singular values. -/
def rightSingularVector {n : Nat}
    (B : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    EuclideanSpace ℂ (Fin n) :=
  B.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvectorBasis (by simp) i

/-- The defining Gram-operator equation for `rightSingularVector`. -/
theorem adjoint_apply_apply_rightSingularVector {n : Nat}
    (B : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    B.toEuclideanLin.adjoint
        (B.toEuclideanLin (rightSingularVector B i)) =
      ((matrixSingularValue B i.val : Real) : ℂ) ^ 2 •
        rightSingularVector B i := by
  let T := B.toEuclideanLin
  have heigen := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis (by simp) i
  have hsquare := T.sq_singularValues_fin (by simp) i
  change (T.adjoint ∘ₗ T) (rightSingularVector B i) = _ at heigen
  change T.singularValues i.val ^ 2 = _ at hsquare
  rw [← hsquare] at heigen
  simpa [T, rightSingularVector, matrixSingularValue,
    LinearMap.comp_apply, RCLike.real_smul_eq_coe_smul] using heigen

/-- Assemble two Euclidean vectors into the left and right blocks of the
dilation space. -/
def euclideanSumElim {n : Nat}
    (x y : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (HermitizationIndex n) :=
  toLp 2 (Sum.elim (ofLp x) (ofLp y))

@[simp]
theorem euclideanSumElim_inl {n : Nat}
    (x y : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    ofLp (euclideanSumElim x y) (Sum.inl i) = ofLp x i :=
  rfl

@[simp]
theorem euclideanSumElim_inr {n : Nat}
    (x y : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    ofLp (euclideanSumElim x y) (Sum.inr i) = ofLp y i :=
  rfl

@[simp]
theorem euclideanSumElim_zero (n : Nat) :
    euclideanSumElim (n := n) 0 0 = 0 := by
  apply PiLp.ext
  intro i
  cases i <;> rfl

/-- The Hermitization acts on block vectors by
`(x,y) ↦ (B y, Bᴴ x)`. -/
theorem hermitization_toEuclideanLin_apply_sumElim {n : Nat}
    (B : Matrix (Fin n) (Fin n) ℂ)
    (x y : EuclideanSpace ℂ (Fin n)) :
    (hermitization B).toEuclideanLin (euclideanSumElim x y) =
      euclideanSumElim
        (B.toEuclideanLin y) (B.toEuclideanLin.adjoint x) := by
  apply PiLp.ext
  intro k
  cases k with
  | inl i =>
      simp [hermitization, euclideanSumElim, Matrix.toLpLin_apply,
        Matrix.fromBlocks_mulVec]
  | inr i =>
      simp [hermitization, euclideanSumElim, Matrix.toLpLin_apply,
        Matrix.fromBlocks_mulVec]
      exact congrArg (fun T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
        EuclideanSpace ℂ (Fin n) => ofLp (T x) i)
          (Matrix.toEuclideanLin_conjTranspose_eq_adjoint B)

/-- Projection to the right block of the Euclidean dilation space. -/
def euclideanSumRight {n : Nat} :
    EuclideanSpace ℂ (HermitizationIndex n) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin n) where
  toFun x := toLp 2 fun i => ofLp x (Sum.inr i)
  map_add' x y := by
    apply PiLp.ext
    intro i
    rfl
  map_smul' c x := by
    apply PiLp.ext
    intro i
    rfl

@[simp]
theorem euclideanSumRight_sumElim {n : Nat}
    (x y : EuclideanSpace ℂ (Fin n)) :
    euclideanSumRight (euclideanSumElim x y) = y := by
  apply PiLp.ext
  intro i
  rfl

/-- For the `i`-th singular value `s`, use `(0,v)` when `s=0`, and
`(s⁻¹ Bv,v)` otherwise.  The right component is always the chosen right
singular vector, which makes linear independence immediate. -/
def singularHermitizationEigenvector {n : Nat}
    (B : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    EuclideanSpace ℂ (HermitizationIndex n) :=
  let s := matrixSingularValue B i.val
  let v := rightSingularVector B i
  if s = 0 then euclideanSumElim 0 v
  else euclideanSumElim ((s : ℂ)⁻¹ • B.toEuclideanLin v) v

@[simp]
theorem euclideanSumRight_singularHermitizationEigenvector {n : Nat}
    (B : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    euclideanSumRight (singularHermitizationEigenvector B i) =
      rightSingularVector B i := by
  dsimp [singularHermitizationEigenvector]
  by_cases hs : matrixSingularValue B i.val = 0 <;> simp [hs]

/-- The chosen right singular vectors form a basis and in particular are
linearly independent. -/
theorem linearIndependent_rightSingularVector {n : Nat}
    (B : Matrix (Fin n) (Fin n) ℂ) :
    LinearIndependent ℂ (rightSingularVector B) := by
  exact B.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvectorBasis
    (by simp) |>.toBasis.linearIndependent

/-- The `n` Hermitization vectors constructed from the right singular basis
are linearly independent. -/
theorem linearIndependent_singularHermitizationEigenvector {n : Nat}
    (B : Matrix (Fin n) (Fin n) ℂ) :
    LinearIndependent ℂ (singularHermitizationEigenvector B) := by
  apply LinearIndependent.of_comp euclideanSumRight
  simpa [Function.comp_def] using linearIndependent_rightSingularVector B

/-- Each constructed vector is a Hermitization eigenvector, with eigenvalue
equal to the corresponding (nonnegative) singular value.  This includes the
zero-singular-value case. -/
theorem hermitization_apply_singularHermitizationEigenvector {n : Nat}
    (B : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (hermitization B).toEuclideanLin
        (singularHermitizationEigenvector B i) =
      (matrixSingularValue B i.val : ℂ) •
        singularHermitizationEigenvector B i := by
  let T := B.toEuclideanLin
  let s := matrixSingularValue B i.val
  let v := rightSingularVector B i
  have hgram : T.adjoint (T v) = (s : ℂ) ^ 2 • v := by
    simpa [T, s, v] using adjoint_apply_apply_rightSingularVector B i
  by_cases hs : s = 0
  · have hTv : T v = 0 := by
      have hzero : (T.adjoint ∘ₗ T) v = 0 := by
        simp [LinearMap.comp_apply, hgram, hs]
      have hvker : v ∈ LinearMap.ker (T.adjoint ∘ₗ T) := by
        exact LinearMap.mem_ker.mpr hzero
      rw [T.ker_adjoint_comp_self] at hvker
      exact LinearMap.mem_ker.mp hvker
    rw [singularHermitizationEigenvector, if_pos hs,
      hermitization_toEuclideanLin_apply_sumElim]
    simp [T, s, v, hs, hTv]
  · have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
    have htop : T v = (s : ℂ) • ((s : ℂ)⁻¹ • T v) := by
      rw [smul_smul]
      simp [hsC]
    have hbottom : T.adjoint ((s : ℂ)⁻¹ • T v) = (s : ℂ) • v := by
      rw [map_smul, hgram, smul_smul]
      congr 1
      field_simp
    rw [singularHermitizationEigenvector, if_neg hs,
      hermitization_toEuclideanLin_apply_sumElim]
    apply PiLp.ext
    intro k
    cases k with
    | inl j =>
        simpa [T, s, v] using congrArg
          (fun x : EuclideanSpace ℂ (Fin n) => ofLp x j) htop
    | inr j =>
        simpa [T, s, v] using congrArg
          (fun x : EuclideanSpace ℂ (Fin n) => ofLp x j) hbottom

/-- First form of the count bridge, using the canonical `Fin (2n)`-indexed
eigenvalue list underlying `Matrix.IsHermitian.eigenvalues₀`. -/
theorem smallSingularValue_card_le_hermitizationEigenvalues₀_card
    {n : Nat} (B : Matrix (Fin n) (Fin n) ℂ) (a : Real)
    (ha : 0 ≤ a) :
    (smallSingularValueIndices
        (fun i : Fin n => matrixSingularValue B i.val) a).card ≤
      (Finset.univ.filter fun j : Fin (Fintype.card (HermitizationIndex n)) =>
        -a ≤ (hermitization_isHermitian B).eigenvalues₀ j ∧
        (hermitization_isHermitian B).eigenvalues₀ j ≤ a).card := by
  let S := smallSingularValueIndices
    (fun i : Fin n => matrixSingularValue B i.val) a
  let kappa := {i : Fin n // i ∈ S}
  let H := (hermitization B).toEuclideanLin
  have hH : H.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (hermitization_isHermitian B)
  have hli : LinearIndependent ℂ
      (fun i : kappa => singularHermitizationEigenvector B i.1) :=
    (linearIndependent_singularHermitizationEigenvector B).comp
      (fun i : kappa => i.1) Subtype.val_injective
  have heigen : ∀ i : kappa,
      H (singularHermitizationEigenvector B i.1) =
        (matrixSingularValue B i.1.val : ℂ) •
          singularHermitizationEigenvector B i.1 := by
    intro i
    exact hermitization_apply_singularHermitizationEigenvector B i.1
  have hband : ∀ i : kappa,
      -a ≤ matrixSingularValue B i.1.val ∧
        matrixSingularValue B i.1.val ≤ a := by
    intro i
    have hi : matrixSingularValue B i.1.val ≤ a := by
      simpa [S, smallSingularValueIndices] using i.2
    exact ⟨(neg_nonpos.mpr ha).trans (matrixSingularValue_nonneg B i.1.val), hi⟩
  have hcount := card_le_symmetricEigenvalueBand_of_linearIndependent
    hH (finrank_euclideanSpace) a
    (fun i : kappa => singularHermitizationEigenvector B i.1)
    (fun i : kappa => matrixSingularValue B i.1.val)
    hli heigen hband
  have hScard : Fintype.card kappa = S.card := by
    apply Fintype.card_of_subtype
    intro i
    simp
  rw [hScard] at hcount
  have heigenvalues :
      hH.eigenvalues finrank_euclideanSpace =
        (hermitization_isHermitian B).eigenvalues₀ := by
    rfl
  rw [heigenvalues] at hcount
  simpa [S] using hcount

/-- Reindexing from `eigenvalues₀ : Fin (card I) → ℝ` to
`eigenvalues : I → ℝ` preserves every predicate count. -/
theorem card_filter_eigenvalues₀_eq_eigenvalues
    {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : A.IsHermitian) (p : Real → Prop)
    [DecidablePred p] :
    (Finset.univ.filter fun j : Fin (Fintype.card I) => p (hA.eigenvalues₀ j)).card =
      (Finset.univ.filter fun i : I => p (hA.eigenvalues i)).card := by
  let e : Fin (Fintype.card I) ≃ I :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card I))
  have he : ∀ j, p (hA.eigenvalues₀ j) ↔ p (hA.eigenvalues (e j)) := by
    intro j
    simp [Matrix.IsHermitian.eigenvalues, e]
  calc
    (Finset.univ.filter fun j : Fin (Fintype.card I) =>
        p (hA.eigenvalues₀ j)).card =
        Fintype.card {j : Fin (Fintype.card I) // p (hA.eigenvalues₀ j)} := by
      symm
      apply Fintype.card_of_subtype
      intro j
      simp
    _ = Fintype.card {i : I // p (hA.eigenvalues i)} := by
      exact Fintype.card_congr (e.subtypeEquiv he)
    _ = (Finset.univ.filter fun i : I => p (hA.eigenvalues i)).card := by
      apply Fintype.card_of_subtype
      intro i
      simp

/-- Complete deterministic Hermitization count bridge.  Every singular
value in `[0,a]` contributes a linearly independent Hermitization eigenvector
with eigenvalue in `[-a,a]`; hence its multiplicity count is no larger than
the Hermitian spectral count. -/
theorem smallSingularValue_card_le_smallHermitizationEigenvalue_card
    {n : Nat} (B : Matrix (Fin n) (Fin n) ℂ) (a : Real)
    (ha : 0 ≤ a) :
    (smallSingularValueIndices
        (fun i : Fin n => matrixSingularValue B i.val) a).card ≤
      (smallHermitizationEigenvalueIndices B a).card := by
  have h := smallSingularValue_card_le_hermitizationEigenvalues₀_card B a ha
  rw [card_filter_eigenvalues₀_eq_eigenvalues
    (hermitization_isHermitian B)
    (fun x : Real => -a ≤ x ∧ x ≤ a)] at h
  exact h

/-! ## Source-facing Proposition 3.4 adapter -/

open Filter Set
open scoped ENNReal Topology

open MeasureTheory

/-- Source-shaped all-cutoff count statement for the actual Hermitization.

The interval is `[-r,r]`, so the right-hand side is written with its actual
length `2r`, exactly as in Corollary 3.5.  This declaration merely packages
caller-supplied hypotheses; it does not assert a random-matrix theorem. -/
structure HermitizationAllCutoffsCountingInput
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat → Nat}
    (mu : Measure Omega)
    (A : ∀ n, Omega → Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (threshold C : Nat → Real) (good : Nat → Set Omega) : Prop where
  threshold_nonneg : ∀ n, 0 ≤ threshold n
  badProbability : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0)
  count : ∀ n omega, omega ∈ good n → ∀ r,
    threshold n ≤ r →
      ((smallHermitizationEigenvalueIndices
        (A n omega - z •
          (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)) r).card : Real) ≤
        C n * (M n : Real) * (2 * r)

/-- The complete adapter from a Corollary-3.5-style Hermitization count to
the all-cutoff singular-value interface consumed by Proposition 3.6.

The only constant change is the explicit interval-length factor:
`C M (2r) = (2C) M r`. -/
theorem proposition34AllCutoffsInput_of_hermitization
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat → Nat}
    {mu : Measure Omega}
    (A : ∀ n, Omega → Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (z : ℂ) (threshold C : Nat → Real) (good : Nat → Set Omega)
    (hHerm : HermitizationAllCutoffsCountingInput
      mu A z threshold C good) :
    Proposition34AllCutoffsInput mu
      (shiftedSingularValueProcess A z) threshold (fun n => 2 * C n) good := by
  refine
    { badProbability := hHerm.badProbability
      count := ?_ }
  intro n omega homega r hr
  have hr0 : 0 ≤ r := (hHerm.threshold_nonneg n).trans hr
  let B := A n omega - z •
    (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)
  have hNat :=
    smallSingularValue_card_le_smallHermitizationEigenvalue_card B r hr0
  have hReal :
      ((smallSingularValueIndices
        (fun i : Fin (M n) => matrixSingularValue B i.val) r).card : Real) ≤
      (smallHermitizationEigenvalueIndices B r).card := by
    exact_mod_cast hNat
  change
    ((smallSingularValueIndices
      (fun i : Fin (M n) => matrixSingularValue B i.val) r).card : Real) ≤
      (2 * C n) * (Fintype.card (Fin (M n)) : Real) * r
  calc
    ((smallSingularValueIndices
      (fun i : Fin (M n) => matrixSingularValue B i.val) r).card : Real)
        ≤ (smallHermitizationEigenvalueIndices B r).card := hReal
    _ ≤ C n * (M n : Real) * (2 * r) := by
      simpa [B] using hHerm.count n omega homega r hr
    _ = (2 * C n) * (Fintype.card (Fin (M n)) : Real) * r := by
      simp
      ring

end ShortRingAnchor
