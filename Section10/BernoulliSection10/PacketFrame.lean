import BernoulliSection10.PacketBoundary
import BernoulliLinearAlgebra.ConcreteBoundaryExterior
import BernoulliLinearAlgebra.GlobalBoundarySquarefree
import BernoulliLinearAlgebra.DenseExtension
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-!
# Fixed exterior-degree packet coefficients from concrete unitary frames

This file is the deterministic frame-limit core used in Proposition 10.10.
The frame data are not an asymptotic certificate: `U` and `V` are literal
unitary completions and `s` is the set of their `r` distinguished columns.
Consequently the `s`-columns of `compound r U` and `compound r V` are the
coordinates of the paper's decomposable unit wedges.
-/

open Filter Topology
open scoped BigOperators Matrix Topology

noncomputable section

set_option maxHeartbeats 800000

namespace BernoulliSection10

open Matrix Set Set.powersetCard MvPolynomial
open BernoulliLinearAlgebra

variable {W : Type*} [Fintype W] [LinearOrder W]

local instance packetFrameSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W => (toLex x : W ⊕ₗ W)) toLex.injective

local instance packetFrameVariableDecidableEq :
    DecidableEq (ThreeBlockVariable W) := Classical.decEq _

/-- The coefficient ring of all concrete seven-block packet polynomials. -/
abbrev PacketPolynomial (W : Type*) :=
  MvPolynomial (ThreeBlockVariable W) ℂ

/-- A companion step over the literal packet-polynomial ring. -/
structure FormalCompanionStep (W : Type*) [Fintype W] [DecidableEq W] where
  B : Matrix W W (PacketPolynomial W)
  D : Matrix W W (PacketPolynomial W)
  C : Matrix W W (PacketPolynomial W)

/-- Jacobi's reindexing sign, now cast into the packet-polynomial ring. -/
def formalJacobiReindexSign {k m : ℕ}
    (hm : m + k = Fintype.card (W ⊕ W))
    (s t : powersetCard (W ⊕ W) k) : PacketPolynomial W :=
  C (jacobiReindexSign hm s t)

/-- Complementary-minor formula for the inverse compound, over the actual
packet-polynomial ring.  It is denominator-free at singular interfaces. -/
def formalClearedInverseCompound (k : ℕ)
    (E : Matrix (W ⊕ W) (W ⊕ W) (PacketPolynomial W)) :
    Matrix (powersetCard (W ⊕ W) k) (powersetCard (W ⊕ W) k)
      (PacketPolynomial W) :=
  if hk : k ≤ Fintype.card (W ⊕ W) then
    let hm : Fintype.card (W ⊕ W) - k + k = Fintype.card (W ⊕ W) :=
      Nat.sub_add_cancel hk
    (show Matrix (powersetCard (W ⊕ W) k) (powersetCard (W ⊕ W) k)
        (PacketPolynomial W) from
      fun s t => formalJacobiReindexSign hm s t *
        minor (Fintype.card (W ⊕ W) - k) E
          (powersetCard.compl hm t) (powersetCard.compl hm s))
  else 0

@[simp] theorem formalClearedInverseCompound_apply_of_le
    (k : ℕ)
    (E : Matrix (W ⊕ W) (W ⊕ W) (PacketPolynomial W))
    (hk : k ≤ Fintype.card (W ⊕ W))
    (s t : powersetCard (W ⊕ W) k) :
    formalClearedInverseCompound k E s t =
      formalJacobiReindexSign (Nat.sub_add_cancel hk) s t *
        minor (Fintype.card (W ⊕ W) - k) E
          (powersetCard.compl (Nat.sub_add_cancel hk) t)
          (powersetCard.compl (Nat.sub_add_cancel hk) s) := by
  rw [formalClearedInverseCompound, dif_pos hk]

/-- The literal denominator-free exterior operator of one formal packet
step. -/
def formalClearedStepCompound (k : ℕ)
    (B D C : Matrix W W (PacketPolynomial W)) :
    Matrix (powersetCard (W ⊕ W) k) (powersetCard (W ⊕ W) k)
      (PacketPolynomial W) :=
  (-1 : PacketPolynomial W) ^ k •
    (formalClearedInverseCompound k (stepL B) *
      compound k (stepK D C))

/-- Chronological product of the three formal cleared packet steps. -/
def formalClearedCompoundProduct (k : ℕ) :
    List (FormalCompanionStep W) →
      Matrix (powersetCard (W ⊕ W) k) (powersetCard (W ⊕ W) k)
        (PacketPolynomial W)
  | [] => compound k 1
  | x :: xs => formalClearedCompoundProduct k xs *
      formalClearedStepCompound k x.B x.D x.C

/-- Constant-polynomial lift of a complex matrix. -/
def packetCMatrix {m n : Type*} (A : Matrix m n ℂ) :
    Matrix m n (PacketPolynomial W) := A.map C

/-- The paper's three physical companion steps, with all seven fresh blocks
literal formal matrices and with the spectral shift on the diagonal blocks. -/
def packetFormalCompanionSteps
    (z : ℂ) (CL BR : Matrix W W ℂ) : List (FormalCompanionStep W) :=
  [
    ⟨threeBlockBLPolynomial,
      threeBlockALPolynomial -
        (C z : PacketPolynomial W) • (1 : Matrix W W (PacketPolynomial W)),
      packetCMatrix (W := W) CL⟩,
    ⟨threeBlockBCPolynomial,
      threeBlockACPolynomial -
        (C z : PacketPolynomial W) • (1 : Matrix W W (PacketPolynomial W)),
      threeBlockCCPolynomial⟩,
    ⟨packetCMatrix (W := W) BR,
      threeBlockARPolynomial -
        (C z : PacketPolynomial W) • (1 : Matrix W W (PacketPolynomial W)),
      threeBlockCRPolynomial⟩
  ]

/-- The concrete denominator-free `r`th exterior packet operator
`Q^(r)(x)` as a matrix whose entries are literal packet polynomials. -/
def packetExteriorOperatorPolynomial
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ) :
    Matrix (powersetCard (W ⊕ W) r) (powersetCard (W ⊕ W) r)
      (PacketPolynomial W) :=
  formalClearedCompoundProduct r (packetFormalCompanionSteps z CL BR)

/-- Compound matrices commute with conjugate transpose. -/
theorem compound_conjTranspose (r : ℕ)
    (A : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    compound r Aᴴ = (compound r A)ᴴ := by
  ext a b
  simp [compound_apply, minor_conjTranspose]

/-- The scalar matrix-coefficient polynomial
`Z = ⟨Û_s, Q^(r) V̂_s⟩`.  A value `U : unitaryGroup` is a concrete
unitary completion; the column indexed by `s` of `compound r U` is exactly
the decomposable unit wedge formed from those `r` orthonormal columns. -/
def packetScalarMatrixCoefficientPolynomial
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) : PacketPolynomial W :=
  (show Matrix (powersetCard (W ⊕ W) r) (powersetCard (W ⊕ W) r)
      (PacketPolynomial W) from
    (packetCMatrix (W := W)
        ((compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ) :
          Matrix (powersetCard (W ⊕ W) r) (powersetCard (W ⊕ W) r)
            (PacketPolynomial W)) *
      packetExteriorOperatorPolynomial r z CL BR *
      (packetCMatrix (W := W)
        (compound r (V : Matrix (W ⊕ W) (W ⊕ W) ℂ)) :
          Matrix (powersetCard (W ⊕ W) r) (powersetCard (W ⊕ W) r)
            (PacketPolynomial W))) s s

/-- Its complete squarefree coefficient vector. -/
def packetScalarMatrixCoefficientCoeffVector
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) :
    CoeffSpace (ThreeBlockVariable W) :=
  WithLp.toLp 2 (fun S =>
    coeff (squarefreeExponent S)
      (packetScalarMatrixCoefficientPolynomial r z CL BR U V s))

/-- The paper's `Γ = ‖Coeff Z‖₂` for the literal scalar
matrix-coefficient polynomial. -/
def packetScalarMatrixCoefficientNorm
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) : ℝ :=
  ‖packetScalarMatrixCoefficientCoeffVector r z CL BR U V s‖

/-! ## The concrete artificial boundary relation -/

/-- The paper's parameter `λ`, sampled along the cofinal sequence `2^q`. -/
def packetFrameLambda (q : ℕ) : ℝ := (2 : ℝ) ^ q

/-- Diagonal value `λ` on the selected `r` frame columns and `λ⁻¹` on
their orthogonal complement. -/
def packetFrameScale {r : ℕ} (s : powersetCard (W ⊕ W) r)
    (q : ℕ) (i : W ⊕ W) : ℂ :=
  if i ∈ s.1 then (2 : ℂ) ^ q else ((2 : ℂ)⁻¹) ^ q

/-- `Θ_λ^(r;U,V) = Ṽ diag(λ I_r,λ⁻¹ I) Ũ*`, using the
literal unitary completions supplied by the caller. -/
def packetFrameTheta {r : ℕ}
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) (q : ℕ) :
    Matrix (W ⊕ W) (W ⊕ W) ℂ :=
  (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) *
    Matrix.diagonal (packetFrameScale s q) *
      (U : Matrix (W ⊕ W) (W ⊕ W) ℂ)ᴴ

@[simp] theorem packetFrameScale_ne_zero {r : ℕ}
    (s : powersetCard (W ⊕ W) r) (q : ℕ) (i : W ⊕ W) :
    packetFrameScale s q i ≠ 0 := by
  by_cases hi : i ∈ s.1 <;> simp [packetFrameScale, hi]

/-- Every artificial frame relation is genuinely invertible. -/
theorem packetFrameTheta_det_isUnit {r : ℕ}
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) (q : ℕ) :
    IsUnit (packetFrameTheta U V s q).det := by
  have hV : IsUnit
      (V : Matrix (W ⊕ W) (W ⊕ W) ℂ).det :=
    Matrix.UnitaryGroup.det_isUnit V
  have hU : IsUnit
      (U : Matrix (W ⊕ W) (W ⊕ W) ℂ).det :=
    Matrix.UnitaryGroup.det_isUnit U
  have hD : IsUnit
      (Matrix.diagonal (packetFrameScale s q) :
        Matrix (W ⊕ W) (W ⊕ W) ℂ).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun i _ => packetFrameScale_ne_zero s q i)
  unfold packetFrameTheta
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  simpa [mul_assoc] using hV.mul (hD.mul hU.star)

/-- Complex normalization `λ⁻r` along the chosen cofinal sequence. -/
def packetFrameComplexNormalization (r q : ℕ) : ℂ :=
  (((2 : ℂ)⁻¹) ^ r) ^ q

/-- Real normalization `λ⁻r` used for coefficient and Gram norms. -/
def packetFrameRealNormalization (r q : ℕ) : ℝ :=
  (((2 : ℝ)⁻¹) ^ r) ^ q

@[simp] theorem packetFrameRealNormalization_pos (r q : ℕ) :
    0 < packetFrameRealNormalization r q := by
  exact pow_pos (pow_pos (by norm_num : 0 < (2 : ℝ)⁻¹) r) q

@[simp] theorem norm_packetFrameComplexNormalization (r q : ℕ) :
    ‖packetFrameComplexNormalization r q‖ =
      packetFrameRealNormalization r q := by
  simp [packetFrameComplexNormalization, packetFrameRealNormalization,
    norm_pow]

/-! ## Evaluation of the literal exterior packet operator -/

/-- Evaluate a formal companion step entrywise. -/
def evalFormalCompanionStep (x : ThreeBlockVariable W → ℂ)
    (S : FormalCompanionStep W) : CompanionStep W where
  B := S.B.map (eval x)
  D := S.D.map (eval x)
  C := S.C.map (eval x)

@[simp] theorem eval_packetCMatrix
    {m n : Type*} (x : ThreeBlockVariable W → ℂ)
    (A : Matrix m n ℂ) :
    (packetCMatrix (W := W) A : Matrix m n (PacketPolynomial W)).map (eval x) = A := by
  ext i j
  simp [packetCMatrix]

@[simp] theorem eval_threeBlockALPolynomial_packetFrame
    (x : ThreeBlockVariable W → ℂ) :
    threeBlockALPolynomial.map (eval x) = threeBlockAL x := by
  ext i j
  simp [threeBlockALPolynomial, threeBlockAL]

@[simp] theorem eval_threeBlockBLPolynomial_packetFrame
    (x : ThreeBlockVariable W → ℂ) :
    threeBlockBLPolynomial.map (eval x) = threeBlockBL x := by
  ext i j
  simp [threeBlockBLPolynomial, threeBlockBL]

@[simp] theorem eval_threeBlockCCPolynomial_packetFrame
    (x : ThreeBlockVariable W → ℂ) :
    threeBlockCCPolynomial.map (eval x) = threeBlockCC x := by
  ext i j
  simp [threeBlockCCPolynomial, threeBlockCC]

@[simp] theorem eval_threeBlockACPolynomial_packetFrame
    (x : ThreeBlockVariable W → ℂ) :
    threeBlockACPolynomial.map (eval x) = threeBlockAC x := by
  ext i j
  simp [threeBlockACPolynomial, threeBlockAC]

@[simp] theorem eval_threeBlockBCPolynomial_packetFrame
    (x : ThreeBlockVariable W → ℂ) :
    threeBlockBCPolynomial.map (eval x) = threeBlockBC x := by
  ext i j
  simp [threeBlockBCPolynomial, threeBlockBC]

@[simp] theorem eval_threeBlockCRPolynomial_packetFrame
    (x : ThreeBlockVariable W → ℂ) :
    threeBlockCRPolynomial.map (eval x) = threeBlockCR x := by
  ext i j
  simp [threeBlockCRPolynomial, threeBlockCR]

@[simp] theorem eval_threeBlockARPolynomial_packetFrame
    (x : ThreeBlockVariable W → ℂ) :
    threeBlockARPolynomial.map (eval x) = threeBlockAR x := by
  ext i j
  simp [threeBlockARPolynomial, threeBlockAR]

@[simp] theorem eval_C_smul_one_packetFrame
    (z : ℂ) (x : ThreeBlockVariable W → ℂ) :
    ((C z : PacketPolynomial W) •
      (1 : Matrix W W (PacketPolynomial W))).map (eval x) =
      z • (1 : Matrix W W ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.smul_apply]
  · simp [Matrix.smul_apply, hij]

@[simp] theorem eval_packetFormalCompanionSteps
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (x : ThreeBlockVariable W → ℂ) :
    (packetFormalCompanionSteps z CL BR).map
        (evalFormalCompanionStep x) =
      boundaryCompanionSteps
        (threeBlockBL x) (threeBlockBC x) BR
        (threeBlockAL x - z • 1) (threeBlockAC x - z • 1)
        (threeBlockAR x - z • 1) CL (threeBlockCC x) (threeBlockCR x) := by
  simp [packetFormalCompanionSteps, boundaryCompanionSteps,
    evalFormalCompanionStep, Matrix.map_sub]

@[simp] theorem eval_minor_packetPolynomial
    {k : ℕ}
    (x : ThreeBlockVariable W → ℂ)
    (A : Matrix (W ⊕ W) (W ⊕ W) (PacketPolynomial W))
    (a b : powersetCard (W ⊕ W) k) :
    eval x (minor k A a b) = minor k (A.map (eval x)) a b := by
  unfold minor
  rw [(eval x).map_det]
  rfl

@[simp] theorem eval_formalJacobiReindexSign
    {k m : ℕ} (hm : m + k = Fintype.card (W ⊕ W))
    (x : ThreeBlockVariable W → ℂ)
    (a b : powersetCard (W ⊕ W) k) :
    eval x (formalJacobiReindexSign hm a b) =
      jacobiReindexSign hm a b := by
  simp [formalJacobiReindexSign]

@[simp] theorem eval_formalClearedInverseCompound
    (k : ℕ) (x : ThreeBlockVariable W → ℂ)
    (E : Matrix (W ⊕ W) (W ⊕ W) (PacketPolynomial W)) :
    (formalClearedInverseCompound k E).map (eval x) =
      clearedInverseCompound k (E.map (eval x)) := by
  by_cases hk : k ≤ Fintype.card (W ⊕ W)
  · ext a b
    rw [Matrix.map_apply,
      formalClearedInverseCompound_apply_of_le k E hk,
      clearedInverseCompound_apply_of_le k (E.map (eval x)) hk]
    simp
  · have hformal : formalClearedInverseCompound k E = 0 := by
      rw [formalClearedInverseCompound, dif_neg hk]
    have hnumeric : clearedInverseCompound k (E.map (eval x)) = 0 := by
      rw [clearedInverseCompound, dif_neg hk]
    rw [hformal, hnumeric]
    ext a b
    simp

@[simp] theorem eval_compound_packetPolynomial
    (k : ℕ) (x : ThreeBlockVariable W → ℂ)
    (A : Matrix (W ⊕ W) (W ⊕ W) (PacketPolynomial W)) :
    (compound k A).map (eval x) = compound k (A.map (eval x)) := by
  ext a b
  simp [compound_apply, eval_minor_packetPolynomial]

@[simp] theorem eval_formalClearedStepCompound
    (k : ℕ) (x : ThreeBlockVariable W → ℂ)
    (B D C₀ : Matrix W W (PacketPolynomial W)) :
    (formalClearedStepCompound k B D C₀).map (eval x) =
      clearedStepCompound k (B.map (eval x)) (D.map (eval x))
        (C₀.map (eval x)) := by
  have hL : (stepL B).map (eval x) = stepL (B.map (eval x)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [stepL, fromBlocks]
    · simp [stepL, fromBlocks]
    · simp [stepL, fromBlocks]
    · by_cases hij : i = j <;> simp [stepL, fromBlocks, hij]
  have hK : (stepK D C₀).map (eval x) =
      stepK (D.map (eval x)) (C₀.map (eval x)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [stepK, fromBlocks]
    · simp [stepK, fromBlocks]
    · by_cases hij : i = j <;> simp [stepK, fromBlocks, hij]
    · simp [stepK, fromBlocks]
  unfold formalClearedStepCompound clearedStepCompound
  rw [Matrix.map_smul' (eval x) ((-1 : PacketPolynomial W) ^ k) _
    (fun a b => map_mul (eval x) a b)]
  simp only [map_pow, map_neg, map_one]
  rw [Matrix.map_mul, eval_formalClearedInverseCompound,
    eval_compound_packetPolynomial, hL, hK]

@[simp] theorem eval_formalClearedCompoundProduct
    (k : ℕ) (x : ThreeBlockVariable W → ℂ)
    (xs : List (FormalCompanionStep W)) :
    (formalClearedCompoundProduct k xs).map (eval x) =
      polynomialClearedCompoundProduct k
        (xs.map (evalFormalCompanionStep x)) := by
  induction xs with
  | nil =>
      rw [formalClearedCompoundProduct,
        List.map_nil, polynomialClearedCompoundProduct]
      rw [eval_compound_packetPolynomial]
      have hone :
          (1 : Matrix (W ⊕ W) (W ⊕ W) (PacketPolynomial W)).map (eval x) =
            (1 : Matrix (W ⊕ W) (W ⊕ W) ℂ) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij]
      rw [hone]
  | cons a xs ih =>
      simp [formalClearedCompoundProduct, polynomialClearedCompoundProduct,
        ih, evalFormalCompanionStep, Matrix.map_mul]

/-- Evaluation identifies the formal packet operator with the stable base's
literal denominator-free numerical operator. -/
theorem eval_packetExteriorOperatorPolynomial
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (x : ThreeBlockVariable W → ℂ) :
    (packetExteriorOperatorPolynomial r z CL BR).map (eval x) =
      polynomialClearedCompoundProduct r
        (boundaryCompanionSteps
          (threeBlockBL x) (threeBlockBC x) BR
          (threeBlockAL x - z • 1) (threeBlockAC x - z • 1)
          (threeBlockAR x - z • 1) CL (threeBlockCC x) (threeBlockCR x)) := by
  rw [packetExteriorOperatorPolynomial,
    eval_formalClearedCompoundProduct,
    eval_packetFormalCompanionSteps]

/-- Pointwise, `Z` is exactly the scalar matrix coefficient of the concrete
denominator-free `r`th exterior packet operator. -/
theorem eval_packetScalarMatrixCoefficientPolynomial
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r)
    (x : ThreeBlockVariable W → ℂ) :
    eval x (packetScalarMatrixCoefficientPolynomial r z CL BR U V s) =
      ((compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ *
        polynomialClearedCompoundProduct r
          (boundaryCompanionSteps
            (threeBlockBL x) (threeBlockBC x) BR
            (threeBlockAL x - z • 1) (threeBlockAC x - z • 1)
            (threeBlockAR x - z • 1) CL (threeBlockCC x) (threeBlockCR x)) *
        compound r (V : Matrix (W ⊕ W) (W ⊕ W) ℂ)) s s := by
  unfold packetScalarMatrixCoefficientPolynomial
  change
    ((show Matrix (powersetCard (W ⊕ W) r) (powersetCard (W ⊕ W) r)
        (PacketPolynomial W) from
      (packetCMatrix (W := W)
          ((compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ)) *
        packetExteriorOperatorPolynomial r z CL BR *
        packetCMatrix (W := W)
          (compound r (V : Matrix (W ⊕ W) (W ⊕ W) ℂ))).map (eval x)) s s = _
  rw [Matrix.map_mul, Matrix.map_mul, eval_packetCMatrix,
    eval_packetExteriorOperatorPolynomial, eval_packetCMatrix]

/-! ## Literal exterior expansion of the packet determinant -/

/-- The denominator-free exterior trace, now retained as a polynomial in
the seven fresh packet blocks. -/
def packetFormalBoundaryTrace
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) : PacketPolynomial W :=
  ∑ a : Finset (W ⊕ W), (-1 : PacketPolynomial W) ^ a.card *
    (show Matrix (powersetCard (W ⊕ W) a.card)
        (powersetCard (W ⊕ W) a.card) (PacketPolynomial W) from
      packetExteriorOperatorPolynomial a.card z CL BR *
        (packetCMatrix (W := W) (compound a.card Theta) :
          Matrix (powersetCard (W ⊕ W) a.card)
            (powersetCard (W ⊕ W) a.card) (PacketPolynomial W)))
      (ofCard rfl) (ofCard rfl)

@[simp] theorem eval_packetExteriorOperatorPolynomial_mul_packetCMatrix_apply
    (k : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (x : ThreeBlockVariable W → ℂ)
    (a b : powersetCard (W ⊕ W) k) :
    eval x
      ((show Matrix (powersetCard (W ⊕ W) k)
          (powersetCard (W ⊕ W) k) (PacketPolynomial W) from
        packetExteriorOperatorPolynomial k z CL BR *
          (packetCMatrix (W := W) (compound k Theta) :
            Matrix (powersetCard (W ⊕ W) k)
              (powersetCard (W ⊕ W) k) (PacketPolynomial W))) a b) =
      (polynomialClearedCompoundProduct k
          (boundaryCompanionSteps
            (threeBlockBL x) (threeBlockBC x) BR
            (threeBlockAL x - z • 1) (threeBlockAC x - z • 1)
            (threeBlockAR x - z • 1) CL (threeBlockCC x) (threeBlockCR x)) *
        compound k Theta) a b := by
  change
    ((show Matrix (powersetCard (W ⊕ W) k)
        (powersetCard (W ⊕ W) k) (PacketPolynomial W) from
      packetExteriorOperatorPolynomial k z CL BR *
        packetCMatrix (W := W) (compound k Theta)).map (eval x)) a b = _
  rw [Matrix.map_mul, eval_packetExteriorOperatorPolynomial,
    eval_packetCMatrix]

/-- Evaluation commutes with the formal exterior trace. -/
theorem eval_packetFormalBoundaryTrace
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (x : ThreeBlockVariable W → ℂ) :
    eval x (packetFormalBoundaryTrace z CL BR Theta) =
      polynomialClearedBoundaryTrace
        (boundaryCompanionSteps
          (threeBlockBL x) (threeBlockBC x) BR
          (threeBlockAL x - z • 1) (threeBlockAC x - z • 1)
          (threeBlockAR x - z • 1) CL (threeBlockCC x) (threeBlockCR x))
        Theta := by
  unfold packetFormalBoundaryTrace polynomialClearedBoundaryTrace
  simp_rw [map_sum, map_mul, map_pow, map_neg, map_one]
  apply Finset.sum_congr rfl
  intro a _
  rw [eval_packetExteriorOperatorPolynomial_mul_packetCMatrix_apply]

/-- The global literal determinant polynomial is exactly the finite exterior
sum, not merely pointwise equivalent on an invertible chart. -/
theorem packetBoundaryPolynomial_eq_packetFormalBoundaryTrace
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    packetBoundaryPolynomial z CL BR Theta =
      packetFormalBoundaryTrace z CL BR Theta := by
  apply MvPolynomial.funext
  intro x
  change eval x (globalBoundaryDetPolynomial z CL BR Theta) = _
  rw [eval_packetFormalBoundaryTrace]
  exact eval_globalBoundaryDetPolynomial_eq_polynomialClearedBoundaryTrace
    z CL BR Theta x

/-! ## Exterior powers of the frame diagonal -/

/-- Product of the selected diagonal scales along an exterior basis set. -/
def packetFrameExteriorWeight {r k : ℕ}
    (s : powersetCard (W ⊕ W) r)
    (q : ℕ) (a : powersetCard (W ⊕ W) k) : ℂ :=
  ∏ i ∈ a.1, packetFrameScale s q i

theorem prod_ofFinEmbEquiv_symm
    {k : ℕ} (a : powersetCard (W ⊕ W) k)
    (f : (W ⊕ W) → ℂ) :
    (∏ j : Fin k, f (ofFinEmbEquiv.symm a j)) = ∏ i ∈ a.1, f i := by
  classical
  refine Finset.prod_bij
    (s := Finset.univ) (t := a.1)
    (fun j _ => ofFinEmbEquiv.symm a j) ?_ ?_ ?_ ?_
  · intro j _
    exact (mem_range_ofFinEmbEquiv_symm_iff_mem a _).mp ⟨j, rfl⟩
  · intro i _ j _ hij
    exact (ofFinEmbEquiv.symm a).injective hij
  · intro i hi
    obtain ⟨j, hj⟩ :=
      (mem_range_ofFinEmbEquiv_symm_iff_mem a i).mpr hi
    exact ⟨j, by simp, hj⟩
  · simp

/-- A compound of a diagonal matrix is diagonal, with the expected product
of diagonal entries. -/
theorem compound_diagonal_apply
    {k : ℕ} (d : (W ⊕ W) → ℂ)
    (a b : powersetCard (W ⊕ W) k) :
    compound k (Matrix.diagonal d) a b =
      if a = b then ∏ j : Fin k, d (ofFinEmbEquiv.symm a j) else 0 := by
  rw [compound_apply]
  by_cases hab : a = b
  · subst b
    simp only [if_pos rfl]
    unfold minor
    rw [Matrix.submatrix_diagonal _ _ (ofFinEmbEquiv.symm a).injective]
    rw [Matrix.det_diagonal]
    simpa only [if_true, Function.comp_apply] using
      prod_ofFinEmbEquiv_symm a d
  · rw [if_neg hab]
    unfold minor
    have hnot : ¬ a.1 ⊆ b.1 := by
      intro hsub
      apply hab
      apply Subtype.ext
      exact Finset.eq_of_subset_of_card_le hsub (by simp [a.2, b.2])
    obtain ⟨i, hia, hib⟩ := Finset.not_subset.mp hnot
    obtain ⟨j, hj⟩ :=
      (mem_range_ofFinEmbEquiv_symm_iff_mem a i).mpr hia
    apply Matrix.det_eq_zero_of_row_eq_zero j
    intro l
    simp only [Matrix.submatrix_apply, Matrix.diagonal_apply]
    rw [if_neg]
    intro heq
    apply hib
    rw [← hj, heq]
    exact (mem_range_ofFinEmbEquiv_symm_iff_mem b _).mp
      ⟨l, rfl⟩

/-- The compound columns of a unitary completion form an orthonormal basis.
In particular, its `s`-column is precisely a decomposable unit wedge. -/
theorem compound_mem_unitaryGroup (r : ℕ)
    (U : Matrix.unitaryGroup (W ⊕ W) ℂ) :
    compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ) ∈
      Matrix.unitaryGroup (powersetCard (W ⊕ W) r) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ *
    compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ) = 1
  rw [← compound_conjTranspose, ← compound_mul]
  have hU :
      (U : Matrix (W ⊕ W) (W ⊕ W) ℂ)ᴴ *
        (U : Matrix (W ⊕ W) (W ⊕ W) ℂ) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  rw [hU]
  ext a b
  have hone : (1 : Matrix (W ⊕ W) (W ⊕ W) ℂ) =
      Matrix.diagonal (fun _ => (1 : ℂ)) := by ext i j; simp
  rw [hone, compound_diagonal_apply]
  by_cases hab : a = b
  · subst b
    have hdiag :
        (1 : Matrix (powersetCard (W ⊕ W) r)
          (powersetCard (W ⊕ W) r) ℂ) a a = 1 := by simp
    rw [if_pos rfl, hdiag]
    simp
  · have hdiag :
        (1 : Matrix (powersetCard (W ⊕ W) r)
          (powersetCard (W ⊕ W) r) ℂ) a b = 0 := by simp [hab]
    rw [if_neg hab, hdiag]

theorem compound_packetFrameDiagonal_apply
    {r k : ℕ} (s : powersetCard (W ⊕ W) r)
    (q : ℕ) (a b : powersetCard (W ⊕ W) k) :
    compound k (Matrix.diagonal (packetFrameScale s q)) a b =
      if a = b then packetFrameExteriorWeight s q a else 0 := by
  rw [compound_diagonal_apply]
  by_cases hab : a = b
  · simp only [if_pos hab]
    unfold packetFrameExteriorWeight
    exact prod_ofFinEmbEquiv_symm a (packetFrameScale s q)
  · simp [hab]

/-- Compound matrices commute with conjugate transpose.  This local bridge
keeps the artificial-frame expansion in the same adjoint normal form as the
paper. -/
theorem compound_conjTranspose_packetFrame
    {k : ℕ} (A : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    compound k Aᴴ = (compound k A)ᴴ := by
  ext a b
  simp [compound_apply, minor_conjTranspose]

/-- Functorial exterior expansion of the concrete artificial relation. -/
theorem compound_packetFrameTheta
    {r k : ℕ}
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) (q : ℕ) :
    compound k (packetFrameTheta U V s q) =
      compound k (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) *
        compound k (Matrix.diagonal (packetFrameScale s q)) *
          (compound k (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ := by
  rw [packetFrameTheta, compound_mul, compound_mul,
    compound_conjTranspose_packetFrame]

theorem packetFrameExteriorWeight_eq
    {r k : ℕ} (s : powersetCard (W ⊕ W) r)
    (q : ℕ) (a : powersetCard (W ⊕ W) k) :
    packetFrameExteriorWeight s q a =
      ((2 : ℂ) ^ q) ^ (a.1 ∩ s.1).card *
        (((2 : ℂ)⁻¹) ^ q) ^ (a.1 \ s.1).card := by
  classical
  unfold packetFrameExteriorWeight packetFrameScale
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  congr 2
  · congr 2
    ext i
    simp [and_left_comm]

/-- The exponent inequality behind the frame extraction.  Equality can
occur only for the selected exterior basis set itself. -/
theorem two_mul_inter_card_lt_add_card_of_ne
    {r k : ℕ} (s : powersetCard (W ⊕ W) r)
    (a : powersetCard (W ⊕ W) k) (hneq : a.1 ≠ s.1) :
    2 * (a.1 ∩ s.1).card < k + r := by
  have hca : (a.1 ∩ s.1).card ≤ k := by
    simpa [a.2] using
      Finset.card_le_card (Finset.inter_subset_left : a.1 ∩ s.1 ⊆ a.1)
  have hcs : (a.1 ∩ s.1).card ≤ r := by
    simpa [s.2] using
      Finset.card_le_card (Finset.inter_subset_right : a.1 ∩ s.1 ⊆ s.1)
  by_contra hnot
  have heqk : (a.1 ∩ s.1).card = k := by omega
  have heqr : (a.1 ∩ s.1).card = r := by omega
  have hinter : a.1 ∩ s.1 = a.1 :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by simpa [a.2, heqk])
  have has : a.1 ⊆ s.1 := by
    intro i hi
    exact (Finset.mem_inter.mp (hinter.symm ▸ hi)).2
  apply hneq
  exact Finset.eq_of_subset_of_card_le has (by
    simpa [a.2, s.2] using (show r ≤ k by omega))

theorem pow_pow_comm {R : Type*} [Monoid R] (a : R) (m n : ℕ) :
    (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem packetFrame_normalizedWeight_eq_pow
    {r k : ℕ} (s : powersetCard (W ⊕ W) r)
    (a : powersetCard (W ⊕ W) k) (q : ℕ) :
    packetFrameComplexNormalization r q * packetFrameExteriorWeight s q a =
      (((2 : ℂ)⁻¹) ^ r *
        (2 : ℂ) ^ (a.1 ∩ s.1).card *
        ((2 : ℂ)⁻¹) ^ (a.1 \ s.1).card) ^ q := by
  rw [packetFrameExteriorWeight_eq]
  unfold packetFrameComplexNormalization
  rw [pow_pow_comm (2 : ℂ) q (a.1 ∩ s.1).card,
    pow_pow_comm ((2 : ℂ)⁻¹) q (a.1 \ s.1).card]
  rw [mul_pow, mul_pow]
  ring

theorem norm_packetFrameWeightBase_lt_one
    {r k : ℕ} (s : powersetCard (W ⊕ W) r)
    (a : powersetCard (W ⊕ W) k) (hneq : a.1 ≠ s.1) :
    ‖((2 : ℂ)⁻¹) ^ r *
        (2 : ℂ) ^ (a.1 ∩ s.1).card *
        ((2 : ℂ)⁻¹) ^ (a.1 \ s.1).card‖ < 1 := by
  let c := (a.1 ∩ s.1).card
  let d := (a.1 \ s.1).card
  have hcard : k = c + d := by
    dsimp [c, d]
    simpa [a.2] using (Finset.card_inter_add_card_sdiff a.1 s.1).symm
  have hexp : c < r + d := by
    have h := two_mul_inter_card_lt_add_card_of_ne s a hneq
    dsimp [c, d] at *
    omega
  have hp : (2 : ℝ) ^ c < (2 : ℝ) ^ (r + d) :=
    pow_lt_pow_right₀ (by norm_num) hexp
  have hden : 0 < (2 : ℝ) ^ (r + d) := by positivity
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
  norm_num
  dsimp [c, d] at hp hden ⊢
  have heq :
      ((2 : ℝ)⁻¹) ^ r * 2 ^ (a.1 ∩ s.1).card *
          ((2 : ℝ)⁻¹) ^ (a.1 \ s.1).card =
        2 ^ (a.1 ∩ s.1).card /
          2 ^ (r + (a.1 \ s.1).card) := by
    calc
      _ = 2 ^ (a.1 ∩ s.1).card *
          (((2 : ℝ)⁻¹) ^ r * ((2 : ℝ)⁻¹) ^ (a.1 \ s.1).card) := by ring
      _ = 2 ^ (a.1 ∩ s.1).card *
          ((2 : ℝ)⁻¹) ^ (r + (a.1 \ s.1).card) := by rw [pow_add]
      _ = 2 ^ (a.1 ∩ s.1).card /
          2 ^ (r + (a.1 \ s.1).card) := by
        rw [div_eq_mul_inv, inv_pow]
  have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [hhalf]
  rw [heq]
  exact (div_lt_one hden).2 hp

theorem tendsto_packetFrame_normalizedWeight
    {r k : ℕ} (s : powersetCard (W ⊕ W) r)
    (a : powersetCard (W ⊕ W) k) :
    Tendsto
      (fun q => packetFrameComplexNormalization r q *
        packetFrameExteriorWeight s q a)
      atTop (nhds (if a.1 = s.1 then 1 else 0)) := by
  by_cases h : a.1 = s.1
  · have hak : a.1.card = s.1.card := congrArg Finset.card h
    have hkr : k = r := by simpa [a.2, s.2] using hak
    subst k
    have ha : a = s := Subtype.ext h
    subst a
    have hbase :
        ((2 : ℂ)⁻¹) ^ r *
            (2 : ℂ) ^ (s.1 ∩ s.1).card *
            ((2 : ℂ)⁻¹) ^ (s.1 \ s.1).card = 1 := by
      simp [s.2, ← mul_pow]
    simp only [if_pos rfl]
    have hfun :
        (fun q => packetFrameComplexNormalization r q *
          packetFrameExteriorWeight s q s) = (fun _ : ℕ => (1 : ℂ)) := by
      funext q
      rw [packetFrame_normalizedWeight_eq_pow, hbase, one_pow]
    rw [hfun]
    exact tendsto_const_nhds
  · simp only [if_neg h]
    rw [show (fun q => packetFrameComplexNormalization r q *
          packetFrameExteriorWeight s q a) =
        fun q => (((2 : ℂ)⁻¹) ^ r *
          (2 : ℂ) ^ (a.1 ∩ s.1).card *
          ((2 : ℂ)⁻¹) ^ (a.1 \ s.1).card) ^ q by
      funext q
      exact packetFrame_normalizedWeight_eq_pow s a q]
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (norm_packetFrameWeightBase_lt_one s a h)

/-- The same exterior trace with the exterior degree displayed explicitly.
This form is convenient for taking the fixed-`r` limit. -/
def packetFormalBoundaryTraceByDegree
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) : PacketPolynomial W :=
  ∑ k ∈ Finset.range (Fintype.card (W ⊕ W) + 1),
    (-1 : PacketPolynomial W) ^ k *
      ∑ t : powersetCard (W ⊕ W) k,
        (show Matrix (powersetCard (W ⊕ W) k)
            (powersetCard (W ⊕ W) k) (PacketPolynomial W) from
          packetExteriorOperatorPolynomial k z CL BR *
            (packetCMatrix (W := W) (compound k Theta) :
              Matrix (powersetCard (W ⊕ W) k)
                (powersetCard (W ⊕ W) k) (PacketPolynomial W))) t t

theorem packetFormalBoundaryTrace_eq_byDegree
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    packetFormalBoundaryTrace z CL BR Theta =
      packetFormalBoundaryTraceByDegree z CL BR Theta := by
  classical
  unfold packetFormalBoundaryTrace packetFormalBoundaryTraceByDegree
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ)
    (t := Finset.range (Fintype.card (W ⊕ W) + 1))
    (g := Finset.card)
    (fun t : Finset (W ⊕ W) => by
      intro _
      simp only [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.card_le_univ t))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  refine Finset.sum_bij
    (s := Finset.univ.filter (fun t : Finset (W ⊕ W) => t.card = k))
    (t := Finset.univ)
    (fun t ht =>
      (⟨t, (Finset.mem_filter.mp ht).2⟩ : powersetCard (W ⊕ W) k)) ?_ ?_ ?_ ?_
  · intro _ _
    simp
  · intro t₁ _ t₂ _ h
    exact congrArg Subtype.val h
  · intro t _
    refine ⟨t.1, ?_, ?_⟩
    · simp
    · apply Subtype.ext
      rfl
  · intro t ht
    have hcard : t.card = k := (Finset.mem_filter.mp ht).2
    subst k
    rfl

/-! ## Coefficientwise frame limit -/

/-- Fully expanded coefficient of the exterior trace along the artificial
frame.  This definition is only a proof normal form; the public object
remains `packetBoundaryPolynomial`. -/
def packetFrameExpandedCoefficient
    (m : ThreeBlockVariable W →₀ ℕ)
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) (q : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (Fintype.card (W ⊕ W) + 1),
    ∑ t : powersetCard (W ⊕ W) k,
      ∑ p : powersetCard (W ⊕ W) k,
        ∑ a : powersetCard (W ⊕ W) k,
          (-1 : ℂ) ^ k *
            coeff m (packetExteriorOperatorPolynomial k z CL BR t p) *
            compound k (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) p a *
            packetFrameExteriorWeight s q a *
            (compound k
              (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ a t

/-- Expanding the compound of `Θ_λ` gives exactly the preceding finite
sum. -/
theorem coeff_packetBoundaryPolynomial_packetFrameTheta_eq_expanded
    (m : ThreeBlockVariable W →₀ ℕ)
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) (q : ℕ) :
    coeff m (packetBoundaryPolynomial z CL BR
      (packetFrameTheta U V s q)) =
      packetFrameExpandedCoefficient m r z CL BR U V s q := by
  rw [packetBoundaryPolynomial_eq_packetFormalBoundaryTrace]
  rw [packetFormalBoundaryTrace_eq_byDegree]
  unfold packetFormalBoundaryTraceByDegree packetFrameExpandedCoefficient
  simp_rw [coeff_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [compound_packetFrameTheta (k := k) U V s q]
  have hleft (p a : powersetCard (W ⊕ W) k) :
      (compound k (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) *
          compound k (Matrix.diagonal (packetFrameScale s q))) p a =
        compound k (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) p a *
          packetFrameExteriorWeight s q a := by
    rw [Matrix.mul_apply]
    simp [compound_packetFrameDiagonal_apply]
  have hframe (p t : powersetCard (W ⊕ W) k) :
      (((compound k (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) *
          compound k (Matrix.diagonal (packetFrameScale s q))) *
        (compound k (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ) p t) =
        ∑ a : powersetCard (W ⊕ W) k,
          compound k (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) p a *
            packetFrameExteriorWeight s q a *
            (compound k
              (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ a t := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hleft p a]
  rw [Finset.mul_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Matrix.mul_apply]
  rw [Finset.mul_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro p hp
  change coeff m
      ((-1 : PacketPolynomial W) ^ k *
        (packetExteriorOperatorPolynomial k z CL BR t p *
          C _)) = _
  rw [hframe p t]
  have hsign :
      ((-1 : PacketPolynomial W) ^ k) = C ((-1 : ℂ) ^ k) := by
    simp
  rw [hsign, coeff_C_mul]
  rw [mul_comm (packetExteriorOperatorPolynomial k z CL BR t p), coeff_C_mul]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- The limiting coefficient obtained after the diagonal exterior weights
collapse to the selected decomposable wedge. -/
def packetFrameLimitCoefficient
    (m : ThreeBlockVariable W →₀ ℕ)
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) : ℂ :=
  ∑ k ∈ Finset.range (Fintype.card (W ⊕ W) + 1),
    ∑ t : powersetCard (W ⊕ W) k,
      ∑ p : powersetCard (W ⊕ W) k,
        ∑ a : powersetCard (W ⊕ W) k,
          (-1 : ℂ) ^ k *
            coeff m (packetExteriorOperatorPolynomial k z CL BR t p) *
            compound k (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) p a *
            (if a.1 = s.1 then 1 else 0) *
            (compound k
              (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ a t

theorem tendsto_normalized_packetFrameExpandedCoefficient
    (m : ThreeBlockVariable W →₀ ℕ)
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) :
    Tendsto
      (fun q => packetFrameComplexNormalization r q *
        packetFrameExpandedCoefficient m r z CL BR U V s q)
      atTop (nhds (packetFrameLimitCoefficient m r z CL BR U V s)) := by
  unfold packetFrameExpandedCoefficient packetFrameLimitCoefficient
  simp_rw [Finset.mul_sum]
  apply tendsto_finset_sum
  intro k _
  apply tendsto_finset_sum
  intro t _
  apply tendsto_finset_sum
  intro p _
  apply tendsto_finset_sum
  intro a _
  have hw := tendsto_packetFrame_normalizedWeight s a
  let c : ℂ := (-1 : ℂ) ^ k *
    coeff m (packetExteriorOperatorPolynomial k z CL BR t p) *
    compound k (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) p a *
    (compound k (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ a t
  have hc : Tendsto
      (fun q => c * (packetFrameComplexNormalization r q *
        packetFrameExteriorWeight s q a)) atTop
      (nhds (c * (if a.1 = s.1 then 1 else 0))) :=
    tendsto_const_nhds.mul hw
  convert hc using 1
  · funext q
    dsimp [c]
    ring
  · dsimp [c]
    ring

theorem packetFrameLimitCoefficient_eq_scalarMatrixCoefficient
    (m : ThreeBlockVariable W →₀ ℕ)
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) :
    packetFrameLimitCoefficient m r z CL BR U V s =
      (-1 : ℂ) ^ r *
        coeff m (packetScalarMatrixCoefficientPolynomial r z CL BR U V s) := by
  classical
  unfold packetFrameLimitCoefficient
  have hrle : r ≤ Fintype.card (W ⊕ W) := by
    simpa [s.2] using Finset.card_le_univ s.1
  rw [Finset.sum_eq_single r]
  · have hcollapse
        (t p : powersetCard (W ⊕ W) r) :
        (∑ a : powersetCard (W ⊕ W) r,
          (-1 : ℂ) ^ r *
            coeff m (packetExteriorOperatorPolynomial r z CL BR t p) *
            compound r (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) p a *
            (if a.1 = s.1 then 1 else 0) *
            (compound r
              (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ a t) =
          (-1 : ℂ) ^ r *
            coeff m (packetExteriorOperatorPolynomial r z CL BR t p) *
            compound r (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) p s *
            (compound r
              (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ s t := by
      calc
        _ = (-1 : ℂ) ^ r *
              coeff m (packetExteriorOperatorPolynomial r z CL BR t p) *
              compound r (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) p s *
              (if s.1 = s.1 then 1 else 0) *
              (compound r
                (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ s t := by
            apply Finset.sum_eq_single s
            · intro a _ has
              rw [if_neg]
              · ring
              · exact fun hval => has (Subtype.ext hval)
            · simp
        _ = _ := by simp
    simp_rw [hcollapse]
    unfold packetScalarMatrixCoefficientPolynomial
    have hcoeff (p : PacketPolynomial W) (a : ℂ) :
        coeff m (p * C a) = coeff m p * a := by
      rw [mul_comm, coeff_C_mul]
      exact mul_comm _ _
    have hsum
        (c : ℂ)
        (u : powersetCard (W ⊕ W) r → ℂ)
        (v : powersetCard (W ⊕ W) r →
          powersetCard (W ⊕ W) r → ℂ) :
        (∑ i, ∑ j, v i j * (c * u i)) =
          c * ∑ i, u i * ∑ j, v i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ j, v i j * (c * u i)) =
            ∑ j, c * u i * v i j := by
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = c * u i * ∑ j, v i j := by rw [Finset.mul_sum]
        _ = c * (u i * ∑ j, v i j) := by ring
    simpa [packetCMatrix, Matrix.mul_apply, coeff_sum, coeff_C_mul,
      hcoeff, mul_assoc, mul_left_comm, mul_comm] using
      (hsum ((-1 : ℂ) ^ r)
        (fun t : powersetCard (W ⊕ W) r =>
          (compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ s t)
        (fun t p : powersetCard (W ⊕ W) r =>
          compound r (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) p s *
            coeff m (packetExteriorOperatorPolynomial r z CL BR t p)))
  · intro k hk hkr
    apply Finset.sum_eq_zero
    intro t _
    apply Finset.sum_eq_zero
    intro p _
    apply Finset.sum_eq_zero
    intro a _
    rw [if_neg]
    · ring
    · intro has
      have hcard := congrArg Finset.card has
      apply hkr
      simpa [a.2, s.2] using hcard
  · intro hnot
    have hrmem : r ∈ Finset.range (Fintype.card (W ⊕ W) + 1) := by
      simpa only [Finset.mem_range] using Nat.lt_succ_of_le hrle
    exact (hnot hrmem).elim

/-- Equation (local-polynomial-limit), coefficient by coefficient, for the
literal packet determinant and the literal scalar matrix coefficient `Z`. -/
theorem tendsto_packetBoundaryPolynomial_frame_coefficient
    (m : ThreeBlockVariable W →₀ ℕ)
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) :
    Tendsto
      (fun q => packetFrameComplexNormalization r q *
        coeff m (packetBoundaryPolynomial z CL BR
          (packetFrameTheta U V s q)))
      atTop
      (nhds ((-1 : ℂ) ^ r *
        coeff m (packetScalarMatrixCoefficientPolynomial r z CL BR U V s))) := by
  have h := tendsto_normalized_packetFrameExpandedCoefficient
    m r z CL BR U V s
  rw [packetFrameLimitCoefficient_eq_scalarMatrixCoefficient] at h
  exact h.congr' (Filter.Eventually.of_forall fun q => by
    rw [← coeff_packetBoundaryPolynomial_packetFrameTheta_eq_expanded])

/-- The finite squarefree coefficient vector converges to the coefficient
vector of the concrete scalar matrix coefficient. -/
theorem tendsto_packetBoundaryCoeffVector_frame
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) :
    Tendsto
      (fun q => packetFrameComplexNormalization r q •
        globalBoundaryCoeffVector z CL BR (packetFrameTheta U V s q))
      atTop
      (nhds ((-1 : ℂ) ^ r •
        packetScalarMatrixCoefficientCoeffVector r z CL BR U V s)) := by
  have hraw : Tendsto
      (fun q => WithLp.ofLp
        (packetFrameComplexNormalization r q •
          globalBoundaryCoeffVector z CL BR (packetFrameTheta U V s q)))
      atTop
      (nhds (WithLp.ofLp
        ((-1 : ℂ) ^ r •
          packetScalarMatrixCoefficientCoeffVector r z CL BR U V s))) := by
    apply tendsto_pi_nhds.mpr
    intro S
    change Tendsto
      (fun q => packetFrameComplexNormalization r q *
        coeff (squarefreeExponent S)
          (packetBoundaryPolynomial z CL BR (packetFrameTheta U V s q)))
      atTop
      (nhds ((-1 : ℂ) ^ r *
        coeff (squarefreeExponent S)
          (packetScalarMatrixCoefficientPolynomial r z CL BR U V s)))
    exact tendsto_packetBoundaryPolynomial_frame_coefficient
      (squarefreeExponent S) r z CL BR U V s
  have hcont : Tendsto (WithLp.toLp (2 : ENNReal))
      (nhds (WithLp.ofLp
        ((-1 : ℂ) ^ r •
          packetScalarMatrixCoefficientCoeffVector r z CL BR U V s)))
      (nhds (WithLp.toLp (2 : ENNReal) (WithLp.ofLp
        ((-1 : ℂ) ^ r •
          packetScalarMatrixCoefficientCoeffVector r z CL BR U V s)))) :=
    (PiLp.continuous_toLp (2 : ENNReal)
      (fun _ : Finset (ThreeBlockVariable W) => ℂ)).continuousAt
  have hto := Filter.Tendsto.comp hcont hraw
  simpa [Function.comp_def] using hto

/-- Equation (local-coeff-limit): coefficientwise convergence in the fixed
finite-dimensional squarefree polynomial space implies convergence of the
Euclidean coefficient norm. -/
theorem tendsto_packetBoundaryCoefficientNorm_frame
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) :
    Tendsto
      (fun q => packetFrameRealNormalization r q *
        packetBoundaryCoefficientNorm z CL BR (packetFrameTheta U V s q))
      atTop
      (nhds (packetScalarMatrixCoefficientNorm r z CL BR U V s)) := by
  have h := (tendsto_packetBoundaryCoeffVector_frame r z CL BR U V s).norm
  simpa [globalBoundaryCoefficientNorm,
    packetScalarMatrixCoefficientNorm, norm_smul,
    norm_packetFrameComplexNormalization] using h

/-- The limiting `Z` is squarefree because every approximating literal
packet determinant is squarefree.  Thus the displayed coefficient vector is
the complete coefficient vector, not a selected subfamily. -/
theorem hasSquarefreeSupport_packetScalarMatrixCoefficientPolynomial
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) :
    HasSquarefreeSupport
      (packetScalarMatrixCoefficientPolynomial r z CL BR U V s) := by
  intro m hm
  have hlim := tendsto_packetBoundaryPolynomial_frame_coefficient
    m r z CL BR U V s
  have hzero (q : ℕ) :
      coeff m (packetBoundaryPolynomial z CL BR
        (packetFrameTheta U V s q)) = 0 :=
    hasSquarefreeSupport_globalBoundaryDetPolynomial
      z CL BR (packetFrameTheta U V s q) m hm
  have hzeroLimit : Tendsto
      (fun q => packetFrameComplexNormalization r q *
        coeff m (packetBoundaryPolynomial z CL BR
          (packetFrameTheta U V s q))) atTop (nhds 0) := by
    have heqfun :
        (fun q => packetFrameComplexNormalization r q *
          coeff m (packetBoundaryPolynomial z CL BR
            (packetFrameTheta U V s q))) =
          (fun _ : ℕ => (0 : ℂ)) := by
      funext q
      simp [hzero q]
    rw [heqfun]
    exact tendsto_const_nhds
  have heq : (-1 : ℂ) ^ r *
      coeff m (packetScalarMatrixCoefficientPolynomial r z CL BR U V s) = 0 :=
    tendsto_nhds_unique hlim hzeroLimit
  exact (mul_eq_zero.mp heq).resolve_left (by simp)

/-! ## The graph-volume limit -/

/-- Left and right unitary changes of basis do not change Gram energy. -/
theorem gramEnergy_unitary_diagonal_unitary
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (d : (W ⊕ W) → ℂ) :
    gramEnergy
      ((V : Matrix (W ⊕ W) (W ⊕ W) ℂ) *
        Matrix.diagonal d *
          (U : Matrix (W ⊕ W) (W ⊕ W) ℂ)ᴴ) =
      gramEnergy (Matrix.diagonal d) := by
  unfold gramEnergy
  have hV := Matrix.UnitaryGroup.star_mul_self V
  have hU := Matrix.UnitaryGroup.star_mul_self U
  have hV' :
      (V : Matrix (W ⊕ W) (W ⊕ W) ℂ)ᴴ *
        (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) = 1 := hV
  have hU' :
      (U : Matrix (W ⊕ W) (W ⊕ W) ℂ)ᴴ *
        (U : Matrix (W ⊕ W) (W ⊕ W) ℂ) = 1 := hU
  have hgram :
      ((V : Matrix (W ⊕ W) (W ⊕ W) ℂ) * Matrix.diagonal d *
          (U : Matrix (W ⊕ W) (W ⊕ W) ℂ)ᴴ)ᴴ *
        ((V : Matrix (W ⊕ W) (W ⊕ W) ℂ) * Matrix.diagonal d *
          (U : Matrix (W ⊕ W) (W ⊕ W) ℂ)ᴴ) =
        (U : Matrix (W ⊕ W) (W ⊕ W) ℂ) *
          ((Matrix.diagonal d)ᴴ * Matrix.diagonal d) *
            (U : Matrix (W ⊕ W) (W ⊕ W) ℂ)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ =
        (U : Matrix (W ⊕ W) (W ⊕ W) ℂ) *
          ((Matrix.diagonal d)ᴴ *
            (((V : Matrix (W ⊕ W) (W ⊕ W) ℂ)ᴴ *
                (V : Matrix (W ⊕ W) (W ⊕ W) ℂ)) *
              Matrix.diagonal d)) *
            (U : Matrix (W ⊕ W) (W ⊕ W) ℂ)ᴴ := by
              simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV']; simp only [Matrix.one_mul]
  rw [hgram]
  have hdet := Matrix.det_one_add_mul_comm
    ((U : Matrix (W ⊕ W) (W ⊕ W) ℂ) *
      ((Matrix.diagonal d)ᴴ * Matrix.diagonal d))
    (U : Matrix (W ⊕ W) (W ⊕ W) ℂ)ᴴ
  rw [hdet]
  rw [← Matrix.mul_assoc,
    hU', Matrix.one_mul]

theorem gramEnergy_packetFrameTheta_eq_diagonal
    {r : ℕ} (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) (q : ℕ) :
    gramEnergy (packetFrameTheta U V s q) =
      gramEnergy (Matrix.diagonal (packetFrameScale s q)) := by
  exact gramEnergy_unitary_diagonal_unitary U V _

theorem star_mul_packetFrameScale
    {r : ℕ} (s : powersetCard (W ⊕ W) r)
    (q : ℕ) (i : W ⊕ W) :
    star (packetFrameScale s q i) * packetFrameScale s q i =
      if i ∈ s.1 then (4 : ℂ) ^ q else ((4 : ℂ)⁻¹) ^ q := by
  by_cases hi : i ∈ s.1
  · simp only [packetFrameScale, if_pos hi]
    have hstar : star ((2 : ℂ) ^ q) = (2 : ℂ) ^ q := by simp
    rw [hstar, ← mul_pow]
    congr 1
    norm_num
  · simp only [packetFrameScale, if_neg hi]
    have hstar : star (((2 : ℂ)⁻¹) ^ q) = ((2 : ℂ)⁻¹) ^ q := by simp
    rw [hstar, ← mul_pow]
    congr 1
    norm_num

/-- Exact singular-value computation for the artificial relation, expressed
without invoking a singular-value API. -/
theorem gramEnergy_packetFrameTheta_exact
    {r : ℕ} (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) (q : ℕ) :
    gramEnergy (packetFrameTheta U V s q) =
      (1 + (4 : ℝ) ^ q) ^ r *
        (1 + ((4 : ℝ)⁻¹) ^ q) ^
          (Fintype.card (W ⊕ W) - r) := by
  rw [gramEnergy_packetFrameTheta_eq_diagonal]
  unfold gramEnergy
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have hadd :
      (1 : Matrix (W ⊕ W) (W ⊕ W) ℂ) +
          Matrix.diagonal (fun i =>
            star (packetFrameScale s q) i * packetFrameScale s q i) =
        Matrix.diagonal (fun i =>
          1 + star (packetFrameScale s q) i * packetFrameScale s q i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hadd, Matrix.det_diagonal]
  simp only [Pi.star_apply]
  simp_rw [star_mul_packetFrameScale, apply_ite]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hfilter : Finset.univ.filter (fun i : W ⊕ W => i ∈ s.1) = s.1 := by
    ext i
    simp
  have hfilterc :
      Finset.univ.filter (fun i : W ⊕ W => ¬ i ∈ s.1) =
        Finset.univ \ s.1 := by
    ext i
    simp
  rw [hfilter, hfilterc]
  have hcardc : (Finset.univ \ s.1).card =
      Fintype.card (W ⊕ W) - r := by
    simp [Finset.card_sdiff, s.2]
  rw [s.2, hcardc]
  simp only [Fintype.card_sum]
  have hA : ((1 + (4 : ℂ) ^ q) ^ r) =
      (((1 + (4 : ℝ) ^ q) ^ r : ℝ) : ℂ) := by norm_cast
  have hB₀ : ((1 + ((4 : ℂ)⁻¹) ^ q) ^
      (Fintype.card W + Fintype.card W - r)) =
      (((1 + ((4 : ℝ)⁻¹) ^ q) ^
        (Fintype.card W + Fintype.card W - r) : ℝ) : ℂ) := by
    have hfour : (4 : ℂ)⁻¹ = (((4 : ℝ)⁻¹ : ℝ) : ℂ) := by
      norm_num
    rw [hfour]
    norm_cast
  have hB : ((1 + ((4 : ℂ) ^ q)⁻¹) ^
      (Fintype.card W + Fintype.card W - r)) =
      (((1 + ((4 : ℝ) ^ q)⁻¹) ^
        (Fintype.card W + Fintype.card W - r) : ℝ) : ℂ) := by
    simpa only [inv_pow] using hB₀
  have hprod :
      ((1 + (4 : ℂ) ^ q) ^ r) *
          ((1 + ((4 : ℂ)⁻¹) ^ q) ^
            (Fintype.card W + Fintype.card W - r)) =
        ((((1 + (4 : ℝ) ^ q) ^ r) *
          ((1 + ((4 : ℝ)⁻¹) ^ q) ^
            (Fintype.card W + Fintype.card W - r)) : ℝ) : ℂ) := by
    calc
      _ = (((1 + (4 : ℝ) ^ q) ^ r : ℝ) : ℂ) *
          (((1 + ((4 : ℝ)⁻¹) ^ q) ^
            (Fintype.card W + Fintype.card W - r) : ℝ) : ℂ) := by
        rw [hA, hB₀]
      _ = _ := by norm_cast
  change (((1 + (4 : ℂ) ^ q) ^ r) *
      ((1 + ((4 : ℂ)⁻¹) ^ q) ^
        (Fintype.card W + Fintype.card W - r))).re =
    ((1 + (4 : ℝ) ^ q) ^ r) *
      ((1 + ((4 : ℝ)⁻¹) ^ q) ^
        (Fintype.card W + Fintype.card W - r))
  rw [hprod]
  rfl

/-- Squared normalization times Gram energy has the especially simple
paper value `(1 + λ⁻²)^(2W)`. -/
theorem normalized_gramEnergy_packetFrameTheta_exact
    {r : ℕ} (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) (q : ℕ) :
    packetFrameRealNormalization r q ^ 2 *
        gramEnergy (packetFrameTheta U V s q) =
      (1 + ((4 : ℝ)⁻¹) ^ q) ^ Fintype.card (W ⊕ W) := by
  rw [gramEnergy_packetFrameTheta_exact]
  have hrle : r ≤ Fintype.card (W ⊕ W) := by
    simpa [s.2] using Finset.card_le_univ s.1
  unfold packetFrameRealNormalization
  have hfour : ((((2 : ℝ)⁻¹) ^ r) ^ q) ^ 2 =
      (((4 : ℝ)⁻¹) ^ q) ^ r := by
    calc
      ((((2 : ℝ)⁻¹) ^ r) ^ q) ^ 2 =
          ((2 : ℝ)⁻¹) ^ (r * (q * 2)) := by
            rw [← pow_mul, ← pow_mul]
      _ = (((2 : ℝ)⁻¹) ^ 2) ^ (q * r) := by
            rw [← pow_mul]
            congr 1
            ring
      _ = ((4 : ℝ)⁻¹) ^ (q * r) := by norm_num
      _ = (((4 : ℝ)⁻¹) ^ q) ^ r := by rw [pow_mul]
  rw [hfour]
  have hfactor :
      ((4 : ℝ)⁻¹) ^ q * (1 + (4 : ℝ) ^ q) =
        1 + ((4 : ℝ)⁻¹) ^ q := by
    have hne : (4 : ℝ) ^ q ≠ 0 := by positivity
    rw [inv_pow, mul_add, inv_mul_cancel₀ hne]
    ring
  rw [← mul_assoc, ← mul_pow, hfactor, ← pow_add]
  congr 1
  exact Nat.add_sub_of_le hrle

theorem tendsto_normalized_gramEnergy_packetFrameTheta
    {r : ℕ} (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) :
    Tendsto
      (fun q => packetFrameRealNormalization r q ^ 2 *
        gramEnergy (packetFrameTheta U V s q))
      atTop (nhds 1) := by
  have hquarter : Tendsto (fun q : ℕ => ((4 : ℝ)⁻¹) ^ q)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have h := ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add hquarter).pow
    (Fintype.card (W ⊕ W))
  simpa [normalized_gramEnergy_packetFrameTheta_exact U V s] using h

/-- Equation (local-graph-limit) in the paper's square-root convention. -/
theorem tendsto_packetFrame_normalized_gramVolume
    {r : ℕ} (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) :
    Tendsto
      (fun q => packetFrameRealNormalization r q *
        gramVolume (packetFrameTheta U V s q))
      atTop (nhds 1) := by
  have h := (tendsto_normalized_gramEnergy_packetFrameTheta U V s).sqrt
  have heq (q : ℕ) :
      Real.sqrt (packetFrameRealNormalization r q ^ 2 *
        gramEnergy (packetFrameTheta U V s q)) =
      packetFrameRealNormalization r q *
        gramVolume (packetFrameTheta U V s q) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_pos (packetFrameRealNormalization_pos r q)]
    rfl
  simpa [heq] using h

/-! ## Proposition 10.10: deterministic frame coefficient bounds -/

/-- Multiplicative form of the concrete pathwise packet comparison. -/
theorem packetCoefficient_gramVolume_multiplicative_pathwise
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (hTheta : IsUnit Theta.det) :
    (packetEndpointComparisonConstant z CL BR)⁻¹ * gramVolume Theta ≤
        packetBoundaryCoefficientNorm z CL BR Theta ∧
      packetBoundaryCoefficientNorm z CL BR Theta ≤
        packetEndpointComparisonConstant z CL BR * gramVolume Theta := by
  simpa [packetEndpointComparisonConstant] using
    (globalBoundaryCoefficientNorm_bounds_fullyInstantiated
      z CL BR hCL hBR Theta hTheta)

/-- Caller-facing deterministic core of Proposition 10.10.  The only inputs
are the paper's endpoint invertibility hypotheses and concrete unitary frame
completions.  No nonvanishing, coefficient-limit, graph-limit, or comparison
certificate is accepted from the caller. -/
theorem packetScalarMatrixCoefficientNorm_bounds_and_pos
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) :
    (packetEndpointComparisonConstant z CL BR)⁻¹ ≤
        packetScalarMatrixCoefficientNorm r z CL BR U V s ∧
      packetScalarMatrixCoefficientNorm r z CL BR U V s ≤
        packetEndpointComparisonConstant z CL BR ∧
      0 < packetScalarMatrixCoefficientNorm r z CL BR U V s := by
  let K := packetEndpointComparisonConstant z CL BR
  let middle : ℕ → ℝ := fun q =>
    packetFrameRealNormalization r q *
      packetBoundaryCoefficientNorm z CL BR (packetFrameTheta U V s q)
  let volume : ℕ → ℝ := fun q =>
    packetFrameRealNormalization r q *
      gramVolume (packetFrameTheta U V s q)
  have hbounds (q : ℕ) :
      K⁻¹ * volume q ≤ middle q ∧ middle q ≤ K * volume q := by
    have hb := packetCoefficient_gramVolume_multiplicative_pathwise
      z CL BR hCL hBR (packetFrameTheta U V s q)
      (packetFrameTheta_det_isUnit U V s q)
    have hn : 0 ≤ packetFrameRealNormalization r q :=
      (packetFrameRealNormalization_pos r q).le
    constructor
    · dsimp [K, middle, volume]
      nlinarith [mul_le_mul_of_nonneg_left hb.1 hn]
    · dsimp [K, middle, volume]
      nlinarith [mul_le_mul_of_nonneg_left hb.2 hn]
  have hvolume : Tendsto volume atTop (nhds 1) := by
    simpa [volume] using tendsto_packetFrame_normalized_gramVolume U V s
  have hmiddle : Tendsto middle atTop
      (nhds (packetScalarMatrixCoefficientNorm r z CL BR U V s)) := by
    simpa [middle] using
      tendsto_packetBoundaryCoefficientNorm_frame r z CL BR U V s
  have hclosed := two_sided_bounds_of_sequence_limit
    (tendsto_const_nhds.mul hvolume) hmiddle
    (tendsto_const_nhds.mul hvolume) hbounds
  have hKpos : 0 < K := by
    exact packetEndpointComparisonConstant_pos z CL BR
  have hclosed' :
      K⁻¹ ≤ packetScalarMatrixCoefficientNorm r z CL BR U V s ∧
        packetScalarMatrixCoefficientNorm r z CL BR U V s ≤ K := by
    simpa using hclosed
  have hpos : 0 < packetScalarMatrixCoefficientNorm r z CL BR U V s :=
    (inv_pos.mpr hKpos).trans_le hclosed'.1
  exact ⟨hclosed'.1, hclosed'.2, hpos⟩

theorem packetScalarMatrixCoefficientPolynomial_ne_zero
    (r : ℕ) (z : ℂ) (CL BR : Matrix W W ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (U V : Matrix.unitaryGroup (W ⊕ W) ℂ)
    (s : powersetCard (W ⊕ W) r) :
    packetScalarMatrixCoefficientPolynomial r z CL BR U V s ≠ 0 := by
  intro hzero
  have hpos :=
    (packetScalarMatrixCoefficientNorm_bounds_and_pos
      r z CL BR hCL hBR U V s).2.2
  have hnormzero : packetScalarMatrixCoefficientNorm r z CL BR U V s = 0 := by
    unfold packetScalarMatrixCoefficientNorm
    rw [norm_eq_zero]
    ext S
    simp [packetScalarMatrixCoefficientCoeffVector, hzero]
  exact (ne_of_gt hpos) hnormzero

end BernoulliSection10
