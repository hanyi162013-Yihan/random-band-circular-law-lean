import BernoulliLinearAlgebra.ConcreteClearedTransfer
import BernoulliLinearAlgebra.DoubleEliminationConcrete
import BernoulliLinearAlgebra.ConcreteBoundaryGlobal

/-!
# Direct cleared exterior formula for an arbitrary boundary relation

This file supplies the missing first-elimination bridge in Section 9.4.  The
boundary exterior expression is built from the inverse-free cleared packet
compounds of `ConcreteClearedTransfer.lean`, rather than from totalized
inverses.  It is therefore meaningful when a packet interface block is
singular.
-/

open Filter Topology
open scoped BigOperators Matrix Topology

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard

section BoundaryTrace

variable {W : Type*} [Fintype W] [LinearOrder W]

local instance boundaryTraceSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift' (fun x : W ⊕ W ↦ (toLex x : W ⊕ₗ W))
    (fun _ _ h ↦ toLex.injective h)

/-- The direct denominator-free exterior boundary expression
`sum_k (-1)^k tr(Q^(k) * ∧^k Theta)`. -/
def polynomialClearedBoundaryTrace
    (xs : List (CompanionStep W))
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) : ℂ :=
  ∑ s : Finset (W ⊕ W), (-1 : ℂ) ^ s.card *
    (polynomialClearedCompoundProduct s.card xs * compound s.card Theta)
      (ofCard rfl) (ofCard rfl)

/-- On the invertible-interface locus, the direct boundary expression is
the determinant-cleared compatibility determinant. -/
theorem polynomialClearedBoundaryTrace_eq_detProduct_mul_det_of_units
    (xs : List (CompanionStep W))
    (hxs : ∀ x ∈ xs, IsUnit x.B.det)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    polynomialClearedBoundaryTrace xs Theta =
      (xs.map fun x ↦ x.B.det).prod *
        (1 - chronologicalProduct
          (xs.map fun x ↦ stepTransfer x.B x.D x.C) * Theta).det := by
  have hdegree (s : Finset (W ⊕ W)) :
      polynomialClearedCompoundProduct s.card xs * compound s.card Theta =
        clearedCompoundProduct s.card
          ((1, Theta) :: inverseTransferClearingData xs) := by
    rw [polynomialClearedCompoundProduct_eq_clearedCompoundProduct
      xs hxs s.card (Finset.card_le_univ s)]
    simp [clearedCompoundProduct, clearedCompound]
  unfold polynomialClearedBoundaryTrace
  simp_rw [hdegree]
  change clearedSignedCompoundTrace
      ((1, Theta) :: inverseTransferClearingData xs) = _
  rw [cleared_floquet_exterior_identity]
  simp [clearingFactor, transferList, inverseTransferClearingData,
    List.map_map, Function.comp_def]

/-- Sylvester-swapped form matching the paper's compatibility matrix
`I - Theta * R_partial`. -/
theorem polynomialClearedBoundaryTrace_eq_detProduct_mul_compatibility_of_units
    (xs : List (CompanionStep W))
    (hxs : ∀ x ∈ xs, IsUnit x.B.det)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    polynomialClearedBoundaryTrace xs Theta =
      (xs.map fun x ↦ x.B.det).prod *
        (1 - Theta * chronologicalProduct
          (xs.map fun x ↦ stepTransfer x.B x.D x.C)).det := by
  rw [polynomialClearedBoundaryTrace_eq_detProduct_mul_det_of_units
    xs hxs Theta]
  rw [det_one_sub_transfer_comm]

end BoundaryTrace

section FirstEliminationOrdering

/-- Names of the five scalar block coordinates.  We enumerate them in the
cycle order `(L,C,R,+,-)`, so that the first-elimination column move is
literally `finRotate 5`. -/
abbrev BoundaryFiveBlock := Fin 5

/-- The even five-cycle which changes the column order from
`(L,C,R,-,+)` to `(C,R,+,L,-)`. -/
def boundaryFiveBlockCycle : Equiv.Perm BoundaryFiveBlock :=
  finRotate 5

@[simp]
theorem boundaryFiveBlockCycle_sign :
    Equiv.Perm.sign boundaryFiveBlockCycle = 1 := by
  simp [boundaryFiveBlockCycle]
  norm_num

variable {W : Type*}

/-- Split a scalar auxiliary coordinate into its five-block name and its
within-block coordinate. -/
def boundaryFiveBlockCoordinateEquiv :
    (Packet3 W ⊕ (W ⊕ W)) ≃ (BoundaryFiveBlock × W) where
  toFun
    | Sum.inl (Sum.inl a) => (0, a)
    | Sum.inl (Sum.inr (Sum.inl a)) => (1, a)
    | Sum.inl (Sum.inr (Sum.inr a)) => (2, a)
    | Sum.inr (Sum.inl a) => (4, a)
    | Sum.inr (Sum.inr a) => (3, a)
  invFun
    | (⟨0, _⟩, a) => Sum.inl (Sum.inl a)
    | (⟨1, _⟩, a) => Sum.inl (Sum.inr (Sum.inl a))
    | (⟨2, _⟩, a) => Sum.inl (Sum.inr (Sum.inr a))
    | (⟨3, _⟩, a) => Sum.inr (Sum.inr a)
    | (⟨4, _⟩, a) => Sum.inr (Sum.inl a)
  left_inv := by intro x; rcases x with ((a | (a | a)) | (a | a)) <;> rfl
  right_inv := by rintro ⟨b, a⟩; fin_cases b <;> rfl

/-- Scalar column permutation implementing the even block cycle. -/
def boundaryFirstColumnPerm : Equiv.Perm (Packet3 W ⊕ (W ⊕ W)) :=
  boundaryFiveBlockCoordinateEquiv.trans
    ((boundaryFiveBlockCycle.prodCongr (Equiv.refl W)).trans
      boundaryFiveBlockCoordinateEquiv.symm)

@[simp]
theorem boundaryFirstColumnPerm_sign [Fintype W] [DecidableEq W] :
    Equiv.Perm.sign (boundaryFirstColumnPerm (W := W)) = 1 := by
  have hprod : boundaryFiveBlockCycle.prodCongr (Equiv.refl W) =
      Equiv.prodCongrLeft (fun _ : W => boundaryFiveBlockCycle) := by
    apply Equiv.ext
    rintro ⟨b, w⟩
    change (boundaryFiveBlockCycle b, w) =
      (boundaryFiveBlockCycle b, w)
    rfl
  simp [boundaryFirstColumnPerm, hprod, Equiv.Perm.sign_prodCongrLeft]

@[simp] theorem boundaryFirstColumnPerm_packetLeft (a : W) :
    boundaryFirstColumnPerm (Sum.inl (Sum.inl a)) =
      Sum.inl (Sum.inr (Sum.inl a)) := by
  rfl

@[simp] theorem boundaryFirstColumnPerm_packetCenter (a : W) :
    boundaryFirstColumnPerm (Sum.inl (Sum.inr (Sum.inl a))) =
      Sum.inl (Sum.inr (Sum.inr a)) := by
  rfl

@[simp] theorem boundaryFirstColumnPerm_packetRight (a : W) :
    boundaryFirstColumnPerm (Sum.inl (Sum.inr (Sum.inr a))) =
      Sum.inr (Sum.inr a) := by
  rfl

@[simp] theorem boundaryFirstColumnPerm_endpointMinus (a : W) :
    boundaryFirstColumnPerm (Sum.inr (Sum.inl a)) =
      Sum.inl (Sum.inl a) := by
  rfl

@[simp] theorem boundaryFirstColumnPerm_endpointPlus (a : W) :
    boundaryFirstColumnPerm (Sum.inr (Sum.inr a)) =
      Sum.inr (Sum.inl a) := by
  rfl

end FirstEliminationOrdering

section FirstEliminationMatrices

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The top half of a two-component state matrix. -/
def boundaryStateTop (P : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    Matrix W (W ⊕ W) ℂ := fun i j ↦ P (Sum.inl i) j

/-- The bottom half of a two-component state matrix. -/
def boundaryStateBottom (P : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    Matrix W (W ⊕ W) ℂ := fun i j ↦ P (Sum.inr i) j

omit [DecidableEq W] in
theorem boundaryStateTop_fromBlocks_mul
    (A B C D : Matrix W W ℂ) (P : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    boundaryStateTop (Matrix.fromBlocks A B C D * P) =
      A * boundaryStateTop P + B * boundaryStateBottom P := by
  ext i j
  simp [boundaryStateTop, boundaryStateBottom, Matrix.mul_apply]

omit [DecidableEq W] in
theorem boundaryStateBottom_fromBlocks_mul
    (A B C D : Matrix W W ℂ) (P : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    boundaryStateBottom (Matrix.fromBlocks A B C D * P) =
      C * boundaryStateTop P + D * boundaryStateBottom P := by
  ext i j
  simp [boundaryStateTop, boundaryStateBottom, Matrix.mul_apply]

/-- The bottom component of a companion step is the previous top component. -/
theorem boundaryStateBottom_stepTransfer_mul
    (B D C : Matrix W W ℂ) (hB : IsUnit B.det)
    (P : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    boundaryStateBottom (stepTransfer B D C * P) = boundaryStateTop P := by
  rw [stepTransfer_eq_companion B D C hB,
    boundaryStateBottom_fromBlocks_mul]
  simp

/-- The top row of the one-step companion equation, after applying the step
to an arbitrary matrix of incoming states. -/
theorem boundary_step_recurrence
    (B D C : Matrix W W ℂ) (hB : IsUnit B.det)
    (P : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    B * boundaryStateTop (stepTransfer B D C * P) +
        D * boundaryStateTop P + C * boundaryStateBottom P = 0 := by
  rw [stepTransfer_eq_companion B D C hB,
    boundaryStateTop_fromBlocks_mul]
  have hinv : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  simp only [Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul,
    ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  abel

/-- The lower-triangular `3W` pivot exposed by the first elimination. -/
def boundaryFirstPivot
    (BL BC BR DC CR DR : Matrix W W ℂ) :
    Matrix (Packet3 W) (Packet3 W) ℂ := fun i j ↦
  match i, j with
  | Sum.inl a, Sum.inl b => BL a b
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr (Sum.inl a), Sum.inl b => DC a b
  | Sum.inr (Sum.inl a), Sum.inr (Sum.inl b) => BC a b
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => 0
  | Sum.inr (Sum.inr a), Sum.inl b => CR a b
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inl b) => DR a b
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inr b) => BR a b

omit [Fintype W] [DecidableEq W] in
theorem boundaryFirstPivot_eq_fromBlocks
    (BL BC BR DC CR DR : Matrix W W ℂ) :
    boundaryFirstPivot BL BC BR DC CR DR =
      Matrix.fromBlocks BL 0
        (fun (i : W ⊕ W) (j : W) ↦ match i with
          | Sum.inl a => DC a j
          | Sum.inr a => CR a j)
        (Matrix.fromBlocks BC 0 DR BR) := by
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> rfl

@[simp]
theorem boundaryFirstPivot_det
    (BL BC BR DC CR DR : Matrix W W ℂ) :
    (boundaryFirstPivot BL BC BR DC CR DR).det =
      BL.det * BC.det * BR.det := by
  let E : Matrix (W ⊕ W) W ℂ := fun i j ↦ match i with
    | Sum.inl a => DC a j
    | Sum.inr a => CR a j
  rw [boundaryFirstPivot_eq_fromBlocks,
    show (fun (i : W ⊕ W) (j : W) ↦ match i with
      | Sum.inl a => DC a j
      | Sum.inr a => CR a j) = E from rfl]
  change (Matrix.fromBlocks BL 0 E (Matrix.fromBlocks BC 0 DR BR)).det = _
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₁₂]
  ring

/-- The two surviving columns `(L,-)` in the first elimination. -/
def boundaryFirstInput
    (DL CC CL : Matrix W W ℂ) :
    Matrix (Packet3 W) (W ⊕ W) ℂ := fun i j ↦
  match i, j with
  | Sum.inl a, Sum.inl b => DL a b
  | Sum.inl a, Sum.inr b => CL a b
  | Sum.inr (Sum.inl a), Sum.inl b => CC a b
  | Sum.inr (Sum.inl _), Sum.inr _ => 0
  | Sum.inr (Sum.inr _), _ => 0

/-- Boundary rows against the pivot columns `(C,R,+)`. -/
def boundaryFirstOutput
    (Theta11 Theta12 Theta21 Theta22 : Matrix W W ℂ) :
    Matrix (W ⊕ W) (Packet3 W) ℂ := fun i j ↦
  match i, j with
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inl a, Sum.inr (Sum.inl b) => -Theta12 a b
  | Sum.inl a, Sum.inr (Sum.inr b) => -Theta11 a b
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr a, Sum.inr (Sum.inl b) => -Theta22 a b
  | Sum.inr a, Sum.inr (Sum.inr b) => -Theta21 a b

/-- Open-chain solution from the surviving state `(psi_L,psi_-)` to the
pivot variables `(psi_C,psi_R,psi_+)`. -/
def boundaryOpenChainSolution
    (BL BC BR DL DC DR CL CC CR : Matrix W W ℂ) :
    Matrix (Packet3 W) (W ⊕ W) ℂ :=
  let TL := stepTransfer BL DL CL
  let TC := stepTransfer BC DC CC
  let TR := stepTransfer BR DR CR
  fun i j ↦
    match i with
    | Sum.inl a => boundaryStateTop TL a j
    | Sum.inr (Sum.inl a) => boundaryStateTop (TC * TL) a j
    | Sum.inr (Sum.inr a) => boundaryStateTop (TR * (TC * TL)) a j

/-- The chronological transfer of the three-site packet. -/
def boundaryPacketTransfer
    (BL BC BR DL DC DR CL CC CR : Matrix W W ℂ) :
    Matrix (W ⊕ W) (W ⊕ W) ℂ :=
  stepTransfer BR DR CR *
    (stepTransfer BC DC CC * stepTransfer BL DL CL)

/-- The literal three-step list used by the inverse-free exterior formula. -/
def boundaryCompanionSteps
    (BL BC BR DL DC DR CL CC CR : Matrix W W ℂ) :
    List (CompanionStep W) :=
  [⟨BL, DL, CL⟩, ⟨BC, DC, CC⟩, ⟨BR, DR, CR⟩]

@[simp]
theorem chronologicalProduct_boundaryCompanionSteps
    (BL BC BR DL DC DR CL CC CR : Matrix W W ℂ) :
    chronologicalProduct
        ((boundaryCompanionSteps BL BC BR DL DC DR CL CC CR).map
          fun x ↦ stepTransfer x.B x.D x.C) =
      boundaryPacketTransfer BL BC BR DL DC DR CL CC CR := by
  simp [boundaryCompanionSteps, boundaryPacketTransfer, Matrix.mul_assoc]

/-- The lower-triangular pivot sends the open-chain solution to the negative
of the two surviving physical columns. -/
theorem boundaryFirstPivot_mul_openChainSolution
    (BL BC BR DL DC DR CL CC CR : Matrix W W ℂ)
    (hBL : IsUnit BL.det) (hBC : IsUnit BC.det) (hBR : IsUnit BR.det) :
    boundaryFirstPivot BL BC BR DC CR DR *
        boundaryOpenChainSolution BL BC BR DL DC DR CL CC CR =
      -boundaryFirstInput DL CC CL := by
  let TL := stepTransfer BL DL CL
  let TC := stepTransfer BC DC CC
  let TR := stepTransfer BR DR CR
  have hL : BL * boundaryStateTop TL +
      DL * boundaryStateTop (1 : Matrix (W ⊕ W) (W ⊕ W) ℂ) +
      CL * boundaryStateBottom (1 : Matrix (W ⊕ W) (W ⊕ W) ℂ) = 0 := by
    simpa [TL] using boundary_step_recurrence BL DL CL hBL
      (1 : Matrix (W ⊕ W) (W ⊕ W) ℂ)
  have hC : BC * boundaryStateTop (TC * TL) +
      DC * boundaryStateTop TL + CC * boundaryStateBottom TL = 0 := by
    simpa [TC] using boundary_step_recurrence BC DC CC hBC TL
  have hR : BR * boundaryStateTop (TR * (TC * TL)) +
      DR * boundaryStateTop (TC * TL) +
      CR * boundaryStateBottom (TC * TL) = 0 := by
    simpa [TR] using boundary_step_recurrence BR DR CR hBR (TC * TL)
  have hTLbottom : boundaryStateBottom TL =
      boundaryStateTop (1 : Matrix (W ⊕ W) (W ⊕ W) ℂ) := by
    simpa [TL] using boundaryStateBottom_stepTransfer_mul BL DL CL hBL
      (1 : Matrix (W ⊕ W) (W ⊕ W) ℂ)
  have hTCbottom : boundaryStateBottom (TC * TL) =
      boundaryStateTop TL := by
    simpa [TC] using boundaryStateBottom_stepTransfer_mul BC DC CC hBC TL
  ext i j
  rcases i with i | (i | i)
  · have hij := congrArg (fun M : Matrix W (W ⊕ W) ℂ ↦ M i j) hL
    have hmul :
        (boundaryFirstPivot BL BC BR DC CR DR *
          boundaryOpenChainSolution BL BC BR DL DC DR CL CC CR)
            (Sum.inl i) j = (BL * boundaryStateTop TL) i j := by
      rw [Matrix.mul_apply]
      simp [boundaryFirstPivot, boundaryOpenChainSolution,
        boundaryStateTop, TL, Matrix.mul_apply]
    rw [hmul]
    rcases j with j | j <;>
      simp [boundaryFirstInput, boundaryStateTop, boundaryStateBottom,
        Matrix.mul_apply, Matrix.one_apply] at hij ⊢ <;>
      linear_combination hij
  · have hij := congrArg (fun M : Matrix W (W ⊕ W) ℂ ↦ M i j) hC
    rw [hTLbottom] at hij
    have hmul :
        (boundaryFirstPivot BL BC BR DC CR DR *
          boundaryOpenChainSolution BL BC BR DL DC DR CL CC CR)
            (Sum.inr (Sum.inl i)) j =
          (DC * boundaryStateTop TL + BC * boundaryStateTop (TC * TL)) i j := by
      rw [Matrix.mul_apply]
      simp [boundaryFirstPivot, boundaryOpenChainSolution,
        boundaryStateTop, TL, TC, Matrix.mul_apply]
    rw [hmul]
    rcases j with j | j <;>
      simp [boundaryFirstInput, boundaryStateTop,
        Matrix.mul_apply, Matrix.one_apply] at hij ⊢ <;>
      linear_combination hij
  · have hij := congrArg (fun M : Matrix W (W ⊕ W) ℂ ↦ M i j) hR
    rw [hTCbottom] at hij
    have hmul :
        (boundaryFirstPivot BL BC BR DC CR DR *
          boundaryOpenChainSolution BL BC BR DL DC DR CL CC CR)
            (Sum.inr (Sum.inr i)) j =
          (CR * boundaryStateTop TL + DR * boundaryStateTop (TC * TL) +
            BR * boundaryStateTop (TR * (TC * TL))) i j := by
      rw [Matrix.mul_apply]
      simp [boundaryFirstPivot, boundaryOpenChainSolution,
        boundaryStateTop, TL, TC, TR, Matrix.mul_apply]
      ring
    rw [hmul]
    rcases j with j | j <;>
      simp [boundaryFirstInput, boundaryStateTop,
        Matrix.mul_apply] at hij ⊢ <;>
      linear_combination hij

/-- Multiplying the boundary output rows by the open-chain solution gives
minus the boundary relation times the packet transfer. -/
theorem boundaryFirstOutput_mul_openChainSolution
    (BL BC BR DL DC DR CL CC CR : Matrix W W ℂ)
    (Theta11 Theta12 Theta21 Theta22 : Matrix W W ℂ)
    (hBR : IsUnit BR.det) :
    boundaryFirstOutput Theta11 Theta12 Theta21 Theta22 *
        boundaryOpenChainSolution BL BC BR DL DC DR CL CC CR =
      -(Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22 *
        boundaryPacketTransfer BL BC BR DL DC DR CL CC CR) := by
  let TL := stepTransfer BL DL CL
  let TC := stepTransfer BC DC CC
  let TR := stepTransfer BR DR CR
  have hbottom : boundaryStateBottom (TR * (TC * TL)) =
      boundaryStateTop (TC * TL) := by
    simpa [TR] using boundaryStateBottom_stepTransfer_mul BR DR CR hBR (TC * TL)
  have hThetaTop :
      boundaryStateTop
          (Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22 *
            (TR * (TC * TL))) =
        Theta11 * boundaryStateTop (TR * (TC * TL)) +
          Theta12 * boundaryStateTop (TC * TL) := by
    rw [boundaryStateTop_fromBlocks_mul, hbottom]
  have hThetaBottom :
      boundaryStateBottom
          (Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22 *
            (TR * (TC * TL))) =
        Theta21 * boundaryStateTop (TR * (TC * TL)) +
          Theta22 * boundaryStateTop (TC * TL) := by
    rw [boundaryStateBottom_fromBlocks_mul, hbottom]
  ext i j
  rcases i with i | i
  · have hmul :
        (boundaryFirstOutput Theta11 Theta12 Theta21 Theta22 *
          boundaryOpenChainSolution BL BC BR DL DC DR CL CC CR)
            (Sum.inl i) j =
          (-(Theta12 * boundaryStateTop (TC * TL)) -
            Theta11 * boundaryStateTop (TR * (TC * TL))) i j := by
      rw [Matrix.mul_apply]
      simp [boundaryFirstOutput, boundaryOpenChainSolution,
        boundaryStateTop, TL, TC, TR, Matrix.mul_apply]
      ring
    rw [hmul]
    have hij := congrArg (fun M : Matrix W (W ⊕ W) ℂ ↦ M i j) hThetaTop
    change _ = -(boundaryStateTop
      (Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22 *
        (TR * (TC * TL))) i j)
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply] at hij ⊢
    linear_combination hij
  · have hmul :
        (boundaryFirstOutput Theta11 Theta12 Theta21 Theta22 *
          boundaryOpenChainSolution BL BC BR DL DC DR CL CC CR)
            (Sum.inr i) j =
          (-(Theta22 * boundaryStateTop (TC * TL)) -
            Theta21 * boundaryStateTop (TR * (TC * TL))) i j := by
      rw [Matrix.mul_apply]
      simp [boundaryFirstOutput, boundaryOpenChainSolution,
        boundaryStateTop, TL, TC, TR, Matrix.mul_apply]
      ring
    rw [hmul]
    have hij := congrArg (fun M : Matrix W (W ⊕ W) ℂ ↦ M i j) hThetaBottom
    change _ = -(boundaryStateBottom
      (Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22 *
        (TR * (TC * TL))) i j)
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply] at hij ⊢
    linear_combination hij

/-- After the even first-elimination column move, the literal auxiliary
matrix has pivot/input/output/identity block form. -/
theorem concreteKTheta_submatrix_boundaryFirstColumnPerm
    (DL BL CC DC BC CR DR CL BR : Matrix W W ℂ)
    (Theta11 Theta12 Theta21 Theta22 : Matrix W W ℂ) :
    (concreteKTheta DL BL CC DC BC CR DR CL BR
      Theta11 Theta12 Theta21 Theta22).submatrix id
        (boundaryFirstColumnPerm (W := W)) =
      Matrix.fromBlocks
        (boundaryFirstPivot BL BC BR DC CR DR)
        (boundaryFirstInput DL CC CL)
        (boundaryFirstOutput Theta11 Theta12 Theta21 Theta22)
        1 := by
  ext i j
  rcases i with ((i | (i | i)) | (i | i)) <;>
    rcases j with ((j | (j | j)) | (j | j)) <;>
    simp [concreteKTheta, packetCore, packetEndpointCoupling,
      boundaryPhysicalCoupling, boundaryOuterCoupling,
      packetOuterInjection, packetOuterProjection, endpointFactor,
      endpointPivot, boundaryFirstPivot, boundaryFirstInput,
      boundaryFirstOutput, Matrix.mul_apply, Matrix.one_apply]

/-- First elimination of the literal five-block matrix on the invertible
interface locus.  No elimination certificate is an input. -/
theorem concreteKTheta_det_eq_boundaryCompatibility_of_units
    (DL BL CC DC BC CR DR CL BR : Matrix W W ℂ)
    (Theta11 Theta12 Theta21 Theta22 : Matrix W W ℂ)
    (hBL : IsUnit BL.det) (hBC : IsUnit BC.det) (hBR : IsUnit BR.det) :
    (concreteKTheta DL BL CC DC BC CR DR CL BR
      Theta11 Theta12 Theta21 Theta22).det =
      (BL.det * BC.det * BR.det) *
        (1 - Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22 *
          boundaryPacketTransfer BL BC BR DL DC DR CL CC CR).det := by
  let A := boundaryFirstPivot BL BC BR DC CR DR
  let B := boundaryFirstInput DL CC CL
  let C := boundaryFirstOutput Theta11 Theta12 Theta21 Theta22
  let U := boundaryOpenChainSolution BL BC BR DL DC DR CL CC CR
  let Theta := Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22
  let R := boundaryPacketTransfer BL BC BR DL DC DR CL CC CR
  have hAdet : A.det = BL.det * BC.det * BR.det := by
    simp [A]
  have hAunit : IsUnit A.det := by
    rw [hAdet]
    exact (hBL.mul hBC).mul hBR
  let _ : Invertible A := A.invertibleOfIsUnitDet hAunit
  have hAU : A * U = -B := by
    simpa [A, B, U] using boundaryFirstPivot_mul_openChainSolution
      BL BC BR DL DC DR CL CC CR hBL hBC hBR
  have hCU : C * U = -(Theta * R) := by
    simpa [C, U, Theta, R] using boundaryFirstOutput_mul_openChainSolution
      BL BC BR DL DC DR CL CC CR Theta11 Theta12 Theta21 Theta22 hBR
  have hsolve : ⅟ A * B = -U := by
    calc
      ⅟ A * B = -(⅟ A * (-B)) := by simp
      _ = -(⅟ A * (A * U)) := by rw [hAU]
      _ = -((⅟ A * A) * U) := by rw [Matrix.mul_assoc]
      _ = -U := by rw [invOf_mul_self, Matrix.one_mul]
  have hschur :
      (1 : Matrix (W ⊕ W) (W ⊕ W) ℂ) - C * ⅟ A * B =
        1 - Theta * R := by
    rw [Matrix.mul_assoc C (⅟ A) B, hsolve, Matrix.mul_neg, hCU]
    simp
  have hperm :
      ((concreteKTheta DL BL CC DC BC CR DR CL BR
        Theta11 Theta12 Theta21 Theta22).submatrix id
          (boundaryFirstColumnPerm (W := W))).det =
        (concreteKTheta DL BL CC DC BC CR DR CL BR
          Theta11 Theta12 Theta21 Theta22).det := by
    simpa using Matrix.det_permute'
      (boundaryFirstColumnPerm (W := W))
      (concreteKTheta DL BL CC DC BC CR DR CL BR
        Theta11 Theta12 Theta21 Theta22)
  calc
    (concreteKTheta DL BL CC DC BC CR DR CL BR
      Theta11 Theta12 Theta21 Theta22).det =
        ((concreteKTheta DL BL CC DC BC CR DR CL BR
          Theta11 Theta12 Theta21 Theta22).submatrix id
            (boundaryFirstColumnPerm (W := W))).det := hperm.symm
    _ = (Matrix.fromBlocks A B C 1).det := by
      rw [concreteKTheta_submatrix_boundaryFirstColumnPerm]
    _ = A.det * ((1 : Matrix (W ⊕ W) (W ⊕ W) ℂ) - C * ⅟ A * B).det :=
      Matrix.det_fromBlocks₁₁ A B C 1
    _ = (BL.det * BC.det * BR.det) * (1 - Theta * R).det := by
      rw [hAdet, hschur]
    _ = (BL.det * BC.det * BR.det) *
        (1 - Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22 *
          boundaryPacketTransfer BL BC BR DL DC DR CL CC CR).det := rfl

end FirstEliminationMatrices

section BoundaryLiteralDeterminant

variable {W : Type*} [Fintype W] [LinearOrder W]

local instance boundaryLiteralDeterminantSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift' (fun x : W ⊕ W ↦ (toLex x : W ⊕ₗ W))
    (fun _ _ h ↦ toLex.injective h)

/-- On the invertible-interface locus, the direct cleared exterior expression
is exactly the determinant of the literal five-block auxiliary matrix. -/
theorem polynomialClearedBoundaryTrace_boundaryCompanionSteps_eq_concreteKTheta_det_of_units
    (DL BL CC DC BC CR DR CL BR : Matrix W W ℂ)
    (Theta11 Theta12 Theta21 Theta22 : Matrix W W ℂ)
    (hBL : IsUnit BL.det) (hBC : IsUnit BC.det) (hBR : IsUnit BR.det) :
    polynomialClearedBoundaryTrace
        (boundaryCompanionSteps BL BC BR DL DC DR CL CC CR)
        (Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22) =
      (concreteKTheta DL BL CC DC BC CR DR CL BR
        Theta11 Theta12 Theta21 Theta22).det := by
  have hsteps : ∀ x ∈ boundaryCompanionSteps BL BC BR DL DC DR CL CC CR,
      IsUnit x.B.det := by
    intro x hx
    simp only [boundaryCompanionSteps, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hBL
    · exact hBC
    · exact hBR
  have htrace :=
    polynomialClearedBoundaryTrace_eq_detProduct_mul_compatibility_of_units
      (boundaryCompanionSteps BL BC BR DL DC DR CL CC CR) hsteps
      (Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22)
  have hK := concreteKTheta_det_eq_boundaryCompatibility_of_units
    DL BL CC DC BC CR DR CL BR Theta11 Theta12 Theta21 Theta22 hBL hBC hBR
  calc
    polynomialClearedBoundaryTrace
        (boundaryCompanionSteps BL BC BR DL DC DR CL CC CR)
        (Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22) =
      (BL.det * BC.det * BR.det) *
        (1 - Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22 *
          boundaryPacketTransfer BL BC BR DL DC DR CL CC CR).det := by
      simpa [boundaryCompanionSteps, boundaryPacketTransfer,
        Matrix.mul_assoc, mul_assoc] using htrace
    _ = (concreteKTheta DL BL CC DC BC CR DR CL BR
        Theta11 Theta12 Theta21 Theta22).det := hK.symm

/-- The literal five-block auxiliary matrix with a single full boundary
relation argument. -/
def concreteBoundaryK
    (DL BL CC DC BC CR DR CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    Matrix (Packet3 W ⊕ (W ⊕ W)) (Packet3 W ⊕ (W ⊕ W)) ℂ :=
  concreteKTheta DL BL CC DC BC CR DR CL BR
    Theta.toBlocks₁₁ Theta.toBlocks₁₂ Theta.toBlocks₂₁ Theta.toBlocks₂₂

/-- Common scalar perturbation preserves the displayed three-step list. -/
@[simp]
theorem perturbCompanionStepList_boundaryCompanionSteps
    (BL BC BR DL DC DR CL CC CR : Matrix W W ℂ) (z : ℂ) :
    perturbCompanionStepList
        (boundaryCompanionSteps BL BC BR DL DC DR CL CC CR) z =
      boundaryCompanionSteps (scalarPerturb BL z) (scalarPerturb BC z)
        (scalarPerturb BR z) DL DC DR CL CC CR := by
  simp [perturbCompanionStepList, boundaryCompanionSteps]

/-- The direct boundary trace is continuous under a common perturbation of
all interface blocks. -/
theorem continuous_polynomialClearedBoundaryTrace_perturb
    (xs : List (CompanionStep W))
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    Continuous (fun z ↦ polynomialClearedBoundaryTrace
      (perturbCompanionStepList xs z) Theta) := by
  unfold polynomialClearedBoundaryTrace
  apply continuous_finsetSum
  intro s _
  exact continuous_const.mul
    (((continuous_polynomialClearedCompoundProduct_perturb s.card xs).matrix_mul
      continuous_const).matrix_elem (ofCard rfl) (ofCard rfl))

/-- The block diagonal used to choose a single perturbation parameter which
makes all three interface blocks invertible at once. -/
def boundaryInterfaceDiagonal (BL BC BR : Matrix W W ℂ) :
    Matrix (Packet3 W) (Packet3 W) ℂ :=
  Matrix.fromBlocks BL 0 0 (Matrix.fromBlocks BC 0 0 BR)

@[simp]
theorem boundaryInterfaceDiagonal_det (BL BC BR : Matrix W W ℂ) :
    (boundaryInterfaceDiagonal BL BC BR).det =
      BL.det * BC.det * BR.det := by
  simp [boundaryInterfaceDiagonal, Matrix.det_fromBlocks_zero₂₁]
  ring

theorem boundaryInterfaceDiagonal_scalarPerturb
    (BL BC BR : Matrix W W ℂ) (z : ℂ) :
    boundaryInterfaceDiagonal (scalarPerturb BL z)
        (scalarPerturb BC z) (scalarPerturb BR z) =
      scalarPerturb (boundaryInterfaceDiagonal BL BC BR) z := by
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    by_cases h : i = j <;>
    simp [boundaryInterfaceDiagonal, scalarPerturb_eq_add_smul_one, h]

/-- The literal auxiliary determinant varies continuously under the same
common perturbation. -/
theorem continuous_concreteKTheta_interfacePerturb
    (DL BL CC DC BC CR DR CL BR : Matrix W W ℂ)
    (Theta11 Theta12 Theta21 Theta22 : Matrix W W ℂ) :
    Continuous (fun z ↦
      (concreteKTheta DL (scalarPerturb BL z) CC DC
        (scalarPerturb BC z) CR DR CL (scalarPerturb BR z)
        Theta11 Theta12 Theta21 Theta22).det) := by
  have hcore : Continuous (fun z ↦
      packetCore DL (scalarPerturb BL z) CC DC
        (scalarPerturb BC z) CR DR) := by
    apply continuous_matrix
    intro i j
    rcases i with i | (i | i)
    · rcases j with j | (j | j)
      · exact continuous_const
      · exact (continuous_scalarPerturb BL).matrix_elem i j
      · exact continuous_const
    · rcases j with j | (j | j)
      · exact continuous_const
      · exact continuous_const
      · exact (continuous_scalarPerturb BC).matrix_elem i j
    · rcases j with j | (j | j)
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
  have hendpoint : Continuous (fun z ↦
      packetEndpointCoupling CL (scalarPerturb BR z)) := by
    simpa [packetEndpointCoupling, endpointFactor] using
      continuous_const.matrix_mul
        (continuous_const.matrix_fromBlocks continuous_const continuous_const
          (continuous_scalarPerturb BR))
  have hK : Continuous (fun z ↦
      concreteKTheta DL (scalarPerturb BL z) CC DC
        (scalarPerturb BC z) CR DR CL (scalarPerturb BR z)
        Theta11 Theta12 Theta21 Theta22) := by
    simpa [concreteKTheta] using hcore.matrix_fromBlocks hendpoint
      continuous_const continuous_const
  exact hK.matrix_det

/-- Polynomial continuation of the first-elimination identity.  This is the
numerical equality requested in Section 9.4, and it is valid for arbitrary,
possibly singular, `BL`, `BC`, and `BR`. -/
theorem polynomialClearedBoundaryTrace_boundaryCompanionSteps_eq_concreteKTheta_det
    (DL BL CC DC BC CR DR CL BR : Matrix W W ℂ)
    (Theta11 Theta12 Theta21 Theta22 : Matrix W W ℂ) :
    polynomialClearedBoundaryTrace
        (boundaryCompanionSteps BL BC BR DL DC DR CL CC CR)
        (Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22) =
      (concreteKTheta DL BL CC DC BC CR DR CL BR
        Theta11 Theta12 Theta21 Theta22).det := by
  rcases exists_scalarPerturbationSequence
      (boundaryInterfaceDiagonal BL BC BR) with ⟨eps, heps0, hepsdet⟩
  have hunits (q : ℕ) :
      IsUnit (scalarPerturb BL (eps q)).det ∧
      IsUnit (scalarPerturb BC (eps q)).det ∧
      IsUnit (scalarPerturb BR (eps q)).det := by
    have hprod :
        (scalarPerturb BL (eps q)).det *
          (scalarPerturb BC (eps q)).det *
            (scalarPerturb BR (eps q)).det ≠ 0 := by
      rw [← boundaryInterfaceDiagonal_det,
        boundaryInterfaceDiagonal_scalarPerturb]
      exact hepsdet q
    constructor
    · apply isUnit_iff_ne_zero.mpr
      intro hzero
      apply hprod
      simp [hzero]
    constructor
    · apply isUnit_iff_ne_zero.mpr
      intro hzero
      apply hprod
      simp [hzero]
    · apply isUnit_iff_ne_zero.mpr
      intro hzero
      apply hprod
      simp [hzero]
  have heq (q : ℕ) :
      polynomialClearedBoundaryTrace
          (boundaryCompanionSteps (scalarPerturb BL (eps q))
            (scalarPerturb BC (eps q)) (scalarPerturb BR (eps q))
            DL DC DR CL CC CR)
          (Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22) =
        (concreteKTheta DL (scalarPerturb BL (eps q)) CC DC
          (scalarPerturb BC (eps q)) CR DR CL (scalarPerturb BR (eps q))
          Theta11 Theta12 Theta21 Theta22).det :=
    polynomialClearedBoundaryTrace_boundaryCompanionSteps_eq_concreteKTheta_det_of_units
      DL (scalarPerturb BL (eps q)) CC DC (scalarPerturb BC (eps q)) CR DR CL
      (scalarPerturb BR (eps q)) Theta11 Theta12 Theta21 Theta22
      (hunits q).1 (hunits q).2.1 (hunits q).2.2
  have hleft : Tendsto
      (fun q ↦ polynomialClearedBoundaryTrace
        (boundaryCompanionSteps (scalarPerturb BL (eps q))
          (scalarPerturb BC (eps q)) (scalarPerturb BR (eps q))
          DL DC DR CL CC CR)
        (Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22))
      atTop
      (nhds (polynomialClearedBoundaryTrace
        (boundaryCompanionSteps BL BC BR DL DC DR CL CC CR)
        (Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22))) := by
    have h :=
      (continuous_polynomialClearedBoundaryTrace_perturb
        (boundaryCompanionSteps BL BC BR DL DC DR CL CC CR)
        (Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22))
        |>.continuousAt.tendsto.comp heps0
    simpa [Function.comp_def] using h
  have hright : Tendsto
      (fun q ↦
        (concreteKTheta DL (scalarPerturb BL (eps q)) CC DC
          (scalarPerturb BC (eps q)) CR DR CL (scalarPerturb BR (eps q))
          Theta11 Theta12 Theta21 Theta22).det)
      atTop
      (nhds ((concreteKTheta DL BL CC DC BC CR DR CL BR
        Theta11 Theta12 Theta21 Theta22).det)) := by
    have h :=
      (continuous_concreteKTheta_interfacePerturb DL BL CC DC BC CR DR CL BR
        Theta11 Theta12 Theta21 Theta22).continuousAt.tendsto.comp heps0
    simpa [Function.comp_def] using h
  have heventually :
      (fun q ↦ polynomialClearedBoundaryTrace
        (boundaryCompanionSteps (scalarPerturb BL (eps q))
          (scalarPerturb BC (eps q)) (scalarPerturb BR (eps q))
          DL DC DR CL CC CR)
        (Matrix.fromBlocks Theta11 Theta12 Theta21 Theta22)) =ᶠ[atTop]
      (fun q ↦
        (concreteKTheta DL (scalarPerturb BL (eps q)) CC DC
          (scalarPerturb BC (eps q)) CR DR CL (scalarPerturb BR (eps q))
          Theta11 Theta12 Theta21 Theta22).det) :=
    Filter.Eventually.of_forall heq
  exact tendsto_nhds_unique hleft (hright.congr' heventually.symm)

/-- Full-matrix form of the singular-inclusive result.  The right-hand side
is a literal numerical `5W x 5W` determinant. -/
theorem polynomialClearedBoundaryTrace_eq_concreteBoundaryK_det
    (DL BL CC DC BC CR DR CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    polynomialClearedBoundaryTrace
        (boundaryCompanionSteps BL BC BR DL DC DR CL CC CR) Theta =
      (concreteBoundaryK DL BL CC DC BC CR DR CL BR Theta).det := by
  have h :=
    polynomialClearedBoundaryTrace_boundaryCompanionSteps_eq_concreteKTheta_det
      DL BL CC DC BC CR DR CL BR Theta.toBlocks₁₁ Theta.toBlocks₁₂
        Theta.toBlocks₂₁ Theta.toBlocks₂₂
  rw [Matrix.fromBlocks_toBlocks] at h
  exact h

/-- Evaluating the polynomial-valued literal boundary matrix gives the
corresponding numerical five-block matrix, without any invertibility
assumption on the evaluated interface blocks. -/
theorem eval_threeBlockConcreteKPolynomialShifted_eq_concreteKTheta
    (z : ℂ) (CL BR Theta11 Theta12 Theta21 Theta22 : Matrix W W ℂ)
    (x : ThreeBlockVariable W → ℂ) :
    (threeBlockConcreteKPolynomialShifted z CL BR Theta11 Theta12
      Theta21 Theta22).map (MvPolynomial.eval x) =
      concreteKTheta
        (threeBlockAL x - z • 1) (threeBlockBL x) (threeBlockCC x)
        (threeBlockAC x - z • 1) (threeBlockBC x) (threeBlockCR x)
        (threeBlockAR x - z • 1) CL BR
        Theta11 Theta12 Theta21 Theta22 := by
  ext i j
  rcases i with ((i | (i | i)) | (i | i)) <;>
    rcases j with ((j | (j | j)) | (j | j)) <;>
    simp [threeBlockConcreteKPolynomialShifted, concreteKTheta,
      packetCore, packetEndpointCoupling, boundaryPhysicalCoupling,
      boundaryOuterCoupling, packetOuterInjection, packetOuterProjection,
      endpointFactor, endpointPivot, threeBlockCMatrix,
      threeBlockALPolynomial, threeBlockBLPolynomial,
      threeBlockCCPolynomial, threeBlockACPolynomial,
      threeBlockBCPolynomial, threeBlockCRPolynomial,
      threeBlockARPolynomial, threeBlockAL, threeBlockBL,
      threeBlockCC, threeBlockAC, threeBlockBC, threeBlockCR,
      threeBlockAR, Matrix.mul_apply, Matrix.one_apply]
  all_goals split_ifs <;> simp_all

/-- Evaluation bridge to the independently defined inverse-free exterior
expression.  This identifies `globalBoundaryDetPolynomial` pointwise at every
assignment, including assignments with singular interface blocks. -/
theorem eval_globalBoundaryDetPolynomial_eq_polynomialClearedBoundaryTrace
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (x : ThreeBlockVariable W → ℂ) :
    MvPolynomial.eval x (globalBoundaryDetPolynomial z CL BR Theta) =
      polynomialClearedBoundaryTrace
        (boundaryCompanionSteps
          (threeBlockBL x) (threeBlockBC x) BR
          (threeBlockAL x - z • 1) (threeBlockAC x - z • 1)
          (threeBlockAR x - z • 1) CL (threeBlockCC x) (threeBlockCR x))
        Theta := by
  have heval :
      MvPolynomial.eval x (globalBoundaryDetPolynomial z CL BR Theta) =
        (concreteBoundaryK
          (threeBlockAL x - z • 1) (threeBlockBL x) (threeBlockCC x)
          (threeBlockAC x - z • 1) (threeBlockBC x) (threeBlockCR x)
          (threeBlockAR x - z • 1) CL BR Theta).det := by
    rw [globalBoundaryDetPolynomial, globalConcreteKPolynomial,
      (MvPolynomial.eval x).map_det]
    change
      ((threeBlockConcreteKPolynomialShifted z CL BR
        Theta.toBlocks₁₁ Theta.toBlocks₁₂ Theta.toBlocks₂₁
          Theta.toBlocks₂₂).map (MvPolynomial.eval x)).det = _
    rw [eval_threeBlockConcreteKPolynomialShifted_eq_concreteKTheta]
    rfl
  rw [heval]
  exact (polynomialClearedBoundaryTrace_eq_concreteBoundaryK_det
    (threeBlockAL x - z • 1) (threeBlockBL x) (threeBlockCC x)
    (threeBlockAC x - z • 1) (threeBlockBC x) (threeBlockCR x)
    (threeBlockAR x - z • 1) CL BR Theta).symm

end BoundaryLiteralDeterminant


end BernoulliLinearAlgebra
